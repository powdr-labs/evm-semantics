module

public import Lean.Data.Json
public import EvmSemantics
public import EvmSemantics.Data.Hex

/-!
`BlockchainTestRunner` — JSON driver for the `ethereum/tests` /
execution-spec-tests **BlockchainTests** (`blockchain_test`) suite.

A blockchain test is a genesis pre-state (`pre`) plus a chain of `blocks`,
each carrying a decoded `blockHeader`, a `transactions` list, optional
`withdrawals` (EIP-4895), and the block's full `rlp`. The runner executes
every transaction of every block in order — threading each tx's post-state
into the next, and each block's post-state into the next block — then
applies the block's withdrawals and the (pre-Merge) block reward, and
finally compares the resulting world against the test's expanded
`postState` (and the last block's `stateRoot`).

This is **Stage 1**: it executes *valid* chains and compares the post-state
in the same three tiers as the state-test runners
(`passCore` ⊂ `passFull` ⊂ `passRoot`). Two things are deferred to a later
stage and reported `INCON` so they land in the baseline rather than
counting as failures:

* **Invalid-block tests** — a block carrying `expectException` must be
  *rejected* by header/consensus validation, which this stage does not yet
  perform.
* **Unmodelled transaction types** — EIP-2930 access lists, EIP-4844 blobs
  and EIP-7702 set-code txs (as in the `gstatetests` runner); legacy and
  EIP-1559 transactions execute.
-/

@[expose] public section

namespace BlockchainTests

open EvmSemantics EvmSemantics.EVM Lean

open EvmSemantics.Hex

----------------------------------------------------------------------------
-- JSON helpers (mirrors the state-test runners).
----------------------------------------------------------------------------

def strField (j : Json) (k : String) : String := (j.getObjValAs? String k).toOption.getD ""

def subObj (j : Json) (k : String) : Json := (j.getObjVal? k).toOption.getD Json.null

def objEntries (j : Json) (k : String) : List (String × Json) :=
  match subObj j k with
  | .obj m => m.toArray.toList
  | _      => []

def jsonArr (j : Json) : Array Json :=
  match j with | .arr a => a | _ => #[]

def hasField (j : Json) (k : String) : Bool := (j.getObjVal? k).toOption.isSome

def storageEntries (j : Json) : List (String × String) :=
  match (j.getObjVal? "storage").toOption.getD Json.null with
  | .obj m => m.toArray.toList.filterMap (fun (k, v) =>
      match v with
      | .str s => some (k, s)
      | _      => none)
  | _      => []

def mkAccount (j : Json) : Account :=
  let balance := hexToUInt256 (strField j "balance")
  let code    := hexToBytes   (strField j "code")
  let nonce   := hexToUInt256 (strField j "nonce")
  let storage : Storage :=
    (storageEntries j).foldl
      (fun σ (k, v) => σ.set (hexToUInt256 k) (hexToUInt256 v))
      Storage.empty
  { balance := balance, nonce := nonce, code := code, storage := storage,
    tstorage := Storage.empty }

/-- Map the `network` field (e.g. `"Cancun"`) to a `Fork`. -/
def parseForkExact (s : String) : Option Fork :=
  match s with
  | "Frontier"          => some .Frontier
  | "Homestead"         => some .Homestead
  | "EIP150"            => some .TangerineWhistle
  | "EIP158"            => some .SpuriousDragon
  | "Byzantium"         => some .Byzantium
  | "Constantinople"    => some .Constantinople
  | "ConstantinopleFix" => some .Petersburg
  | "Petersburg"        => some .Petersburg
  | "Istanbul"          => some .Istanbul
  | "MuirGlacier"       => some .MuirGlacier
  | "Berlin"            => some .Berlin
  | "London"            => some .London
  | "ArrowGlacier"      => some .ArrowGlacier
  | "GrayGlacier"       => some .GrayGlacier
  | "Merge" | "Paris"   => some .Paris
  | "Shanghai"          => some .Shanghai
  | "Cancun"            => some .Cancun
  | "Prague"            => some .Prague
  | "Osaka"             => some .Osaka
  | _                   => none

----------------------------------------------------------------------------
-- Block header decode (the EVM-env subset) + EIP-4844 blob base fee.
----------------------------------------------------------------------------

/-- EIP-4844 fake-exponential (see `GeneralStateTestRunner`). -/
partial def fakeExponential (factor numerator denominator : Nat) : Nat :=
  let rec go (i accum numAcc : Nat) (fuel : Nat) : Nat :=
    if fuel = 0 then accum
    else
      let term := numAcc / (denominator * i)
      if term = 0 then accum
      else go (i + 1) (accum + term) (numAcc * numerator) (fuel - 1)
  go 1 factor (factor * numerator) 64

def blobBaseFeeOf (excessBlobGas : Nat) : Nat := fakeExponential 1 excessBlobGas 3338477

/-- Decode a `blockHeader` object into the EVM-env `BlockHeader`. Post-Merge
    `prevRandao` reads `mixHash`, falling back to `difficulty` pre-Merge.
    `blobBaseFee` derives from `excessBlobGas` (EIP-4844). `blockHash` is
    stubbed to `0` (BLOCKHASH support is a later stage). -/
def decodeBlockHeader (bh : Json) : BlockHeader :=
  let mixHash := strField bh "mixHash"
  let prevRandao : UInt256 :=
    if mixHash ≠ "" ∧ mixHash ≠ "0x0000000000000000000000000000000000000000000000000000000000000000"
    then hexToUInt256 mixHash
    else hexToUInt256 (strField bh "difficulty")
  let excessStr := strField bh "excessBlobGas"
  let blobBaseFee : UInt256 :=
    if excessStr ≠ "" then UInt256.ofNat (blobBaseFeeOf (hexToUInt256 excessStr).toNat) else ⟨0⟩
  { coinbase      := hexToAddress (strField bh "coinbase")
    timestamp     := hexToUInt256 (strField bh "timestamp")
    number        := hexToUInt256 (strField bh "number")
    prevRandao    := prevRandao
    gasLimit      := hexToUInt256 (strField bh "gasLimit")
    baseFeePerGas := hexToUInt256 (strField bh "baseFeePerGas")
    chainId       := ⟨1⟩
    blobBaseFee   := blobBaseFee
    blockHash     := fun _ => ⟨0⟩ }

----------------------------------------------------------------------------
-- Transaction build (block-tx JSON: scalar fields, `sender` given).
----------------------------------------------------------------------------

/-- Reason a block transaction can't be executed by this runner, or `none`.
    Legacy and EIP-1559 (empty access list) execute; access-list / blob /
    set-code txs are unmodelled (mirrors `GeneralStateTestRunner`). -/
def txUnsupportedReason (tx : Json) : Option String :=
  if (jsonArr (subObj tx "blobVersionedHashes")).size > 0 then
    some "blob tx (EIP-4844) unsupported"
  else if hasField tx "authorizationList" then
    some "set-code tx (EIP-7702) unsupported"
  else if (jsonArr (subObj tx "accessList")).size > 0 then
    some "access-list tx (EIP-2930) unsupported"
  else none

/-- Effective gas price: `min(maxFeePerGas, baseFee + maxPriorityFeePerGas)`
    for EIP-1559, else the legacy `gasPrice`. -/
def effectiveGasPrice (tx : Json) (baseFee : Nat) : UInt256 :=
  if hasField tx "maxFeePerGas" then
    let maxFee  := hexToNat (strField tx "maxFeePerGas")
    let maxPrio := hexToNat (strField tx "maxPriorityFeePerGas")
    UInt256.ofNat (Nat.min maxFee (baseFee + maxPrio))
  else hexToUInt256 (strField tx "gasPrice")

/-- Build a `Tx.Transaction` from a block-tx JSON object. `sender` is given
    directly by the fixture (no ECDSA recovery needed). -/
def buildTx (tx : Json) (baseFee : Nat) : Tx.Transaction :=
  let toStr := strField tx "to"
  { sender    := hexToAddress (strField tx "sender")
    recipient := if toStr = "" then none else some (hexToAddress toStr)
    value     := hexToUInt256 (strField tx "value")
    data      := hexToBytes   (strField tx "data")
    gasLimit  := hexToNat     (strField tx "gasLimit")
    gasPrice  := effectiveGasPrice tx baseFee
    nonce     := hexToUInt256 (strField tx "nonce") }

----------------------------------------------------------------------------
-- Block-level system calls (EIP-4788 beacon roots).
----------------------------------------------------------------------------

/-- EIP-4788 beacon-roots contract. -/
def beaconRootsAddress : AccountAddress :=
  AccountAddress.ofNat 0x000F3df6D732807Ef1319fB7B8bB8522d0Beac02

/-- EIP-2935 block-hash history contract (Prague+). -/
def historyStorageAddress : AccountAddress :=
  AccountAddress.ofNat 0x0000F90827F1C53a10cb7A02335B175320002935

/-- EIP-7002 withdrawal-requests contract (Prague+). -/
def withdrawalRequestAddress : AccountAddress :=
  AccountAddress.ofNat 0x00000961Ef480Eb55e80D19ad83579A64c007002

/-- EIP-7251 consolidation-requests contract (Prague+). -/
def consolidationRequestAddress : AccountAddress :=
  AccountAddress.ofNat 0x0000BBdDc7CE488642fb579F8B00f3a590007251

/-- EIP-4788 / EIP-2935 system caller. -/
def systemAddress : AccountAddress :=
  AccountAddress.ofNat 0xfffffffffffffffffffffffffffffffffffffffe

/-- Execute a block-level *system call*: run `target`'s code with `calldata`
    from `systemAddress`, committing its state writes, but with none of the
    transaction-level accounting (no nonce bump, no gas charge, no EIP-1559
    fee floor, no coinbase credit). Used for EIP-4788. A no-op if the target
    has no code; a reverting/failing system call leaves state unchanged. -/
def systemCall (m : AccountMap) (header : BlockHeader) (fork : Fork)
    (target : AccountAddress) (calldata : ByteArray) : AccountMap :=
  let code := (m target).code
  if code.size == 0 then m
  else
    let gas := 30000000
    let execEnv : ExecutionEnv :=
      { address := target, origin := systemAddress, caller := systemAddress,
        weiValue := ⟨0⟩, calldata := calldata, code := code, codeAddr := target,
        gasPrice := ⟨0⟩, header := header, depth := 0, permitStateMutation := true,
        blobVersionedHashes := #[], fork := fork }
    let s0 : State :=
      { toMachineState :=
          { gasAvailable := gas, activeWords := ⟨0⟩, memory := .empty,
            returnData := .empty, hReturn := .empty }
        accountMap   := m
        substate     :=
          { Substate.empty with
              originalAccountMap := m
              accessedAccounts   := [systemAddress, target] }
        executionEnv := execEnv
        pc := ⟨0⟩, stack := [], execLength := 0, halt := .Running }
    match Tx.run s0 (2 * gas + 100000) with
    | .ok sf =>
      match sf.halt with
      | .Exception _ => m   -- failed system call: no state change
      | _            => sf.accountMap
    | .error _ => m

/-- EIP-4788 (Cancun+): at the start of a block, invoke the beacon-roots
    contract with `parentBeaconBlockRoot` as calldata so it records the
    `timestamp → root` mapping in its ring buffer. -/
def applyBeaconRoot (m : AccountMap) (block : Json) (header : BlockHeader)
    (fork : Fork) : AccountMap :=
  if fork ≥ .Cancun then
    let rootStr := strField (subObj block "blockHeader") "parentBeaconBlockRoot"
    if rootStr = "" then m
    else systemCall m header fork beaconRootsAddress (hexToBytes rootStr)
  else m

/-- EIP-2935 (Prague+): at the start of a block, invoke the block-hash
    history contract with the `parentHash` as calldata so it records the
    parent block's hash in its ring buffer. -/
def applyBlockHashHistory (m : AccountMap) (block : Json) (header : BlockHeader)
    (fork : Fork) : AccountMap :=
  if fork ≥ .Prague then
    let parentStr := strField (subObj block "blockHeader") "parentHash"
    if parentStr = "" then m
    else systemCall m header fork historyStorageAddress (hexToBytes parentStr)
  else m

/-- EIP-7002 / EIP-7251 (Prague+): at the *end* of a block, invoke the
    withdrawal-requests then consolidation-requests contracts (empty
    calldata) so they dequeue their queued requests, updating contract
    storage. -/
def applyBlockEndRequests (m : AccountMap) (header : BlockHeader)
    (fork : Fork) : AccountMap :=
  if fork ≥ .Prague then
    let m := systemCall m header fork withdrawalRequestAddress ByteArray.empty
    systemCall m header fork consolidationRequestAddress ByteArray.empty
  else m

----------------------------------------------------------------------------
-- Block execution: thread txs, then withdrawals + block reward.
----------------------------------------------------------------------------

/-- Apply a block's EIP-4895 withdrawals: credit each `address` with
    `amount` Gwei (`amount · 10⁹` wei). -/
def applyWithdrawals (m : AccountMap) (block : Json) : AccountMap := Id.run do
  let mut m := m
  for w in jsonArr (subObj block "withdrawals") do
    let addr := hexToAddress (strField w "address")
    let wei  := hexToNat (strField w "amount") * 1000000000
    if wei ≠ 0 then
      let acc := m addr
      m := m.set addr { acc with balance := acc.balance + UInt256.ofNat wei }
  return m

/-- Execute one block against `preMap`: run every transaction in order
    (threading the post-state), then apply withdrawals and — once for the
    whole block — the pre-Merge block reward. Returns `.error reason` for an
    unmodelled tx type or a fuel-exhausted run (⇒ `INCON`). -/
def executeBlock (preMap : AccountMap) (block : Json) (fork : Fork) :
    Except String AccountMap := do
  let header := decodeBlockHeader (subObj block "blockHeader")
  let baseFee := header.baseFeePerGas.toNat
  -- Block-start system calls: EIP-4788 beacon roots (Cancun+) and EIP-2935
  -- block-hash history (Prague+).
  let mut m := applyBlockHashHistory (applyBeaconRoot preMap block header fork) block header fork
  for tx in jsonArr (subObj block "transactions") do
    match txUnsupportedReason tx with
    | some r => throw r
    | none =>
      let t := buildTx tx baseFee
      let fuel := 2 * t.gasLimit + 100_000
      -- `applyReward := false`: the fixed block subsidy is paid once per
      -- block below, not per transaction.
      let result := EvmSemantics.Tx.execute m header t fork fuel #[] (applyReward := false)
      match result.outcome with
      | .fuelExhausted => throw "fuel exhausted"
      | _ => m := result.finalAccounts
  -- End-of-block: EIP-7002/7251 request system calls, withdrawals, then the
  -- (pre-Merge) block reward on the block's own coinbase.
  m := applyBlockEndRequests m header fork
  m := applyWithdrawals m block
  pure (Tx.applyBlockReward m header.coinbase fork)

----------------------------------------------------------------------------
-- Post-state comparison (mirrors GeneralStateTestRunner).
----------------------------------------------------------------------------

/-- Outcome tiers, strongest-first: `passRoot ⊃ passFull ⊃ passCore`. -/
inductive Outcome where
  | passCore
  | passFull
  | passRoot
  | fail  (msg : String)
  | incon (msg : String)
  deriving Repr

/-- Compare final accounts to a `postState` object; storage/nonce/code always,
    balance only when `checkBal`. -/
def cmpPost (finalAccounts : AccountMap)
    (preEntries postEntries : List (String × Json)) (checkBal : Bool) :
    List String := Id.run do
  let mut msgs := []
  for (addrStr, accJson) in postEntries do
    let a := hexToAddress addrStr
    let got := finalAccounts a
    let expNonce := hexToUInt256 (strField accJson "nonce")
    let expCode := hexToBytes (strField accJson "code")
    if got.nonce.toNat != expNonce.toNat then
      msgs := s!"{addrStr} nonce {got.nonce.toNat}≠{expNonce.toNat}" :: msgs
    if got.code.toList != expCode.toList then
      msgs := s!"{addrStr} code size {got.code.size}≠{expCode.size}" :: msgs
    let postSlots := storageEntries accJson
    let preSlots :=
      match preEntries.find? (fun (k, _) => k == addrStr) with
      | some (_, preJson) => storageEntries preJson
      | none              => []
    let mut seen : List String := []
    for (slot, val) in postSlots do
      seen := slot :: seen
      let k := hexToUInt256 slot
      let want := hexToUInt256 val
      if (got.storage k).toNat != want.toNat then
        msgs := s!"{addrStr}[{slot}] {(got.storage k).toNat}≠{want.toNat}" :: msgs
    for (slot, _) in preSlots do
      if seen.contains slot then continue
      let k := hexToUInt256 slot
      if (got.storage k).toNat != 0 then
        msgs := s!"{addrStr}[{slot}] {(got.storage k).toNat}≠0 (cleared)" :: msgs
    if checkBal then
      let expBal := hexToUInt256 (strField accJson "balance")
      if got.balance.toNat != expBal.toNat then
        msgs := s!"{addrStr} bal {got.balance.toNat}≠{expBal.toNat}" :: msgs
  return msgs

----------------------------------------------------------------------------
-- Per-test runner.
----------------------------------------------------------------------------

/-- Run one blockchain test: build the genesis pre-state, execute the chain,
    and compare the final world against `postState` (tiered) and the last
    block's `stateRoot` (root tier). -/
def runTest (testObj : Json) : Outcome :=
  match parseForkExact (strField testObj "network") with
  | none => .incon s!"unmodelled fork {strField testObj "network"}"
  | some fork =>
    let blocks := (jsonArr (subObj testObj "blocks")).toList
    -- Stage 1 executes valid chains only; a block asserting `expectException`
    -- needs consensus validation to reject it (a later stage).
    if blocks.any (fun b => hasField b "expectException") then
      .incon "invalid-block test (needs consensus validation)"
    else
      let preEntries := objEntries testObj "pre"
      let preMap : AccountMap :=
        preEntries.foldl
          (fun σ (addrStr, accJson) => σ.set (hexToAddress addrStr) (mkAccount accJson))
          AccountMap.empty
      -- Fold the chain, threading the world state block to block.
      let rec go (m : AccountMap) : List Json → Except String AccountMap
        | []      => .ok m
        | b :: bs => match executeBlock m b fork with
                     | .error r => .error r
                     | .ok m'   => go m' bs
      match go preMap blocks with
      | .error r => .incon r
      | .ok finalAccounts =>
        let post := objEntries testObj "postState"
        if post.isEmpty then .incon "no postState (postStateHash-only, unsupported)"
        else match cmpPost finalAccounts preEntries post false with
        | [] =>
          match cmpPost finalAccounts preEntries post true with
          | [] =>
            -- Root tier: compare our world MPT root to the last block's
            -- `stateRoot`.
            let lastRootStr :=
              match blocks.getLast? with
              | some b => strField (subObj b "blockHeader") "stateRoot"
              | none   => ""
            let expRoot := hexToUInt256 lastRootStr
            let isPrecompileAddr (a : AccountAddress) : Bool :=
              decide (1 ≤ a.val) && decide (a.val ≤ 9)
            let wasInPreState : AccountAddress → Bool :=
              fun a => preMap.contains a && ¬ isPrecompileAddr a
            match AccountMap.stateRoot finalAccounts fork wasInPreState with
            | some ourRoot =>
              if lastRootStr ≠ "" ∧ ourRoot.toNat == expRoot.toNat then .passRoot
              else .passFull
            | none => .passFull
          | _ => .passCore
        | msgs => .fail (String.intercalate "; " (msgs.take 3))

----------------------------------------------------------------------------
-- Tally + file/dir driver (mirrors GeneralStateTestRunner).
----------------------------------------------------------------------------

structure Tally where
  passRoot : Nat := 0
  passFull : Nat := 0
  passCore : Nat := 0
  fail : Nat := 0
  incon : Nat := 0
  crash : Nat := 0
  deriving Inhabited

def Tally.total (t : Tally) : Nat :=
  t.passRoot + t.passFull + t.passCore + t.fail + t.incon + t.crash

partial def collectJson (dir : System.FilePath) : IO (Array System.FilePath) := do
  let mut out : Array System.FilePath := #[]
  for ent in (← dir.readDir) do
    let path := ent.path
    if (← path.isDir) then out := out ++ (← collectJson path)
    else if path.toString.endsWith ".json" then out := out.push path
  return out.qsort (fun a b => a.toString < b.toString)

/-- Sanitize a test name into an id-safe token (no spaces/colons). -/
def sanitize (s : String) : String := (s.replace " " "_").replace ":" "_"

/-- Run every test in one file; one `(tag, id, msg)` per test key. -/
def runFileResults (path : System.FilePath) : IO (Array (String × String × String)) := do
  let txt ← IO.FS.readFile path
  match Json.parse txt with
  | .error e => return #[("CRASH", path.fileName.getD path.toString, s!"parse: {e}")]
  | .ok j =>
    let tests := match j with | .obj m => m.toArray.toList | _ => []
    let fileTag := ((path.fileName.getD "").replace ".json" "")
    let mut out := #[]
    for (testName, testObj) in tests do
      let id := s!"{fileTag}_{sanitize testName}"
      let r : String × String × String :=
        match runTest testObj with
        | .passRoot => ("PASS_ROOT", id, "")
        | .passFull => ("PASS_FULL", id, "")
        | .passCore => ("PASS_CORE", id, "")
        | .fail m   => ("FAIL", id, m)
        | .incon m  => ("INCON", id, m)
      out := out.push r
    return out

/-- Run `files` keeping up to `jobs` `Task`s in flight, with an optional
    per-task wall-clock cap. -/
def runFiles (files : Array System.FilePath) (jobs : Nat) (verbose : Bool)
    (timeoutMs : Nat := 0) : IO Tally := do
  let mut t : Tally := {}
  let n := files.size
  if n = 0 then return t
  let workers := Nat.max 1 jobs
  let mut slots :
      Array (Option (Nat × Nat × Task (Except IO.Error (Array (String × String × String))))) :=
    Array.replicate workers none
  let mut nextIdx : Nat := 0
  let mut remaining : Nat := n
  let fold : Tally → Bool →
      Except IO.Error (Array (String × String × String)) → IO Tally :=
    fun t verb r => do
      let mut t := t
      match r with
      | .ok results =>
        for (tag, name, msg) in results do
          match tag with
          | "PASS_ROOT" => t := { t with passRoot := t.passRoot + 1 }
          | "PASS_FULL" => t := { t with passFull := t.passFull + 1 }
          | "PASS_CORE" => t := { t with passCore := t.passCore + 1 }
          | "FAIL"      => t := { t with fail := t.fail + 1 }
                           if verb then IO.println s!"FAIL {name}: {msg}"
          | "INCON"     => t := { t with incon := t.incon + 1 }
                           if verb then IO.println s!"INCON {name}: {msg}"
          | _           => t := { t with crash := t.crash + 1 }
                           if verb then IO.println s!"CRASH {name}: {msg}"
      | .error e =>
        t := { t with crash := t.crash + 1 }
        if verb then IO.println s!"CRASH (task): {e}"
      return t
  for i in [0:workers] do
    if nextIdx < n then
      let now ← IO.monoMsNow
      let task ← IO.asTask (runFileResults files[nextIdx]!) Task.Priority.dedicated
      slots := slots.set! i (some (nextIdx, now, task))
      nextIdx := nextIdx + 1
  while remaining > 0 do
    let mut progress := false
    for i in [0:workers] do
      match slots[i]! with
      | none => pure ()
      | some (idx, startMs, task) =>
        let done ← IO.hasFinished task
        let elapsed := (← IO.monoMsNow) - startMs
        if done then
          t ← fold t verbose (← IO.wait task)
          remaining := remaining - 1
          progress := true
          if nextIdx < n then
            let now ← IO.monoMsNow
            let next ← IO.asTask (runFileResults files[nextIdx]!) Task.Priority.dedicated
            slots := slots.set! i (some (nextIdx, now, next))
            nextIdx := nextIdx + 1
          else slots := slots.set! i none
        else if timeoutMs > 0 ∧ elapsed > timeoutMs then
          t := { t with incon := t.incon + 1 }
          if verbose then
            IO.println s!"INCON {files[idx]!.fileName.getD files[idx]!.toString}: \
              wall-timeout (>{timeoutMs}ms, abandoned)"
          remaining := remaining - 1
          progress := true
          if nextIdx < n then
            let now ← IO.monoMsNow
            let next ← IO.asTask (runFileResults files[nextIdx]!) Task.Priority.dedicated
            slots := slots.set! i (some (nextIdx, now, next))
            nextIdx := nextIdx + 1
          else slots := slots.set! i none
    if !progress then IO.sleep 10
  return t

/-- Parse `-j N` and `--timeout MS`; returns `(jobs, timeoutMs, rest)`. -/
def parseFlags (args : List String) : Nat × Nat × List String := Id.run do
  let rec go : List String → Option Nat → Option Nat → List String → Nat × Nat × List String
    | [], j, tm, acc => (j.getD 0, tm.getD 0, acc.reverse)
    | "-j" :: v :: rest, _, tm, acc => go rest (some v.toNat!) tm acc
    | "--timeout" :: v :: rest, j, _, acc => go rest j (some v.toNat!) acc
    | x :: rest, j, tm, acc => go rest j tm (x :: acc)
  go args none none []

/-- Entry point: `blockchaintests [-v] [-j N] [--timeout MS] <dir-or-file>`. -/
def main (args : List String) : IO Unit := do
  let verbose := args.contains "-v"
  let (jobs0, timeoutMs, rest) := parseFlags (args.filter (· != "-v"))
  let jobs ← if jobs0 > 0 then pure jobs0 else do
    match (← IO.getEnv "BLOCKCHAINTESTS_JOBS") with
    | some s => pure (Nat.max 1 s.toNat!)
    | none   => pure 8
  let root : System.FilePath := rest.headD "."
  let files ← if (← root.isDir) then collectJson root else pure #[root]
  let t ← runFiles files jobs verbose timeoutMs
  IO.println s!"pass(root={t.passRoot} full+={t.passFull} core+={t.passCore}) \
fail={t.fail} incon={t.incon} crash={t.crash} (total {t.total})"

end BlockchainTests

def main (args : List String) : IO Unit := BlockchainTests.main args
