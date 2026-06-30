module

public import Lean.Data.Json
public import EvmSemantics
public import EvmSemantics.Data.Hex

/-!
`StateTestRunner` — JSON driver around `EvmSemantics.Tx.execute`.

The runner's *only* job is plumbing: read a BlockchainTest JSON file,
build a `Tx.Transaction` and a `BlockHeader`, hand them to
`EvmSemantics.Tx.execute`, and compare the resulting `AccountMap`
against the test's `postState`. The transaction semantics — value
transfer, sender-nonce bump, address-collision check, top-level OOG
rollback, deployed-code install on create success — all live in
`EvmSemantics.Tx`, where they belong.
-/

@[expose] public section

namespace StateTests

open EvmSemantics EvmSemantics.EVM Lean

open EvmSemantics.Hex

----------------------------------------------------------------------------
-- JSON helpers.
----------------------------------------------------------------------------

def strField (j : Json) (k : String) : String := (j.getObjValAs? String k).toOption.getD ""

def subObj (j : Json) (k : String) : Json := (j.getObjVal? k).toOption.getD Json.null

def objEntries (j : Json) (k : String) : List (String × Json) :=
  match subObj j k with
  | .obj m => m.toArray.toList
  | _      => []

def storageEntries (j : Json) : List (String × String) :=
  match (j.getObjVal? "storage").toOption.getD Json.null with
  | .obj m => m.toArray.toList.filterMap (fun (k, v) =>
      match v with
      | .str s => some (k, s)
      | _      => none)
  | _      => []

/-- All blockchain tests in the legacy ethereum/tests corpus use this
    deterministic sender. -/
def txSender : AccountAddress :=
  hexToAddress "0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b"

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

----------------------------------------------------------------------------
-- Transaction / header decode.
----------------------------------------------------------------------------

/-- Decode a BlockchainTest transaction JSON into a
    `EvmSemantics.Tx.Transaction`. `to = ""` (or missing) marks a
    contract-creating tx, signalled here as `recipient = none`. -/
def decodeTx (tx : Json) : EvmSemantics.Tx.Transaction :=
  let toStr := strField tx "to"
  { sender    := txSender
    recipient := if toStr = "" then none else some (hexToAddress toStr)
    value     := hexToUInt256 (strField tx "value")
    data      := hexToBytes   (strField tx "data")
    gasLimit  := hexToNat     (strField tx "gasLimit")
    gasPrice  := hexToUInt256 (strField tx "gasPrice") }

/-- EIP-4844 fake-exponential `fake_exp(factor, numerator, denominator)`
    approximates `factor · e^(numerator / denominator)` using the
    convergent series `Σ (numerator^i · factor) / (denominator^i · i!)`,
    stopping as soon as a term contributes 0 (Nat arithmetic). The blob
    base fee is `fake_exp(MIN_BLOB_BASE_FEE = 1, excessBlobGas,
    BLOB_BASE_FEE_UPDATE_FRACTION = 3338477)` per EIP-4844 §5. -/
partial def fakeExponential (factor numerator denominator : Nat) : Nat :=
  let rec go (i accum numAcc : Nat) (fuel : Nat) : Nat :=
    if fuel = 0 then accum
    else
      let term := numAcc / (denominator * i)
      if term = 0 then accum
      else go (i + 1) (accum + term) (numAcc * numerator) (fuel - 1)
  go 1 factor (factor * numerator) 64

/-- EIP-4844 blob base fee derived from `excessBlobGas`. -/
def blobBaseFeeOf (excessBlobGas : Nat) : Nat :=
  fakeExponential 1 excessBlobGas 3338477

/-- Decode the EVM-relevant subset of the BlockchainTests block header.
    The corpus stores these in `blocks[i].blockHeader` with the same
    field names the YP uses (`coinbase`, `timestamp`, `number`,
    `difficulty`, `gasLimit`, plus modern additions `baseFeePerGas`,
    `excessBlobGas`); missing fields fall back to zero.

    * `prevRandao` ← `difficulty` (the YP renamed the field at the
      Merge; pre-Merge `DIFFICULTY` reads `difficulty`, post-Merge
      `PREVRANDAO` reads `mixHash` — the corpus is pre-Merge so
      `difficulty` is what's populated).
    * `chainId` is *not* in the block header per se; mainnet = 1.
    * `blobBaseFee` — preferred path: derive from `excessBlobGas` via
      EIP-4844 `fake_exp(1, excessBlobGas, 3338477)`. If the corpus
      provides an explicit `blobBaseFee` field that takes precedence
      (some tooling emits it directly); otherwise we use the derivation
      from `excessBlobGas`; otherwise 0. -/
def decodeHeader (blockHeader : Json) : BlockHeader :=
  let blobBaseFeeField   := strField blockHeader "blobBaseFee"
  let excessBlobGasField := strField blockHeader "excessBlobGas"
  let blobBaseFee : UInt256 :=
    if blobBaseFeeField ≠ "" then hexToUInt256 blobBaseFeeField
    else if excessBlobGasField ≠ "" then
      UInt256.ofNat (blobBaseFeeOf (hexToUInt256 excessBlobGasField).toNat)
    else ⟨0⟩
  { coinbase      := hexToAddress (strField blockHeader "coinbase")
    timestamp     := hexToUInt256 (strField blockHeader "timestamp")
    number        := hexToUInt256 (strField blockHeader "number")
    prevRandao    := hexToUInt256 (strField blockHeader "difficulty")
    gasLimit      := hexToUInt256 (strField blockHeader "gasLimit")
    baseFeePerGas := hexToUInt256 (strField blockHeader "baseFeePerGas")
    chainId       := ⟨1⟩
    blobBaseFee   := blobBaseFee
    blockHash     := fun _ => ⟨0⟩ }

/-- Read the EIP-4844 `blobVersionedHashes` list out of a tx JSON
    (Cancun-era blob-typed transactions). Pre-Cancun tests have no such
    field and we return `#[]`. -/
def decodeBlobHashes (tx : Json) : Array UInt256 :=
  match (tx.getObjVal? "blobVersionedHashes").toOption.getD Json.null with
  | .arr a => a.map (fun j => hexToUInt256 ((j.getStr?).toOption.getD ""))
  | _      => #[]

/-- Map a BlockchainTest variant suffix (the bit after the last `_` in the
    test object's key, e.g. `_Constantinople`, `_Berlin`) to a `Fork`. -/
def parseFork (s : String) : Option Fork :=
  if s.endsWith "_Frontier" then some .Frontier
  else if s.endsWith "_Homestead" then some .Homestead
  else if s.endsWith "_EIP150" then some .TangerineWhistle
  else if s.endsWith "_EIP158" then some .SpuriousDragon
  else if s.endsWith "_Byzantium" then some .Byzantium
  else if s.endsWith "_Constantinople" then some .Constantinople
  else if s.endsWith "_ConstantinopleFix" then some .Petersburg
  else if s.endsWith "_Petersburg" then some .Petersburg
  else if s.endsWith "_Istanbul" then some .Istanbul
  else if s.endsWith "_MuirGlacier" then some .MuirGlacier
  else if s.endsWith "_Berlin" then some .Berlin
  else if s.endsWith "_London" then some .London
  else if s.endsWith "_ArrowGlacier" then some .ArrowGlacier
  else if s.endsWith "_GrayGlacier" then some .GrayGlacier
  else if s.endsWith "_Merge" then some .Paris
  else if s.endsWith "_Paris" then some .Paris
  else if s.endsWith "_Shanghai" then some .Shanghai
  else if s.endsWith "_Cancun" then some .Cancun
  else if s.endsWith "_Prague" then some .Prague
  else if s.endsWith "_Osaka" then some .Osaka
  else none

----------------------------------------------------------------------------
-- Post-state comparison.
----------------------------------------------------------------------------

inductive Outcome where
  /-- Storage + nonce + code match, but balances don't. -/
  | passCore
  /-- `passCore` plus exact balances on every account in `postState`,
      but the MPT `stateRoot` we compute doesn't equal the corpus's
      (some account our run touched isn't in `postState`, or
      vice-versa — usually a stale self-destructed account, an empty
      account that EIP-161 should have pruned, or an extra coinbase
      entry). -/
  | passFull
  /-- `passFull` plus the world MPT root matches the corpus's
      `blockHeader.stateRoot` — the strongest tier, equivalent to
      "every observable byte of the post-state is bit-identical to
      what Geth would produce." -/
  | passRoot
  | fail (msg : String)
  | incon (msg : String)
  deriving Repr

/-- Compare the run's final accounts to `postState`. Returns a list of
    mismatch descriptions; checks storage/nonce/code always, balance only
    when `checkBal` is set.

    Storage is checked over the **union** of pre-state and post-state slot
    keys for each address: post-state JSON omits zero-valued entries, so a
    slot that held a non-zero value in pre-state and was cleared (or
    rolled back) to zero would be invisible if we iterated post-state
    alone. Slots in pre that are absent from post are expected to be 0. -/
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

/-- Run one test object (a single fork variant). Builds the pre-state map
    from the test's `pre` block, decodes the first transaction, hands
    everything off to `EvmSemantics.Tx.execute`, then compares the
    resulting `AccountMap` to the test's `postState`. -/
def runOne (testObj : Json) (fork : Fork) : Outcome :=
  let preMap : AccountMap :=
    (objEntries testObj "pre").foldl
      (fun σ (addrStr, accJson) => σ.set (hexToAddress addrStr) (mkAccount accJson))
      AccountMap.empty
  let blocks := match subObj testObj "blocks" with | .arr a => a.toList | _ => []
  match blocks with
  | block :: _ =>
    let txs := match subObj block "transactions" with | .arr a => a.toList | _ => []
    match txs with
    | tx :: _ =>
      let txObj  := decodeTx tx
      let header := decodeHeader (subObj block "blockHeader")
      let blobHashes := decodeBlobHashes tx
      -- Fuel: every non-halting opcode costs ≥1 gas and every CALL
      -- resume step is bounded by the # of CALLs (≥700 gas each), so
      -- `2·gasLimit + 100_000` cannot pre-empt a genuine OOG; it is
      -- purely a backstop against an evaluator bug producing a 0-gas
      -- non-halting step.
      let fuel := 2 * txObj.gasLimit + 100_000
      let result := EvmSemantics.Tx.execute preMap header txObj fork fuel blobHashes
      match result.outcome with
      | .fuelExhausted => .incon "fuel exhausted"
      | _ =>
        let pre  := objEntries testObj "pre"
        let post := objEntries testObj "postState"
        match cmpPost result.finalAccounts pre post false with
        | [] => match cmpPost result.finalAccounts pre post true with
                | [] =>
                  -- All fields the test enumerates match. Try the
                  -- strongest tier: world-state MPT root match.
                  let expHex := strField (subObj block "blockHeader") "stateRoot"
                  let expRoot := hexToUInt256 expHex
                  match AccountMap.stateRoot result.finalAccounts fork with
                  | some ourRoot =>
                    if ourRoot.toNat == expRoot.toNat then .passRoot
                    else .passFull
                  | none => .passFull
                | _  => .passCore
        | msgs => .fail (String.intercalate "; " (msgs.take 3))
    | [] => .incon "no transactions"
  | [] => .incon "no blocks"

----------------------------------------------------------------------------
-- Tally + file/dir driver.
----------------------------------------------------------------------------

structure Tally where
  passRoot : Nat := 0
  passFull : Nat := 0
  passCore : Nat := 0
  fail : Nat := 0
  incon : Nat := 0
  crash : Nat := 0
  deriving Inhabited

def Tally.add (t u : Tally) : Tally :=
  { passRoot := t.passRoot + u.passRoot
    passFull := t.passFull + u.passFull
    passCore := t.passCore + u.passCore
    fail := t.fail + u.fail, incon := t.incon + u.incon, crash := t.crash + u.crash }

def Tally.total (t : Tally) : Nat :=
  t.passRoot + t.passFull + t.passCore + t.fail + t.incon + t.crash

/-- Walk `dir` recursively, returning every `*.json` underneath, sorted. -/
partial def collectJson (dir : System.FilePath) :
    IO (Array System.FilePath) := do
  let mut out : Array System.FilePath := #[]
  for ent in (← dir.readDir) do
    let path := ent.path
    if (← path.isDir) then out := out ++ (← collectJson path)
    else if path.toString.endsWith ".json" then out := out.push path
  return out.qsort (fun a b => a.toString < b.toString)

/-- Run every fork variant in one file; return one `(tag, name, msg)`
    triple per test (`tag ∈ {PASS_FULL, PASS_CORE, FAIL, INCON}`). Variants
    whose `network` suffix doesn't map to a `Fork` we model are skipped
    silently. -/
def runFileResults (path : System.FilePath) : IO (Array (String × String × String)) := do
  let txt ← IO.FS.readFile path
  match Json.parse txt with
  | .error e => return #[("CRASH", path.fileName.getD path.toString, s!"parse: {e}")]
  | .ok j =>
    let entries := match j with | .obj m => m.toArray.toList | _ => []
    let mut out := #[]
    for (name, testObj) in entries do
      match parseFork name with
      | none => continue
      | some fork =>
        let r := match runOne testObj fork with
          | .passRoot => ("PASS_ROOT", name, "")
          | .passFull => ("PASS_FULL", name, "")
          | .passCore => ("PASS_CORE", name, "")
          | .fail m   => ("FAIL", name, m)
          | .incon m  => ("INCON", name, m)
        out := out.push r
    return out

/-- Run `files` keeping up to `jobs` `Task`s **continuously in flight**: as
    each one finishes, the next file is dispatched immediately rather than
    waiting for the rest of the batch (the old `for task in tasks do IO.wait
    task` pattern starved cores whenever one file in the batch was slow).

    Per-task wall-clock cap: if `timeoutMs > 0`, a task whose elapsed time
    exceeds the cap is marked `INCON wall-timeout`, its slot freed, and the
    next file dispatched. The abandoned task continues running in the
    background (Lean's `Task`s aren't OS-cancellable). `timeoutMs = 0`
    disables the cap.

    Output is in completion order (which can differ from spawn order). The
    summary scripts key on FAIL ids, not line order. -/
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
  let foldResult : Tally → Bool →
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
  -- Prime the pool with up to `workers` initial tasks.
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
          t ← foldResult t verbose (← IO.wait task)
          remaining := remaining - 1
          progress := true
          if nextIdx < n then
            let now ← IO.monoMsNow
            let next ← IO.asTask (runFileResults files[nextIdx]!) Task.Priority.dedicated
            slots := slots.set! i (some (nextIdx, now, next))
            nextIdx := nextIdx + 1
          else
            slots := slots.set! i none
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
          else
            slots := slots.set! i none
    if !progress then IO.sleep 10
  return t

/-- Parse `-j N` and `--timeout MS` out of `args`. Returns the jobs
    value (or `0` for "unset"), the timeout-in-millis (`0` = disabled),
    and the remaining args. -/
def parseFlags (args : List String) : Nat × Nat × List String := Id.run do
  let rec go : List String → Option Nat → Option Nat → List String → Nat × Nat × List String
    | [], j, tm, acc => (j.getD 0, tm.getD 0, acc.reverse)
    | "-j" :: v :: rest, _, tm, acc => go rest (some v.toNat!) tm acc
    | "--timeout" :: v :: rest, j, _, acc => go rest j (some v.toNat!) acc
    | x :: rest, j, tm, acc => go rest j tm (x :: acc)
  go args none none []

def main (args : List String) : IO Unit := do
  let verbose := args.contains "-v"
  let (jobs0, timeoutMs, rest) := parseFlags (args.filter (· != "-v"))
  let jobs ← if jobs0 > 0 then pure jobs0 else do
    match (← IO.getEnv "STATETESTS_JOBS") with
    | some s => pure (Nat.max 1 s.toNat!)
    | none   => pure 8
  let root : System.FilePath := rest.headD "."
  let files ← if (← root.isDir) then collectJson root else pure #[root]
  let t ← runFiles files jobs verbose timeoutMs
  IO.println s!"pass(root={t.passRoot} full+={t.passFull} core+={t.passCore}) \
fail={t.fail} incon={t.incon} crash={t.crash} (total {t.total})"

end StateTests

def main (args : List String) : IO Unit := StateTests.main args
