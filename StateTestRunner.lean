import EvmSemantics
import EvmSemantics.Data.Hex
import Std.Internal.Parsec
import Lean.Data.Json

/-!
`statetests` — a conformance runner for the **BlockchainTests** form of the
ethereum/legacytests GeneralStateTests (`Constantinople/BlockchainTests/
GeneralStateTests/stCall*`). Unlike the plain GeneralStateTests (which give only
a post-state-root `hash`, needing keccak + RLP + a Merkle-Patricia trie), the
BlockchainTests carry an **expanded `postState`** (balance/code/nonce/storage
per account), so we can verify the recursive CALL semantics directly.

Scope (v1): we run only the `Constantinople` fork variant of each test (the only
fork whose schedule `EvmSemantics` models for the CALL family — EIP-150 gas).
The top-level transaction is executed as the `to` account's code; CALL opcodes
inside it recurse through the new frame-stack machinery. We compare the
resulting accounts against `postState`:

* **core** match = storage + nonce + code (the CALL-semantics signal);
* **full** match also requires the gas-dependent **balances** to agree.

`core` is the headline pass metric; `full` is reported separately because exact
balances require exact gas accounting (the hardest part to get right).
-/

open EvmSemantics EvmSemantics.EVM Lean

namespace StateTests

open EvmSemantics.Hex

----------------------------------------------------------------------------
-- JSON helpers
----------------------------------------------------------------------------

def strField (j : Json) (k : String) : String :=
  match j.getObjVal? k with
  | .ok v => (v.getStr?.toOption.getD (toString v))
  | .error _ => ""

def subObj (j : Json) (k : String) : Json := (j.getObjVal? k).toOption.getD Json.null

def objEntries (j : Json) (k : String) : List (String × Json) :=
  match (subObj j k) with
  | .obj m => m.toArray.toList.map (fun (kv) => (kv.1, kv.2))
  | _ => []

/-- Storage slot→value entries of an account JSON object. -/
def storageEntries (accJson : Json) : List (String × String) :=
  match subObj accJson "storage" with
  | .obj m => m.toArray.toList.filterMap (fun kv =>
      (kv.2.getStr?.toOption).map (fun v => (kv.1, v)))
  | _ => []

----------------------------------------------------------------------------
-- State construction.
----------------------------------------------------------------------------

/-- The fixed ethereum/tests transaction sender (we have no ECDSA recovery; the
    transactions carry only `v/r/s`). All stCall* `pre` states fund this EOA. -/
def txSender : AccountAddress := hexToAddress "0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b"

def mkAccount (accJson : Json) : Account :=
  let storage := (storageEntries accJson).foldl
    (fun st (slot, val) => st.set (hexToUInt256 slot) (hexToUInt256 val)) Storage.empty
  { nonce    := hexToUInt256 (strField accJson "nonce")
    balance  := hexToUInt256 (strField accJson "balance")
    code     := hexToBytes   (strField accJson "code")
    storage  := storage
    tstorage := Storage.empty }

/-- Intrinsic transaction gas: 21000 + 16 per non-zero calldata byte + 4 per
    zero byte (pre-EIP-2028 the non-zero rate was 68; Constantinople uses 68).
    The legacy corpus predates EIP-2028, so we use 68/4. -/
def intrinsicGas (data : ByteArray) : Nat := Id.run do
  let mut g := 21000
  for b in data do
    g := g + (if b == 0 then 4 else 68)
  return g

/-- Map a state-test `"network"` string (the variant suffix on each
    test's JSON key, also stored in the test object) to the matching
    `Fork`. Unknown strings fall back to `Petersburg`. -/
def forkOfNetwork (s : String) : Fork :=
  match s with
  | "Frontier"          => .Frontier
  | "Homestead"         => .Homestead
  | "EIP150"            => .EIP150
  | "EIP158"            => .EIP158
  | "Byzantium"         => .Byzantium
  | "Constantinople"    => .Constantinople
  | "ConstantinopleFix" => .Petersburg
  | _                   => .Petersburg

/-- Build the top-level execution `State` for a BlockchainTest test object,
    given its `pre` accounts and the block's transaction JSON. The `fork`
    argument is taken from the test's `"network"` field. -/
def buildState (preMap : AccountMap) (blockHeader tx : Json) (fork : Fork) : State :=
  let toAddr   := hexToAddress (strField tx "to")
  let value    := hexToUInt256 (strField tx "value")
  let data     := hexToBytes   (strField tx "data")
  let gasLimit := hexToNat     (strField tx "gasLimit")
  let gasPrice := hexToUInt256 (strField tx "gasPrice")
  -- Apply the transaction-level effects up front: bump the sender nonce, debit
  -- the up-front gas charge, and transfer `value` to the callee.
  let sender := preMap txSender
  let upfront := gasLimit * gasPrice.toNat
  let preMap := preMap.set txSender
    { sender with nonce := sender.nonce + UInt256.ofNat 1
                  balance := sender.balance - UInt256.ofNat upfront }
  let accountMap := preMap.transfer txSender toAddr value
  -- Read the block header from `blocks[0].blockHeader` — the
  -- BlockchainTest format. Field names are the un-prefixed ones
  -- (`coinbase`, `timestamp`, …); the VMTests-style `currentCoinbase`
  -- prefix is a different format we don't use here.
  let header : BlockHeader :=
    { coinbase      := hexToAddress (strField blockHeader "coinbase")
      timestamp     := hexToUInt256 (strField blockHeader "timestamp")
      number        := hexToUInt256 (strField blockHeader "number")
      prevRandao    := hexToUInt256 (strField blockHeader "difficulty")
      gasLimit      := hexToUInt256 (strField blockHeader "gasLimit")
      baseFeePerGas := ⟨0⟩, chainId := ⟨0⟩, blobBaseFee := ⟨0⟩
      blockHash     := fun _ => ⟨0⟩ }
  let execEnv : ExecutionEnv :=
    { codeOwner := toAddr
      sender    := txSender
      source    := txSender
      weiValue  := value
      calldata  := data
      code      := (accountMap toAddr).code
      gasPrice  := gasPrice
      header    := header
      depth     := 0
      permitStateMutation := true
      blobVersionedHashes := #[]
      fork                := fork }
  { toMachineState :=
      { gasAvailable := gasLimit - intrinsicGas data, activeWords := ⟨0⟩
        memory := .empty, returnData := .empty, hReturn := .empty }
    accountMap   := accountMap
    substate     := { Substate.empty with originalAccountMap := accountMap }
    executionEnv := execEnv
    pc           := ⟨0⟩
    stack        := []
    execLength   := 0
    halt         := .Running }

----------------------------------------------------------------------------
-- Runner.
----------------------------------------------------------------------------

/-- Fueled `stepF` loop until the whole execution is done.

    `stepF` reports an in-frame exception as `Except.error` rather than as a
    `halt := .Exception` state. When that happens *inside a sub-call* (the call
    stack is non-empty) it is **not** a transaction abort — the callee faulted,
    so we resume the caller with a `0` (and roll its world back to the snapshot).
    This is the executable bridge to the relational `callReturnException` rule.
    Only a fault at the top frame (empty call stack) aborts the whole run. -/
partial def run (s : State) (fuel : Nat) : Except ExecutionException State :=
  if fuel = 0 then .error .OutOfFuel else
    if s.isDone then .ok s else
      match stepF s with
      | .ok s'   => run s' (fuel - 1)
      | .error e =>
        match s.callStack with
        | []        => .error e
        | f :: rest => run (({ s with halt := .Exception e }).resumeException f rest) (fuel - 1)


inductive Outcome where
  | passCore       -- storage + nonce + code match (balances not checked)
  | passFull       -- core + balances also match
  | fail (msg : String)
  | incon (msg : String)
  deriving Repr

/-- Compare the run's final accounts to `postState`. Returns a list of
    mismatch descriptions; checks storage/nonce/code always, balance only when
    `checkBal` is set.

    Storage is checked over the **union** of pre-state and post-state slot keys
    for each address: post-state JSON omits zero-valued entries, so a slot that
    held a non-zero value in pre-state and was cleared (or rolled back) to
    zero would be invisible if we iterated post-state alone. Slots in pre that
    are absent from post are expected to be 0. -/
def cmpPost (sf : State) (preEntries postEntries : List (String × Json))
    (checkBal : Bool) : List String := Id.run do
  let mut msgs := []
  for (addrStr, accJson) in postEntries do
    let a := hexToAddress addrStr
    let got := sf.accountMap a
    let expNonce := hexToUInt256 (strField accJson "nonce")
    let expCode := hexToBytes (strField accJson "code")
    if got.nonce.toNat != expNonce.toNat then
      msgs := s!"{addrStr} nonce {got.nonce.toNat}≠{expNonce.toNat}" :: msgs
    if got.code.toList != expCode.toList then
      msgs := s!"{addrStr} code size {got.code.size}≠{expCode.size}" :: msgs
    -- Build the slot key union: post-state slots ∪ pre-state slots (for the
    -- same address, if any). Each slot's expected value is the post-state
    -- entry if listed, otherwise `0` (post-state omits cleared slots).
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

def runOne (testObj : Json) : Outcome :=
  let preMap : AccountMap :=
    (objEntries testObj "pre").foldl
      (fun σ (addrStr, accJson) => σ.set (hexToAddress addrStr) (mkAccount accJson))
      AccountMap.empty
  let fork := forkOfNetwork (strField testObj "network")
  let blocks := match subObj testObj "blocks" with | .arr a => a.toList | _ => []
  match blocks with
  | block :: _ =>
    let txs := match subObj block "transactions" with | .arr a => a.toList | _ => []
    match txs with
    | tx :: _ =>
      let s0 := buildState preMap (subObj block "blockHeader") tx fork
      -- Use the *full* tx gas limit (including intrinsic) so the coinbase
      -- fee in `finalizeTx` matches the total gas the EVM accounts for.
      let txGasLimit := hexToNat (strField tx "gasLimit")
      let sender := txSender
      let gasPrice := hexToUInt256 (strField tx "gasPrice")
      -- Steps are bounded by gas: every non-halting opcode costs ≥1 gas, and
      -- resume steps are bounded by the number of CALLs (≥700 gas each). So
      -- `2·gasAvailable` (plus slack) can never pre-empt a genuine OutOfGas; it
      -- is purely a backstop against an evaluator bug producing a 0-gas
      -- non-halting step.
      let coinbase := hexToAddress (strField (subObj block "blockHeader") "coinbase")
      let pre := objEntries testObj "pre"
      let post := objEntries testObj "postState"
      -- A top-level exception (typically OOG) is *not* an "incon" — the
      -- corpus's postState for an OOG-ing tx still has a well-defined
      -- shape: every in-tx state change rolls back to the pre-state, but
      -- the sender pays the *full* `gasLimit · gasPrice` and the coinbase
      -- receives that fee plus the block reward. We reconstruct that
      -- post-state from `preMap` (which already has the upfront gas
      -- debit + nonce bump applied by `buildState`) and add the
      -- coinbase credit by calling `finalizeTx` with `gasAvailable = 0`.
      let rollbackThenFinalize : State :=
        let senderAcc := preMap txSender
        let preMapBumped := preMap.set txSender
          { senderAcc with nonce := senderAcc.nonce + UInt256.ofNat 1
                           balance := senderAcc.balance -
                                        UInt256.ofNat (txGasLimit * gasPrice.toNat) }
        ({ s0 with accountMap := preMapBumped, gasAvailable := 0
                   substate := { Substate.empty with originalAccountMap := preMapBumped }
         }.finalizeTx txGasLimit sender gasPrice)
      let _ := coinbase  -- silence linter if not used directly
      match run s0 (2 * s0.gasAvailable + 100000) with
      | .error .OutOfFuel => .incon "fuel exhausted"
      | .error _ =>
        -- Top-level exception (typically OOG): compare against the
        -- rollback+full-fee state (preMap with sender debited
        -- `gasLimit*gasPrice` and coinbase credited that + block reward).
        match cmpPost rollbackThenFinalize pre post false with
        | [] => match cmpPost rollbackThenFinalize pre post true with
                | [] => .passFull
                | _  => .passCore
        | msgs => .fail ("oog-rollback storage-diff: " ++ String.intercalate "; " (msgs.take 3))
      | .ok sf =>
        -- Apply end-of-transaction finalisation (refund cap +
        -- leftover-gas-to-sender) — the relational counterpart is
        -- `EvalTx` in `EVM/BigStep.lean`.
        let sf' := sf.finalizeTx txGasLimit sender gasPrice
        match cmpPost sf' pre post false with
        | [] => match cmpPost sf' pre post true with
                | [] => .passFull
                | _  => .passCore
        | msgs => .fail (String.intercalate "; " (msgs.take 3))
    | [] => .incon "no transactions"
  | [] => .incon "no blocks"

structure Tally where
  passFull : Nat := 0
  passCore : Nat := 0
  fail : Nat := 0
  incon : Nat := 0
  crash : Nat := 0
  deriving Inhabited

def Tally.add (t u : Tally) : Tally :=
  { passFull := t.passFull + u.passFull, passCore := t.passCore + u.passCore
    fail := t.fail + u.fail, incon := t.incon + u.incon, crash := t.crash + u.crash }

def Tally.total (t : Tally) : Nat :=
  t.passFull + t.passCore + t.fail + t.incon + t.crash

partial def collectJson (p : System.FilePath) : IO (Array System.FilePath) := do
  let mut out := #[]
  for ent in (← p.readDir) do
    let path := ent.path
    if (← path.isDir) then out := out ++ (← collectJson path)
    else if path.toString.endsWith ".json" then out := out.push path
  return out.qsort (fun a b => a.toString < b.toString)

/-- Run every `*_Constantinople` test in one file; return one `(tag, name, msg)`
    triple per test (`tag ∈ {PASS_FULL, PASS_CORE, FAIL, INCON}`). -/
def runFileResults (path : System.FilePath) : IO (Array (String × String × String)) := do
  let txt ← IO.FS.readFile path
  match Json.parse txt with
  | .error e => return #[("CRASH", path.fileName.getD path.toString, s!"parse: {e}")]
  | .ok j =>
    let entries := match j with | .obj m => m.toArray.toList | _ => []
    let mut out := #[]
    for (name, testObj) in entries do
      -- Each test JSON contains one variant per fork (`_Frontier`,
      -- `_Homestead`, `_EIP150`, `_EIP158`, `_Byzantium`,
      -- `_Constantinople`, `_ConstantinopleFix`, …). Run every variant
      -- whose `"network"` field maps to one of our supported forks;
      -- skip variants whose fork we don't model.
      let network := strField testObj "network"
      let supported := ["Frontier", "Homestead", "EIP150", "EIP158",
                        "Byzantium", "Constantinople", "ConstantinopleFix"]
      if !supported.contains network then continue
      let r := match runOne testObj with
        | .passFull => ("PASS_FULL", name, "")
        | .passCore => ("PASS_CORE", name, "")
        | .fail m   => ("FAIL", name, m)
        | .incon m  => ("INCON", name, m)
      out := out.push r
    return out

/-- Run `files`, up to `jobs` `Task`s in flight. Prints per-test `FAIL`/`INCON`
    notes (stable, spawn order) when `verbose`, then returns the folded tally.
    Mirrors `VMRunner.runDir`. -/
def runFiles (files : Array System.FilePath) (jobs : Nat) (verbose : Bool) : IO Tally := do
  let mut t : Tally := {}
  let mut i := 0
  let n := files.size
  let batch := Nat.max 1 jobs
  while i < n do
    let stop := Nat.min (i + batch) n
    let mut tasks : Array (Task (Except IO.Error (Array (String × String × String)))) := #[]
    for k in [i:stop] do
      tasks := tasks.push (← IO.asTask (runFileResults files[k]!))
    for task in tasks do
      match (← IO.wait task) with
      | .ok results =>
        for (tag, name, msg) in results do
          match tag with
          | "PASS_FULL" => t := { t with passFull := t.passFull + 1 }
          | "PASS_CORE" => t := { t with passCore := t.passCore + 1 }
          | "FAIL"      => t := { t with fail := t.fail + 1 }
                           if verbose then IO.println s!"FAIL {name}: {msg}"
          | "INCON"     => t := { t with incon := t.incon + 1 }
                           if verbose then IO.println s!"INCON {name}: {msg}"
          | _           => t := { t with crash := t.crash + 1 }
                           if verbose then IO.println s!"CRASH {name}: {msg}"
      | .error e =>
        t := { t with crash := t.crash + 1 }
        if verbose then IO.println s!"CRASH (task): {e}"
    i := stop
  return t

/-- Resolve worker count: `-j N`, else env `STATETESTS_JOBS`, else 8. -/
def parseJobs (args : List String) : Nat × List String := Id.run do
  let rec go : List String → Option Nat → List String → Nat × List String
    | [], n, acc => (n.getD 0, acc.reverse)
    | "-j" :: v :: rest, _, acc => go rest (some v.toNat!) acc
    | x :: rest, n, acc => go rest n (x :: acc)
  go args none []

def main (args : List String) : IO Unit := do
  let verbose := args.contains "-v"
  let (jobs0, rest) := parseJobs (args.filter (· != "-v"))
  let jobs ← if jobs0 > 0 then pure jobs0 else do
    match (← IO.getEnv "STATETESTS_JOBS") with
    | some s => pure (Nat.max 1 s.toNat!)
    | none   => pure 8
  let root : System.FilePath := rest.headD "."
  let files ← if (← root.isDir) then collectJson root else pure #[root]
  let t ← runFiles files jobs verbose
  IO.println s!"pass(full={t.passFull} core+={t.passCore}) fail={t.fail} \
incon={t.incon} crash={t.crash} (total {t.total})"

end StateTests

def main (args : List String) : IO Unit := StateTests.main args
