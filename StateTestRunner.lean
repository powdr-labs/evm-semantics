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

/-- Default sender if we can't infer one from `pre`. Most legacy
    ethereum/tests use this address. -/
def defaultTxSender : AccountAddress :=
  hexToAddress "0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b"

/-- Recover the transaction sender by scanning the `pre` accounts for
    a code-less account whose nonce matches `tx.nonce`. The legacy
    ethereum/tests don't carry an explicit sender field, and we don't
    do ECDSA recovery, so this nonce/EOA match is the best we can do.

    Falls back to [[defaultTxSender]] when no unique candidate exists. -/
def recoverSender (preEntries : List (String × Json)) (tx : Json) : AccountAddress :=
  let txNonce := hexToUInt256 (strField tx "nonce")
  let candidates := preEntries.filterMap (fun (addrStr, accJson) =>
    let code := hexToBytes (strField accJson "code")
    let nonce := hexToUInt256 (strField accJson "nonce")
    if code.size = 0 ∧ nonce.toNat = txNonce.toNat then
      some (hexToAddress addrStr) else none)
  match candidates with
  | [a] => a
  | _   => defaultTxSender

def mkAccount (accJson : Json) : Account :=
  let storage := (storageEntries accJson).foldl
    (fun st (slot, val) => st.set (hexToUInt256 slot) (hexToUInt256 val)) Storage.empty
  { nonce    := hexToUInt256 (strField accJson "nonce")
    balance  := hexToUInt256 (strField accJson "balance")
    code     := hexToBytes   (strField accJson "code")
    storage  := storage
    tstorage := Storage.empty }

/-- Intrinsic transaction gas: 21000 + per-byte calldata costs (+ 32000
    `G_txcreate` for a contract-creation transaction).
    Pre-EIP-2028 (Frontier..Petersburg): 68 per non-zero byte, 4 per
    zero byte. EIP-2028 (Istanbul+) reduced the non-zero rate from 68
    to 16. -/
def intrinsicGas (fork : Fork) (data : ByteArray) (isCreate : Bool := false) : Nat :=
  Id.run do
  let mut g := 21000 + (if isCreate then 32000 else 0)
  let nzCost : Nat := if fork.atLeast .Istanbul then 16 else 68
  for b in data do
    g := g + (if b == 0 then 4 else nzCost)
  return g

/-- Yellow Paper CREATE address derivation: `keccak256(rlp([sender,
    nonce]))[12:]`. This is the formula for both top-level
    contract-creation transactions and the in-EVM `CREATE` opcode. -/
def createAddrOf (sender : AccountAddress) (nonce : Nat) : AccountAddress :=
  AccountAddress.ofUInt256 (EvmSemantics.keccak256
    (Rlp.encodeAddrNonce sender nonce))

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
  | "Istanbul"          => .Istanbul
  | "MuirGlacier"       => .MuirGlacier
  | "Berlin"            => .Berlin
  | "London"            => .London
  | "ArrowGlacier"      => .ArrowGlacier
  | "GrayGlacier"       => .GrayGlacier
  | "Merge" | "Paris"   => .Paris
  | "Shanghai"          => .Shanghai
  | "Cancun"            => .Cancun
  | _                   => .Cancun

/-- True iff the tx is a *contract-creation* transaction — `"to"` is
    absent / empty / the empty hex string. In that case the tx data
    is the init code and the recipient is a fresh address derived
    from `(sender, sender.nonce)`. -/
def isCreateTx (tx : Json) : Bool :=
  let toStr := strField tx "to"
  toStr.length = 0 ∨ toStr == "0x"

/-- Build the top-level execution `State` for a BlockchainTest test object,
    given its `pre` accounts and the block's transaction JSON. The `fork`
    argument is taken from the test's `"network"` field. Handles both
    a regular call-transaction (`"to"` set) and a contract-creation
    transaction (`"to"` empty). -/
def buildState (sender : AccountAddress) (preMap : AccountMap)
    (blockHeader tx : Json) (fork : Fork) : State :=
  let create   := isCreateTx tx
  let value    := hexToUInt256 (strField tx "value")
  let data     := hexToBytes   (strField tx "data")
  let gasLimit := hexToNat     (strField tx "gasLimit")
  let gasPrice := hexToUInt256 (strField tx "gasPrice")
  -- Apply the transaction-level effects up front: bump the sender nonce
  -- and debit the up-front gas charge. (Value transfer is done below,
  -- separately for the call vs create cases.)
  let senderAcc := preMap sender
  let upfront := gasLimit * gasPrice.toNat
  let senderPreNonce := senderAcc.nonce.toNat
  let preMap := preMap.set sender
    { senderAcc with nonce := senderAcc.nonce + UInt256.ofNat 1
                     balance := senderAcc.balance - UInt256.ofNat upfront }
  -- Compute the destination address. For a CREATE-tx, derive the new
  -- contract's address from the *pre-bump* sender nonce per YP §7.
  let toAddr   :=
    if create then createAddrOf sender senderPreNonce
    else hexToAddress (strField tx "to")
  -- Effect the value transfer. For a CREATE-tx we additionally bump
  -- the new account's nonce to 1 (EIP-158 / EIP-161).
  let accountMap :=
    if create then
      let am := preMap.transfer sender toAddr value
      let newAcc := am toAddr
      if fork.atLeast .EIP158 then am.set toAddr { newAcc with nonce := ⟨1⟩ } else am
    else preMap.transfer sender toAddr value
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
  -- For a CREATE-tx, the tx data is the init code (executed as the new
  -- contract's bytecode), and the calldata is empty. For a regular
  -- call-tx, the data is the calldata and the code comes from `toAddr`.
  let execEnv : ExecutionEnv :=
    { codeOwner := toAddr
      sender    := sender
      source    := sender
      weiValue  := value
      calldata  := if create then ByteArray.empty else data
      code      := if create then data else (accountMap toAddr).code
      gasPrice  := gasPrice
      header    := header
      depth     := 0
      permitStateMutation := true
      blobVersionedHashes := #[]
      fork                := fork }
  -- EIP-2929 access-list pre-warming (Berlin+): the sender, the call
  -- target, the precompiles 0x01..0x09, and (Shanghai+) the coinbase
  -- start the transaction warm.
  let preWarm : List AccountAddress :=
    if fork.atLeast .Berlin then
      let base := [sender, toAddr,
                   AccountAddress.ofNat 1, AccountAddress.ofNat 2,
                   AccountAddress.ofNat 3, AccountAddress.ofNat 4,
                   AccountAddress.ofNat 5, AccountAddress.ofNat 6,
                   AccountAddress.ofNat 7, AccountAddress.ofNat 8,
                   AccountAddress.ofNat 9]
      if fork.atLeast .Shanghai then header.coinbase :: base else base
    else []
  let warmedSub : Substate :=
    preWarm.foldl (fun A a => A.addAccessedAccount a)
      { Substate.empty with originalAccountMap := accountMap }
  { toMachineState :=
      { gasAvailable := gasLimit - intrinsicGas fork data create
        activeWords := ⟨0⟩
        memory := .empty, returnData := .empty, hReturn := .empty }
    accountMap   := accountMap
    executionEnv := execEnv
    pc           := ⟨0⟩
    stack        := []
    execLength   := 0
    halt         := .Running
    substate     := warmedSub }

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
      let sender := recoverSender (objEntries testObj "pre") tx
      let s0 := buildState sender preMap (subObj block "blockHeader") tx fork
      -- Use the *full* tx gas limit (including intrinsic) so the coinbase
      -- fee in `finalizeTx` matches the total gas the EVM accounts for.
      let txGasLimit := hexToNat (strField tx "gasLimit")
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
        let senderAcc := preMap sender
        let preMapBumped := preMap.set sender
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
        let expRoot :=
          hexToUInt256 (strField (subObj block "blockHeader") "stateRoot")
        let gotRoot := AccountMap.stateRoot rollbackThenFinalize.accountMap
        let rootMsg :=
          if expRoot.toNat = 0 then []
          else if gotRoot.toNat = expRoot.toNat then []
          else [s!"stateRoot {gotRoot}≠{expRoot}"]
        match cmpPost rollbackThenFinalize pre post true ++ rootMsg with
        | [] => .passFull
        | msgs => .fail ("oog-rollback diff: " ++ String.intercalate "; " (msgs.take 3))
      | .ok sf =>
        -- For a CREATE-tx, the top-level frame's `hReturn` *is* the
        -- contract's deployed code. We deploy it at the new address
        -- before finalising, charging `G_codedeposit = 200 · |code|`
        -- from whatever the init code left behind. If the deposit
        -- doesn't fit (or the init code REVERTed / threw), the world
        -- rolls back to the pre-state for accountMap (sender keeps
        -- `value`; intrinsic gas is still paid).
        let create := isCreateTx tx
        let newAddr := s0.executionEnv.codeOwner
        let codeLen := sf.hReturn.size
        let depositCost := State.codeDepositPerByte * codeLen
        let initSuccess :=
          match sf.halt with
          | .Success | .Returned => true
          | _                    => false
        let sfDeployed :=
          if create then
            if initSuccess ∧ depositCost ≤ sf.gasAvailable then
              { sf with
                  accountMap   := sf.accountMap.set newAddr
                                    { (sf.accountMap newAddr) with code := sf.hReturn }
                  gasAvailable := sf.gasAvailable - depositCost }
            else
              -- Deposit OOG or init reverted/exception: roll back to preMap.
              -- preMap here is the *post-buildState* preMap (sender nonce
              -- bumped, gas debited) — but the in-EVM value transfer is
              -- undone by reverting to it.
              { sf with
                  accountMap   := preMap
                  gasAvailable := if initSuccess then 0 else sf.gasAvailable }
          else sf
        -- Apply end-of-transaction finalisation (refund cap +
        -- leftover-gas-to-sender) — the relational counterpart is
        -- `EvalTx` in `EVM/BigStep.lean`.
        let sf' := sfDeployed.finalizeTx txGasLimit sender gasPrice
        let expRoot :=
          hexToUInt256 (strField (subObj block "blockHeader") "stateRoot")
        let gotRoot := AccountMap.stateRoot sf'.accountMap
        let rootMsg :=
          if expRoot.toNat = 0 then []
          else if gotRoot.toNat = expRoot.toNat then []
          else [s!"stateRoot {gotRoot}≠{expRoot}"]
        match cmpPost sf' pre post true ++ rootMsg with
        | [] => .passFull
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
                        "Byzantium", "Constantinople", "ConstantinopleFix",
                        "Istanbul", "MuirGlacier", "Berlin", "London",
                        "ArrowGlacier", "GrayGlacier", "Merge", "Paris",
                        "Shanghai", "Cancun"]
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
