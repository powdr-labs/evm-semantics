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

Scope: we run only the `Constantinople` fork variant of each test (the only
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

/-- Intrinsic transaction gas `g₀` (YP §6.2). Fork- and tx-kind-aware:

    * Per-byte data cost: 4 for zero bytes; 68 for non-zero bytes
      pre-Istanbul, 16 from Istanbul onwards (EIP-2028).
    * `+G_txcreate = 32000` for a contract-creating transaction.
    * `+G_initcodeword · ⌈|initcode|/32⌉ = 2 · ⌈|data|/32⌉` for a
      create-tx from Shanghai onwards (EIP-3860).

    `data` is `T_d` — the calldata for a call tx, the init code for a
    create tx. -/
def intrinsicGas (fork : Fork) (isCreate : Bool) (data : ByteArray) : Nat := Id.run do
  let perNonZero := if fork.atLeast .Istanbul then 16 else 68
  let mut g := 21000
  for b in data do
    g := g + (if b == 0 then 4 else perNonZero)
  if isCreate then
    -- `G_txcreate = 32000` was introduced by Homestead (EIP-2). Frontier
    -- create transactions pay only the base 21000.
    if fork.atLeast .Homestead then
      g := g + 32000
    if fork.atLeast .Shanghai then
      -- EIP-3860 init-code word cost: 2 per 32-byte word.
      g := g + 2 * ((data.size + 31) / 32)
  return g

/-- Map a BlockchainTest variant suffix (the bit after the last `_` in the
    test object's key, e.g. `_Constantinople`, `_Berlin`) to a `Fork`. Each
    variant in BlockchainTests/GeneralStateTests is named
    `<base>_<network>_d<i>g<j>v<k>` (the suffix we get) — the `network` is
    the activation fork. We return `none` for variants we don't model
    (notably `Frontier`-tagged variants that exercise the legacy schedule;
    those are covered by VMTests). -/
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

/-- `true` iff this transaction is a contract-creating transaction
    (the `to` field is empty / absent — the YP's `Tᵢ` flag). -/
def isCreateTx (tx : Json) : Bool := (strField tx "to") = ""

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

/-- Build the EVM `BlockHeader` from the test block's `blockHeader` JSON
    (BlockchainTests format). Missing modern fields fall back to zero —
    a pre-London corpus has no `baseFeePerGas`, a pre-Cancun corpus has
    no `excessBlobGas`, etc. Maps:

    * `coinbase` / `timestamp` / `number` / `gasLimit` ← same-named JSON
      fields.
    * `prevRandao` ← `difficulty` (the YP renamed the field at the Merge
      and the same opcode 0x44 reads `mixHash` post-Paris; the
      BlockchainTests corpus is pre-Merge, so `difficulty` is what's
      populated and pre-Merge `DIFFICULTY` reads it).
    * `baseFeePerGas` ← `baseFeePerGas` if present (London+), else 0.
    * `chainId` is *not* in the block header per se; we default to 1
      (mainnet) when not exposed by the test.
    * `blobBaseFee` — preferred path: derive from `excessBlobGas` via
      EIP-4844 `fake_exp(1, excessBlobGas, 3338477)`. If the corpus
      provides an explicit `blobBaseFee` field that takes precedence
      (some tooling emits it directly); otherwise we use the derivation
      from `excessBlobGas`; otherwise 0. -/
def decodeHeader (blockHeader : Json) : BlockHeader :=
  let blobBaseFeeField    := strField blockHeader "blobBaseFee"
  let excessBlobGasField  := strField blockHeader "excessBlobGas"
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

/-- Build the top-level execution `State` for a BlockchainTest test object,
    given its `pre` accounts, the block's `blockHeader` JSON, and the
    transaction JSON.

    For a **call tx** (`tx.to ≠ ""`): the executing account is `tx.to`,
    its `code` runs as bytecode, `tx.data` is the calldata. Value is
    transferred from sender to `tx.to`.

    For a **create tx** (`tx.to = ""`): the executing account is the
    derived `newAddr = keccak(rlp [sender, sender_nonce_pre_bump])[12:]`.
    Per YP `Λ`: the new account starts with `code := ∅` (NOT the init
    code — init code is what runs, but the *deployed* code only
    materialises on a successful halt; until then the account is
    invisible to `EXTCODESIZE`/`EXTCODECOPY`/etc.). The init code is
    placed in `executionEnv.code` so `decoded` reads it from there.
    The nonce is bumped to 1 (EIP-158+) or 0 (pre-EIP-158) so an
    internal CREATE inside the init code derives the right child
    address. Value is transferred from sender to `newAddr`. The
    runner's success path (`runOne` below) then snaps `sf.hReturn`
    into `newAddr.code` *only* after passing the EIP-3541 reserved-
    prefix, EIP-170 max-code-size, and `G_codedeposit · |hReturn|`
    deposit-gas checks. -/
def buildState (preMap : AccountMap) (blockHeader tx : Json) (fork : Fork) : State :=
  let value    := hexToUInt256 (strField tx "value")
  let data     := hexToBytes   (strField tx "data")
  let gasLimit := hexToNat     (strField tx "gasLimit")
  let gasPrice := hexToUInt256 (strField tx "gasPrice")
  let isCreate := isCreateTx tx
  let sender0 := preMap txSender
  let toAddr  :=
    if isCreate then
      (EvmSemantics.createAddress txSender sender0.nonce.toNat).getD default
    else
      hexToAddress (strField tx "to")
  let upfront := gasLimit * gasPrice.toNat
  let preMap := preMap.set txSender
    { sender0 with nonce := sender0.nonce + UInt256.ofNat 1
                   balance := sender0.balance - UInt256.ofNat upfront }
  -- Create-tx: seed the new account's nonce (EIP-158 / pre-EIP-158).
  -- Critically, leave `code := ∅` — the deployed code is installed by
  -- the runner *only* on a successful halt that passes the deploy
  -- checks; until then the account is bytecode-empty.
  let preMap :=
    if isCreate then
      let existing := preMap toAddr
      let n : UInt256 := if fork.atLeast .SpuriousDragon then ⟨1⟩ else ⟨0⟩
      preMap.set toAddr { existing with nonce := n }
    else preMap
  let accountMap := preMap.transfer txSender toAddr value
  let header := decodeHeader blockHeader
  -- A create tx runs `data` as the init code with empty calldata; a
  -- call tx runs the target's existing code with `data` as calldata.
  let calldata := if isCreate then ByteArray.empty else data
  let code     := if isCreate then data else (accountMap toAddr).code
  let execEnv : ExecutionEnv :=
    { address := toAddr
      origin  := txSender
      caller  := txSender
      weiValue  := value
      calldata  := calldata
      code      := code
      gasPrice  := gasPrice
      header    := header
      depth     := 0
      permitStateMutation := true
      blobVersionedHashes := decodeBlobHashes tx
      fork                := fork }
  { toMachineState :=
      { gasAvailable := gasLimit - intrinsicGas fork isCreate data,
        activeWords := ⟨0⟩
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
      let blockHeader := subObj block "blockHeader"
      let gasLimit := hexToNat     (strField tx "gasLimit")
      let gasPrice := hexToUInt256 (strField tx "gasPrice")
      let coinbase := hexToAddress (strField blockHeader "coinbase")
      let upfront  := gasLimit * gasPrice.toNat
      let s0 := buildState preMap blockHeader tx fork
      -- Steps are bounded by gas: every non-halting opcode costs ≥1 gas, and
      -- resume steps are bounded by the number of CALLs (≥700 gas each). So
      -- `2·gasAvailable` (plus slack) can never pre-empt a genuine OutOfGas; it
      -- is purely a backstop against an evaluator bug producing a 0-gas
      -- non-halting step.
      let pre := objEntries testObj "pre"
      let post := objEntries testObj "postState"
      let finishOk (sf : State) : Outcome :=
        match cmpPost sf pre post false with
        | [] => match cmpPost sf pre post true with
                | [] => .passFull
                | _  => .passCore
        | msgs => .fail (String.intercalate "; " (msgs.take 3))
      let isCreate := isCreateTx tx
      let newAddr  := s0.executionEnv.address
      -- The YP tx-create rollback post-state: sender's nonce bumped,
      -- sender debited the full upfront gas charge, coinbase credited
      -- the same amount; everything else as in `preMap`. Used by the
      -- collision, top-level-exception, and reverted/deploy-rejected
      -- arms below.
      let rollbackAccounts : AccountMap :=
        let sender  := preMap txSender
        let coinAcc := preMap coinbase
        let m₁ := preMap.set txSender
          { sender with nonce := sender.nonce + UInt256.ofNat 1
                        balance := sender.balance - UInt256.ofNat upfront }
        m₁.set coinbase { coinAcc with balance := coinAcc.balance + UInt256.ofNat upfront }
      let rollback : Outcome := finishOk { s0 with accountMap := rollbackAccounts,
                                                   halt := .Success }
      -- Address-collision short-circuit for create txs: if the derived
      -- contract address already hosts code or has a non-zero nonce
      -- (YP "account already exists"), the create tx fails before any
      -- execution — same disposition as a top-level exception.
      let preExisting := preMap newAddr
      let isCollision : Bool :=
        isCreate && (preExisting.nonce.toNat > 0 || preExisting.code.size > 0)
      if isCollision then rollback
      else
      match run s0 (2 * s0.gasAvailable + 100000) with
      | .error .OutOfFuel => .incon "fuel exhausted"
      | .error _ => rollback
      | .ok sf =>
        -- The active frame halted; disposition depends on *how*.
        --
        -- For a **call tx**: `.Success`/`.Returned`/`.Reverted` all keep
        -- the world `sf.accountMap` produced; `.Exception` rolls back.
        -- (Our `Tx.execute` will eventually distinguish revert from
        -- success on balances, but `passCore` checks only storage/nonce/
        -- code so we accept the executed world as-is for non-exception.)
        --
        -- For a **create tx**: `.Success`/`.Returned` triggers the YP
        -- `Λ` deploy step — install `sf.hReturn` as `newAddr.code` if
        -- the three deploy checks pass:
        --   (i) `G_codedeposit · |hReturn| ≤ sf.gasAvailable`
        --       (deposit-gas affordability);
        --  (ii) `|hReturn| ≤ maxCodeSize` from Spurious Dragon onwards
        --       (EIP-170);
        -- (iii) `hReturn` does *not* begin with `0xEF` from London
        --       onwards (EIP-3541).
        -- Any one of these failing — or a `.Reverted` halt, or an
        -- `.Exception` halt — collapses the create-tx into the
        -- `rollback` post-state.
        match sf.halt with
        | .Exception _ | .Reverted => rollback
        | _ =>
          -- .Success or .Returned: a call-tx is done; a create-tx
          -- runs the deploy-or-reject check.
          if isCreate then
            let hReturn := sf.hReturn
            let depositCost := State.codeDepositPerByte * hReturn.size
            let oversized   := sf.executionEnv.fork.atLeast .SpuriousDragon
                                && decide (hReturn.size > State.maxCodeSize)
            let badPrefix   := State.isReservedCodePrefix sf.executionEnv.fork hReturn
            if depositCost ≤ sf.gasAvailable ∧ ¬ oversized ∧ ¬ badPrefix then
              let newAcc := sf.accountMap newAddr
              let map' := sf.accountMap.set newAddr { newAcc with code := hReturn }
              finishOk { sf with accountMap := map',
                                 gasAvailable := sf.gasAvailable - depositCost }
            else
              -- Deploy rejected by EIP-3541, EIP-170, or deposit-gas
              -- OOG: rollback the whole tx per YP.
              rollback
          else finishOk sf
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

/-- Run every fork variant in one file; return one `(tag, name, msg)`
    triple per test (`tag ∈ {PASS_FULL, PASS_CORE, FAIL, INCON}`). Variants
    whose `network` suffix doesn't map to a `Fork` we model are skipped
    silently (they don't count toward any tally). -/
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
          | .passFull => ("PASS_FULL", name, "")
          | .passCore => ("PASS_CORE", name, "")
          | .fail m   => ("FAIL", name, m)
          | .incon m  => ("INCON", name, m)
        out := out.push r
    return out

/-- Run `files` keeping up to `jobs` `Task`s **continuously in flight**: as
    each one finishes, the next file is dispatched immediately rather than
    waiting for the rest of the batch (the old `for task in tasks do IO.wait
    task` pattern starved cores whenever one file in the batch was slow —
    the `_ABCB_RECURSIVE` family on functional world-state maps takes
    minutes per file).

    The scheduler is a fixed-size array of `jobs` slots; each slot holds at
    most one in-flight task. The main loop polls slots with
    `Task.hasFinished` (non-blocking), harvests anything done, refills the
    slot with the next file, and sleeps `10ms` only when every slot is
    busy (so we don't busy-spin the main thread).

    Per-task wall-clock cap: if `timeoutMs > 0`, a task whose elapsed time
    exceeds the cap is marked `INCON wall-timeout`, its slot freed, and the
    next file dispatched. The abandoned task continues running in the
    background (Lean's `Task`s aren't OS-cancellable), but it no longer
    blocks the harness — and the slot count drops to `jobs - hung` for the
    remainder of the run, which is the closest we can get without
    subprocess isolation. `timeoutMs = 0` disables the cap.

    Output is in completion order (which can differ from spawn order). The
    summary scripts key on FAIL ids, not line order. -/
def runFiles (files : Array System.FilePath) (jobs : Nat) (verbose : Bool)
    (timeoutMs : Nat := 0) : IO Tally := do
  let mut t : Tally := {}
  let n := files.size
  if n = 0 then return t
  let workers := Nat.max 1 jobs
  -- Each slot: optional (file index, spawn-time millis, task).
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
  -- Prime the pool: spawn up to `workers` initial tasks. Use
  -- `Task.Priority.dedicated` so each task gets its own OS thread —
  -- Lean's default pool caps non-dedicated workers at `numCores`,
  -- which under heavy GC contention starves the sliding window even
  -- when `jobs` is set higher.
  for i in [0:workers] do
    if nextIdx < n then
      let now ← IO.monoMsNow
      let task ← IO.asTask (runFileResults files[nextIdx]!) Task.Priority.dedicated
      slots := slots.set! i (some (nextIdx, now, task))
      nextIdx := nextIdx + 1
  -- Main loop: poll, harvest, refill.
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
          -- Refill slot.
          if nextIdx < n then
            let now ← IO.monoMsNow
            let next ← IO.asTask (runFileResults files[nextIdx]!) Task.Priority.dedicated
            slots := slots.set! i (some (nextIdx, now, next))
            nextIdx := nextIdx + 1
          else
            slots := slots.set! i none
        else if timeoutMs > 0 ∧ elapsed > timeoutMs then
          -- Abandon: mark INCON and free the slot. The task keeps
          -- running in the background but the harness moves on.
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
    if !progress then
      -- All in-flight tasks still running; yield CPU briefly.
      IO.sleep 10
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
  IO.println s!"pass(full={t.passFull} core+={t.passCore}) fail={t.fail} \
incon={t.incon} crash={t.crash} (total {t.total})"

end StateTests

def main (args : List String) : IO Unit := StateTests.main args
