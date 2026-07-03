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

It executes *valid* chains and compares the post-state in the same three
tiers as the state-test runners (`passCore` ⊂ `passFull` ⊂ `passRoot`). All
transaction types execute through `Tx.execute` — legacy, EIP-2930 access
lists, EIP-1559 fee-market, EIP-4844 blobs and EIP-7702 set-code (the access
list / blob versioned hashes / authorization list are parsed from the block
tx and passed through, as in the `gstatetests` runner).

Still deferred and reported `INCON` (so they land in the baseline rather
than counting as failures):

* **Invalid-block tests** — a block carrying `expectException` must be
  *rejected* by header/consensus validation, which needs a block-`rlp`
  decoder and the header transition checks (a later stage).
* **Fork-transition networks** (e.g. `CancunToPragueAtTime15k`) — the
  timestamp-triggered mid-chain fork switch is not modelled.
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
  -- EIP-7892 blob-parameter-only forks change only the blob-gas schedule
  -- (target/max blobs, base-fee update fraction), not EVM opcodes, so they
  -- are semantically Osaka for `Tx.execute`/`stepF`. The differing blob
  -- update fraction is read from the fixture's `config.blobSchedule` (see
  -- `blobUpdateFractionAt`), not from the `Fork`.
  | "BPO1" | "BPO2" | "BPO3" | "BPO4" | "BPO5" => some .Osaka
  | _                   => none

----------------------------------------------------------------------------
-- Block header decode (the EVM-env subset) + EIP-4844 blob base fee.
----------------------------------------------------------------------------

/-- EIP-4844 `fake_exponential(factor, numerator, denominator)` —
    `⌊factor · e^(numerator/denominator)⌋` approximated by the Taylor series
    with *factorial* denominators (`Σ factor·num^i / (denom^i · i!)`). The
    running term is `numerator_accum`, seeded at `factor·denominator` and
    updated `numerator_accum := numerator_accum · numerator / (denominator · i)`
    each step (so the `i!` accumulates), summed until it underflows to `0`; the
    total is then divided by `denominator`. A plain `num^i` polynomial (without
    the `/i!`) overshoots astronomically for large `numerator`, which would push
    the blob base fee above `maxFeePerBlobGas` and spuriously reject blob txs. -/
partial def fakeExponential (factor numerator denominator : Nat) : Nat :=
  let rec go (i output numAccum : Nat) (fuel : Nat) : Nat :=
    if fuel = 0 ∨ numAccum = 0 then output
    else go (i + 1) (output + numAccum) (numAccum * numerator / (denominator * i)) (fuel - 1)
  (go 1 0 (factor * denominator) 100000) / denominator

/-- Decode a `blockHeader` object into the EVM-env `BlockHeader`. Post-Merge
    `prevRandao` reads `mixHash`, falling back to `difficulty` pre-Merge.
    `blobBaseFee = fake_exponential(1, excessBlobGas, blobFrac)` (EIP-4844),
    where `blobFrac` is the block's fork-specific update fraction supplied by
    the caller (see `blobUpdateFractionAt`). `blockHash` is the caller's
    number→hash closure (EIP-2935 / BLOCKHASH). -/
def decodeBlockHeader (bh : Json) (blobFrac : Nat)
    (blockHashFn : UInt256 → UInt256 := fun _ => ⟨0⟩) : BlockHeader :=
  let mixHash := strField bh "mixHash"
  let prevRandao : UInt256 :=
    if mixHash ≠ "" ∧ mixHash ≠ "0x0000000000000000000000000000000000000000000000000000000000000000"
    then hexToUInt256 mixHash
    else hexToUInt256 (strField bh "difficulty")
  let excessStr := strField bh "excessBlobGas"
  let blobBaseFee : UInt256 :=
    if excessStr ≠ "" then UInt256.ofNat (fakeExponential 1 (hexToUInt256 excessStr).toNat blobFrac)
    else ⟨0⟩
  { coinbase      := hexToAddress (strField bh "coinbase")
    timestamp     := hexToUInt256 (strField bh "timestamp")
    number        := hexToUInt256 (strField bh "number")
    prevRandao    := prevRandao
    gasLimit      := hexToUInt256 (strField bh "gasLimit")
    baseFeePerGas := hexToUInt256 (strField bh "baseFeePerGas")
    chainId       := ⟨1⟩
    blobBaseFee   := blobBaseFee
    blockHash     := blockHashFn }

----------------------------------------------------------------------------
-- Transaction build (block-tx JSON: scalar fields, `sender` given).
----------------------------------------------------------------------------

/-- Parse a block tx's EIP-2930 `accessList` (`[{address, storageKeys:[…]}]`)
    into `(address, storageKeys)` pairs. Empty when absent. -/
def parseAccessList (tx : Json) : List (AccountAddress × List UInt256) :=
  (jsonArr (subObj tx "accessList")).toList.map (fun e =>
    let addr := hexToAddress (strField e "address")
    let keys := (jsonArr (subObj e "storageKeys")).toList.filterMap
      (fun k => match k with | .str s => some (hexToUInt256 s) | _ => none)
    (addr, keys))

/-- Parse the EIP-4844 `blobVersionedHashes` array. Empty for non-blob txs. -/
def parseBlobHashes (tx : Json) : Array UInt256 :=
  (jsonArr (subObj tx "blobVersionedHashes")).filterMap
    (fun h => match h with | .str s => some (hexToUInt256 s) | _ => none)

/-- Parse the EIP-7702 `authorizationList` into `Tx.Authorization`s, using the
    fixture's recovered `signer` as the authority (the runner takes the tx
    `sender` directly rather than recovering it). -/
def parseAuthList (tx : Json) : List Tx.Authorization :=
  (jsonArr (subObj tx "authorizationList")).toList.map (fun e =>
    { chainId   := hexToNat     (strField e "chainId")
      address   := hexToAddress (strField e "address")
      nonce     := hexToNat     (strField e "nonce")
      authority := hexToAddress (strField e "signer") })

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
    nonce     := hexToUInt256 (strField tx "nonce")
    accessList := parseAccessList tx
    maxFeePerBlobGas := hexToUInt256 (strField tx "maxFeePerBlobGas")
    authList  := parseAuthList tx }

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
    (threading the post-state), then apply the end-of-block request system
    calls, withdrawals and — once for the whole block — the pre-Merge block
    reward. Returns `.error reason` for a fuel-exhausted run (⇒ `INCON`). -/
def executeBlock (preMap : AccountMap) (block : Json) (fork : Fork)
    (blobFrac : Nat := 5007716)
    (blockHashFn : UInt256 → UInt256 := fun _ => ⟨0⟩) :
    Except String AccountMap := do
  let header := decodeBlockHeader (subObj block "blockHeader") blobFrac blockHashFn
  let baseFee := header.baseFeePerGas.toNat
  -- Block-start system calls: EIP-4788 beacon roots (Cancun+) and EIP-2935
  -- block-hash history (Prague+).
  let mut m := applyBlockHashHistory (applyBeaconRoot preMap block header fork) block header fork
  for tx in jsonArr (subObj block "transactions") do
    let t := buildTx tx baseFee
    let blobHashes := parseBlobHashes tx
    let fuel := 2 * t.gasLimit + 100_000
    -- `applyReward := false`: the fixed block subsidy is paid once per
    -- block below, not per transaction. Legacy / EIP-2930 / EIP-1559 /
    -- EIP-4844 / EIP-7702 all execute through `Tx.execute`.
    let result := EvmSemantics.Tx.execute m header t fork fuel blobHashes (applyReward := false)
    match result.outcome with
    | .fuelExhausted => throw "fuel exhausted"
    | _ => m := result.finalAccounts
  -- End-of-block: EIP-7002/7251 request system calls, withdrawals, then the
  -- (pre-Merge) block reward on the block's own coinbase.
  m := applyBlockEndRequests m header fork
  m := applyWithdrawals m block
  pure (Tx.applyBlockReward m header.coinbase fork)

----------------------------------------------------------------------------
-- Independent invalid-block detection (header consensus rules from `rlp`).
----------------------------------------------------------------------------

/-- The consensus parent-header fields the transition rules need. -/
structure ParentInfo where
  gasLimit     : Nat
  excessBlobGas : Nat
  blobGasUsed  : Nat
  deriving Inhabited

/-- Read `(gasLimit, excessBlobGas, blobGasUsed)` from a decoded header JSON
    object (`blockHeader` or `genesisBlockHeader`). -/
def parentInfoOf (bh : Json) : ParentInfo :=
  { gasLimit      := hexToNat (strField bh "gasLimit")
    excessBlobGas := hexToNat (strField bh "excessBlobGas")
    blobGasUsed   := hexToNat (strField bh "blobGasUsed") }

/-- EIP-4844/7691 target blob gas per block: 3 blobs at Cancun, 6 from Prague.
    (Osaka's BPO variants retune this; we only validate the excess transition
    on Cancun/Prague, where the constants are fixed, to avoid ever flagging a
    genuinely-valid block.) -/
def targetBlobGas (fork : Fork) : Nat :=
  if fork ≥ .Prague then 6 * Tx.gasPerBlob else 3 * Tx.gasPerBlob

/-- Max blob gas per block: 6 blobs at Cancun, 9 from Prague (EIP-7691). -/
def maxBlobGasPerBlock (fork : Fork) : Nat :=
  if fork ≥ .Prague then 9 * Tx.gasPerBlob else 6 * Tx.gasPerBlob

/-- EIP-4844 `calc_excess_blob_gas(parent)`: carry over the parent's excess
    plus what it used, minus the per-block target (clamped at 0). -/
def calcExcessBlobGas (p : ParentInfo) (fork : Fork) : Nat :=
  let sum := p.excessBlobGas + p.blobGasUsed
  let target := targetBlobGas fork
  if sum < target then 0 else sum - target

/-- Field indices in the RLP block header (post-Cancun layout). -/
def hdrGasLimit : Nat := 9
def hdrBlobGasUsed : Nat := 17
def hdrExcessBlobGas : Nat := 18

/-- Decode a block's `rlp` into its header field list. The block RLP is
    `[header, transactions, uncles, …]`; the header is a list of scalar/‌byte
    fields. Returns `none` if the bytes don't decode to that shape. -/
def decodeBlockHeaderRlp (rlpHex : String) : Option (List Rlp.Item) := do
  let (item, _) ← Rlp.decodeAt (hexToBytes rlpHex) 0
  let top ← item.asList
  (← top[0]?).asList

/-- Independently decide whether a block is invalid *from its `rlp`* by the
    header consensus rules we model, given the parent's header info. Catches:
    RLP-undecodable, gas-limit below the `5000` floor or outside the
    `±parent/1024` adjustment band, blob-gas-used above the per-block max, and
    (Cancun/Prague) an `excessBlobGas` that doesn't match the transition
    formula. Conservative: only returns `true` for genuine violations, so a
    valid block is never flagged. `none` reasons we don't model return `false`
    (the caller falls back to the fixture's `expectException`). -/
def headerConsensusInvalid (fork : Fork) (p : ParentInfo) (rlpHex : String)
    (maxBlobGas : Nat) : Option String :=
  match decodeBlockHeaderRlp rlpHex with
  | none => some "undecodable block rlp"
  | some fields =>
    let get (i : Nat) : Nat := ((fields[i]?).bind Rlp.Item.asNat).getD 0
    let gasLimit := get hdrGasLimit
    -- Gas-limit consensus bounds (fork-independent).
    if gasLimit < 5000 then some "gas limit below 5000"
    else
      let delta := p.gasLimit / 1024
      if gasLimit ≥ p.gasLimit + delta ∨ gasLimit + delta ≤ p.gasLimit then
        some "gas limit outside ±parent/1024"
      -- `maxBlobGas` is the block's fork-specific per-block blob-gas cap
      -- (EIP-7691/7892 BPO schedules retune it; supplied by the caller).
      else if fork ≥ .Cancun ∧ get hdrBlobGasUsed > maxBlobGas then
        some "blob gas used above per-block max"
      -- Excess-blob-gas transition — only on Cancun/Prague (fixed constants).
      else if (fork = .Cancun ∨ fork = .Prague)
              ∧ get hdrExcessBlobGas ≠ calcExcessBlobGas p fork then
        some "incorrect excessBlobGas"
      else none

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

/-- Resolve the active fork for a block at `timestamp`. Handles the EEST
    fork-*transition* networks `<A>To<B>AtTime<N>[k]` (fork `A` before the
    transition timestamp, `B` at/after it) as well as a plain single-fork
    `network`. Returns `none` for networks naming a fork we don't model —
    including the blob-parameter-only (`BPO*`) transitions. -/
def resolveForkAt (network : String) (timestamp : Nat) : Option Fork :=
  match parseForkExact network with
  | some f => some f
  | none =>
    match network.splitOn "AtTime" with
    | [forks, timeStr] =>
      let digits := timeStr.dropEndWhile (· == 'k')
      match digits.toNat? with
      | none   => none
      | some n =>
        let transTime := if timeStr.endsWith "k" then n * 1000 else n
        match forks.splitOn "To" with
        | [a, b] =>
          match parseForkExact a, parseForkExact b with
          | some fa, some fb => some (if timestamp ≥ transTime then fb else fa)
          | _, _ => none
        | _ => none
    | _ => none

/-- The *name* of the fork active at `timestamp` for `network` (the sub-fork of
    an `AToBAtTimeN` transition, else `network` itself). Unlike `resolveForkAt`
    this keeps the EEST fork name — including `BPO*` — so the blob schedule can
    be indexed by it even though `BPO*` maps to `Osaka` semantically. -/
def activeForkName (network : String) (timestamp : Nat) : String :=
  match network.splitOn "AtTime" with
  | [forks, timeStr] =>
    let digits := timeStr.dropEndWhile (· == 'k')
    match digits.toNat? with
    | none   => network
    | some n =>
      let transTime := if timeStr.endsWith "k" then n * 1000 else n
      match forks.splitOn "To" with
      | [a, b] => if timestamp ≥ transTime then b else a
      | _      => network
  | _ => network

/-- EIP-4844/7691/7892 blob-base-fee update fraction for the block at
    `timestamp`. Prefer the fixture's `config.blobSchedule[<forkName>]
    .baseFeeUpdateFraction` (the authoritative per-fork value, and the only
    source for `BPO*` schedules); fall back to the hardcoded protocol defaults
    (`3338477` Cancun, `5007716` Prague+) when the fixture omits it. -/
def blobUpdateFractionAt (config : Json) (network : String) (timestamp : Nat) : Nat :=
  let name    := activeForkName network timestamp
  let sched   := subObj (subObj config "blobSchedule") name
  let fracStr := strField sched "baseFeeUpdateFraction"
  if fracStr ≠ "" then (hexToUInt256 fracStr).toNat
  else match parseForkExact name with
    | some f => if f ≥ .Prague then 5007716 else 3338477
    | none   => 5007716

/-- Per-block max blob gas for the block at `timestamp`, from the fixture's
    `config.blobSchedule[<forkName>].max` (× `GAS_PER_BLOB`); falls back to the
    protocol default (`maxBlobGasPerBlock`) when the fixture omits it. The
    `BPO*` schedules raise this above Osaka's 9-blob cap. -/
def blobMaxGasAt (config : Json) (network : String) (timestamp : Nat) : Nat :=
  let name   := activeForkName network timestamp
  let sched  := subObj (subObj config "blobSchedule") name
  let maxStr := strField sched "max"
  if maxStr ≠ "" then (hexToUInt256 maxStr).toNat * Tx.gasPerBlob
  else match parseForkExact name with
    | some f => maxBlobGasPerBlock f
    | none   => 9 * Tx.gasPerBlob

/-- A block's `timestamp` — from the decoded `blockHeader` when present, else
    from the RLP header (field index 11). `0` if neither decodes. -/
def blockTimestamp (b : Json) : Nat :=
  let bh := subObj b "blockHeader"
  if hasField bh "timestamp" then hexToNat (strField bh "timestamp")
  else match decodeBlockHeaderRlp (strField b "rlp") with
    | some fields => ((fields[11]?).bind Rlp.Item.asNat).getD 0
    | none        => 0

/-- Run one blockchain test: build the genesis pre-state, process the chain,
    and compare the final world against `postState` (tiered) and the last
    applied block's `stateRoot` (root tier).

    The active fork is resolved *per block* from its timestamp
    (`resolveForkAt`), so the EEST fork-transition networks
    (`CancunToPragueAtTime15k`, …) run with the right fork on each side of the
    transition.

    Each block is checked for validity: a block that fails our independent
    header-consensus checks (`headerConsensusInvalid`, decoded from its `rlp`)
    is *rejected* — it does not apply and the chain state stays as before it.
    A block flagged `expectException` in the fixture but invalid for a reason
    we don't model yet is also rejected (fallback), so the final state reflects
    only the valid blocks — exactly what `postState` encodes. -/
def runTest (testObj : Json) : Outcome :=
      let network := strField testObj "network"
      let blocks := (jsonArr (subObj testObj "blocks")).toList
      let preEntries := objEntries testObj "pre"
      let preMap : AccountMap :=
        preEntries.foldl
          (fun σ (addrStr, accJson) => σ.set (hexToAddress addrStr) (mkAccount accJson))
          AccountMap.empty
      -- Fold every block, threading the world state, the parent-header info
      -- (for the consensus transition rules), the last *applied* block's
      -- `stateRoot`, and the last block's fork (for the final root compare). A
      -- rejected block leaves the state / parent / stateRoot unchanged. The
      -- fork is resolved per block from its timestamp.
      -- EIP-2935 / BLOCKHASH: accumulate a number→hash map of processed blocks
      -- (seeded with the genesis header's hash) so the `BLOCKHASH` opcode can
      -- read the real hash of a recent block instead of the old `0` stub.
      let genesisBh := subObj testObj "genesisBlockHeader"
      let genesisHashes : Std.HashMap Nat UInt256 :=
        (∅ : Std.HashMap Nat UInt256).insert
          (hexToNat (strField genesisBh "number")) (hexToUInt256 (strField genesisBh "hash"))
      let rec go (m : AccountMap) (p : ParentInfo) (lastRoot : String)
          (lastFork : Fork) (hashes : Std.HashMap Nat UInt256)
          : List Json → Except String (AccountMap × String × Fork)
        | []      => .ok (m, lastRoot, lastFork)
        | b :: bs =>
          match resolveForkAt network (blockTimestamp b) with
          | none => .error s!"unmodelled fork {network}"
          | some fork =>
            let detected := headerConsensusInvalid fork p (strField b "rlp")
                              (blobMaxGasAt (subObj testObj "config") network (blockTimestamp b))
            let flagged  := hasField b "expectException"
            if detected.isSome ∨ flagged then go m p lastRoot fork hashes bs   -- reject
            else
              let bh := subObj b "blockHeader"
              let curNum := hexToNat (strField bh "number")
              -- BLOCKHASH exposes hashes of the 256 most-recent prior blocks;
              -- 0 for the current/future block or anything older than 256.
              let blockHashFn : UInt256 → UInt256 := fun n =>
                let k := n.toNat
                if k < curNum ∧ k + 256 ≥ curNum then hashes.getD k ⟨0⟩ else ⟨0⟩
              let blobFrac := blobUpdateFractionAt (subObj testObj "config") network
                                (blockTimestamp b)
              match executeBlock m b fork blobFrac blockHashFn with
              | .error r => .error r
              | .ok m'   =>
                let hashes' := hashes.insert curNum (hexToUInt256 (strField bh "hash"))
                go m' (parentInfoOf bh) (strField bh "stateRoot") fork hashes' bs
      let fork0 := (resolveForkAt network 0).getD .Frontier
      match go preMap (parentInfoOf genesisBh) (strField genesisBh "stateRoot")
              fork0 genesisHashes blocks with
      | .error r => .incon r
      | .ok (finalAccounts, lastRootStr, fork) =>
        let isPrecompileAddr (a : AccountAddress) : Bool :=
          decide (1 ≤ a.val) && decide (a.val ≤ 9)
        let wasInPreState : AccountAddress → Bool :=
          fun a => preMap.contains a && ¬ isPrecompileAddr a
        let post := objEntries testObj "postState"
        if post.isEmpty then
          -- Some fixtures give only `postStateHash` (the expected final world
          -- MPT root) instead of an expanded `postState`. Invalid-block
          -- fixtures (`gas_limit_below_minimum`, `invalid_header`, …) instead
          -- carry an empty `postState` *and* no `postStateHash`, encoding
          -- success as `lastblockhash == genesis`: every block is rejected, so
          -- the final world is the genesis world whose root equals the
          -- threaded `lastRootStr` (the last *applied* block's stateRoot, =
          -- genesis when all were rejected). Compare against `postStateHash`
          -- when present, else fall back to `lastRootStr` rather than INCON.
          let phash := strField testObj "postStateHash"
          let expectedRoot := if phash ≠ "" then phash else lastRootStr
          if expectedRoot = "" then .incon "no postState / postStateHash"
          else match AccountMap.stateRoot finalAccounts fork wasInPreState with
            | some r => if r.toNat == (hexToUInt256 expectedRoot).toNat then .passRoot
                        else .fail "postStateHash mismatch"
            | none   => .incon "state root uncomputable"
        else match cmpPost finalAccounts preEntries post false with
        | [] =>
          match cmpPost finalAccounts preEntries post true with
          | [] =>
            -- Root tier: compare our world MPT root to the last *applied*
            -- block's `stateRoot` (the genesis root if none applied).
            let expRoot := hexToUInt256 lastRootStr
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
