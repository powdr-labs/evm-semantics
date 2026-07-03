module

public import Lean.Data.Json
public import EvmSemantics
public import EvmSemantics.Data.Hex

/-!
`BlockchainEngineTestRunner` — JSON driver for the execution-spec-tests
**BlockchainTests (Engine)** (`blockchain_test_engine`) suite.

An engine blockchain test is the same genesis pre-state (`pre`) plus expanded
`postState` as a plain `blockchain_test`, but each block is delivered the way a
consensus client feeds it to an execution client over the Engine API — as an
`engineNewPayload` call rather than as a raw block `rlp`. Each entry of
`engineNewPayloads` is

```
{ params: [executionPayload, [versionedHashes], parentBeaconBlockRoot,
           executionRequests?],
  newPayloadVersion, forkchoiceUpdatedVersion, validationError? }
```

where `executionPayload` carries the block header fields under their
Engine-API camelCase names (`feeRecipient` = coinbase, `blockNumber` = number,
`prevRandao` directly, no `mixHash`/`difficulty`), the block's withdrawals, and
its **transactions as opaque EIP-2718 RLP byte strings** — unlike the plain
`blockchain_test`, whose `transactions` are pre-decoded objects with the
`sender` (and each EIP-7702 authorization `signer`) already recovered.

So the one genuinely new job here, versus the `blockchaintests` runner whose
block-execution core this shares, is decoding each raw transaction: RLP-decode
the EIP-2718 envelope (legacy / EIP-2930 / EIP-1559 / EIP-4844 blob / EIP-7702
set-code), **recover the sender** from its signature, and — for set-code txs —
**recover each authorization's authority** from `keccak(0x05 ‖ rlp([chainId,
address, nonce]))`. The decoded transactions then execute through the same
`Tx.execute` path (threading each block's post-state into the next), followed
by the block-level system calls (EIP-4788 beacon root from `params[2]`,
EIP-2935 block-hash history from `parentHash`, EIP-7002/7251 end-of-block
requests), withdrawals and the (pre-Merge) block reward, and the world is
compared against `postState` in the same three tiers as the other runners
(`passCore ⊂ passFull ⊂ passRoot`).

A payload flagged with `validationError` is one the Engine API must reject
(`newPayload → INVALID`); we *reject* it — it does not apply and the chain
state stays as it was before it — exactly as the `blockchaintests` runner
treats a block flagged `expectException`. A payload naming a fork we don't
model, or carrying a transaction we can't decode, is reported `INCON` (so it
lands in the baseline rather than counting as a failure).

The output format is byte-for-byte identical to the `blockchaintests` runner's,
so the same CI `blockchaintests_{run,summary,check}.sh` scripts drive this suite
(via the `BLOCKCHAINTESTS_BIN` override) against its own expected-failures
baseline.
-/

@[expose] public section

namespace BlockchainEngineTests

open EvmSemantics EvmSemantics.EVM Lean

open EvmSemantics.Hex

----------------------------------------------------------------------------
-- JSON helpers (mirrors the other runners).
----------------------------------------------------------------------------

def strField (j : Json) (k : String) : String := (j.getObjValAs? String k).toOption.getD ""

def subObj (j : Json) (k : String) : Json := (j.getObjVal? k).toOption.getD Json.null

def objEntries (j : Json) (k : String) : List (String × Json) :=
  match subObj j k with
  | .obj m => m.toArray.toList
  | _      => []

def jsonArr (j : Json) : Array Json :=
  match j with | .arr a => a | _ => #[]

def jsonStr : Json → String | .str s => s | _ => ""

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
  -- EIP-7892 blob-parameter-only forks change only the blob-gas schedule, not
  -- EVM opcodes, so they are semantically Osaka for `Tx.execute`/`stepF`.
  | "BPO1" | "BPO2" | "BPO3" | "BPO4" | "BPO5" => some .Osaka
  | _                   => none

/-- Resolve the active fork for a block at `timestamp`, handling the EEST
    fork-*transition* networks `<A>To<B>AtTime<N>[k]` as well as a plain
    single-fork `network`. `none` for a network naming a fork we don't model. -/
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

/-- The *name* of the fork active at `timestamp` for `network` (keeps the EEST
    name — including `BPO*` — so the blob schedule can be indexed by it). -/
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

----------------------------------------------------------------------------
-- Blob base fee (EIP-4844 fake_exponential) + blob update fraction.
----------------------------------------------------------------------------

/-- EIP-4844 `fake_exponential(factor, numerator, denominator)` — the Taylor
    series with factorial denominators (see the `blockchaintests` runner). -/
partial def fakeExponential (factor numerator denominator : Nat) : Nat :=
  let rec go (i output numAccum : Nat) (fuel : Nat) : Nat :=
    if fuel = 0 ∨ numAccum = 0 then output
    else go (i + 1) (output + numAccum) (numAccum * numerator / (denominator * i)) (fuel - 1)
  (go 1 0 (factor * denominator) 100000) / denominator

/-- EIP-4844/7691/7892 blob-base-fee update fraction for the block at
    `timestamp`: prefer `config.blobSchedule[<forkName>].baseFeeUpdateFraction`,
    else the protocol defaults (`3338477` Cancun, `5007716` Prague+). -/
def blobUpdateFractionAt (config : Json) (network : String) (timestamp : Nat) : Nat :=
  let name    := activeForkName network timestamp
  let sched   := subObj (subObj config "blobSchedule") name
  let fracStr := strField sched "baseFeeUpdateFraction"
  if fracStr ≠ "" then (hexToUInt256 fracStr).toNat
  else match parseForkExact name with
    | some f => if f ≥ .Prague then 5007716 else 3338477
    | none   => 5007716

----------------------------------------------------------------------------
-- executionPayload → EVM-env BlockHeader.
----------------------------------------------------------------------------

/-- Decode an `executionPayload` object into the EVM-env `BlockHeader`. The
    field names are the Engine-API camelCase ones: `feeRecipient` is the
    coinbase, `blockNumber` the number, and `prevRandao` is read directly (an
    engine payload is always post-Merge). `blobBaseFee =
    fake_exponential(1, excessBlobGas, blobFrac)`; `blockHash` is the caller's
    number→hash closure (EIP-2935 / BLOCKHASH). -/
def decodeEngineHeader (ep : Json) (blobFrac : Nat)
    (blockHashFn : UInt256 → UInt256 := fun _ => ⟨0⟩) : BlockHeader :=
  let excessStr := strField ep "excessBlobGas"
  let blobBaseFee : UInt256 :=
    if excessStr ≠ "" then UInt256.ofNat (fakeExponential 1 (hexToUInt256 excessStr).toNat blobFrac)
    else ⟨0⟩
  { coinbase      := hexToAddress (strField ep "feeRecipient")
    timestamp     := hexToUInt256 (strField ep "timestamp")
    number        := hexToUInt256 (strField ep "blockNumber")
    prevRandao    := hexToUInt256 (strField ep "prevRandao")
    gasLimit      := hexToUInt256 (strField ep "gasLimit")
    baseFeePerGas := hexToUInt256 (strField ep "baseFeePerGas")
    chainId       := ⟨1⟩
    blobBaseFee   := blobBaseFee
    blockHash     := blockHashFn }

----------------------------------------------------------------------------
-- Raw EIP-2718 transaction decode (+ ECDSA sender / authority recovery).
----------------------------------------------------------------------------

/-- Big-endian `Nat` of an RLP byte-string item (`0` for a list). -/
def itemNat (it : Rlp.Item) : Nat := (it.asNat).getD 0

/-- Parse a `to` RLP item: empty string → contract creation (`none`); a
    (20-byte) string → that address. -/
def parseTo (it : Rlp.Item) : Option AccountAddress :=
  match it.asBytes with
  | some b => if b.size == 0 then none
              else some (AccountAddress.ofNat (Data.Bytes.bytesToBigEndianNat b))
  | none   => none

/-- Parse an EIP-2930 access-list RLP item (`[[addr, [key,…]], …]`) into
    `(address, storageKeys)` pairs; `[]` if malformed. -/
def parseAccessList (it : Rlp.Item) : List (AccountAddress × List UInt256) :=
  match it.asList with
  | none => []
  | some entries => entries.filterMap (fun e => do
      let pair ← e.asList
      let addrB ← (← pair[0]?).asBytes
      let keys ← (← pair[1]?).asList
      let ks := keys.filterMap (fun k => k.asBytes.map
        (fun kb => UInt256.ofNat (Data.Bytes.bytesToBigEndianNat kb)))
      pure (AccountAddress.ofNat (Data.Bytes.bytesToBigEndianNat addrB), ks))

/-- Parse an EIP-4844 `blobVersionedHashes` RLP item into `UInt256`s. -/
def parseBlobHashes (it : Rlp.Item) : Array UInt256 :=
  match it.asList with
  | none => #[]
  | some hs => (hs.filterMap (fun h => h.asBytes.map
      (fun b => UInt256.ofNat (Data.Bytes.bytesToBigEndianNat b)))).toArray

/-- Recover a secp256k1 signer address from a 32-byte message hash and the
    normalised `(yParity, r, s)` signature. `recoverAddress` wants
    `v ∈ {27, 28}`, so we pass `27 + yParity`. -/
def recoverFrom (hash : UInt256) (yParity r s : Nat) : Option AccountAddress := do
  let padded32 ← Crypto.Ecrecover.recoverAddress hash.toNat (27 + yParity) r s
  pure (AccountAddress.ofNat (Data.Bytes.bytesToBigEndianNat (padded32.extract 12 32)))

/-- `keccak256` of an RLP-list encoding, optionally prefixed with an EIP-2718
    type byte (typed txs) — the transaction signing preimage. -/
def preimageHash (typeByte : Option Nat) (coreItems : List Rlp.Item) : Option UInt256 := do
  let enc ← Rlp.encodeList coreItems
  match typeByte with
  | none    => pure (EvmSemantics.keccak256 enc)
  | some tb => pure (EvmSemantics.keccak256 ((ByteArray.mk #[tb.toUInt8]) ++ enc))

/-- Parse an EIP-7702 `authorizationList` RLP item
    (`[[chainId, address, nonce, yParity, r, s], …]`), recovering each entry's
    `authority` from `keccak(0x05 ‖ rlp([chainId, address, nonce]))`. An entry
    whose signature fails to recover contributes `authority = 0` (matches no
    account ⇒ an inert authorization). -/
def parseAuthList (it : Rlp.Item) : List Tx.Authorization :=
  match it.asList with
  | none => []
  | some entries => entries.filterMap (fun e => do
      let tup ← e.asList
      guard (tup.length == 6)
      let chainId := itemNat (← tup[0]?)
      let addrB   ← (← tup[1]?).asBytes
      let nonce   := itemNat (← tup[2]?)
      let yParity := itemNat (← tup[3]?)
      let r       := itemNat (← tup[4]?)
      let s       := itemNat (← tup[5]?)
      -- Authority preimage is 0x05 ‖ rlp([chainId, address, nonce]).
      let authority :=
        match preimageHash (some 0x05) (tup.take 3) with
        | some h => (recoverFrom h yParity r s).getD (AccountAddress.ofNat 0)
        | none   => AccountAddress.ofNat 0
      pure { chainId   := chainId
             address   := AccountAddress.ofNat (Data.Bytes.bytesToBigEndianNat addrB)
             nonce     := nonce
             authority := authority })

/-- A decoded block transaction: the executable `Tx.Transaction` plus its
    EIP-4844 blob versioned hashes (passed alongside to `Tx.execute`). -/
structure BlockTx where
  tx         : Tx.Transaction
  blobHashes : Array UInt256

/-- Effective gas price for the fee-market kinds:
    `min(maxFeePerGas, baseFee + maxPriorityFeePerGas)`. -/
def effectiveGasPrice (maxFee maxPrio baseFee : Nat) : UInt256 :=
  UInt256.ofNat (Nat.min maxFee (baseFee + maxPrio))

/-- Decode a raw EIP-2718 transaction (already hex-decoded) into a `BlockTx`,
    recovering its sender. `baseFee` is the block's base fee (for the
    fee-market effective-price computation). `none` if the bytes don't decode
    to a transaction we execute. -/
def decodeBlockTx (raw : ByteArray) (baseFee : Nat) : Option BlockTx := do
  guard (raw.size > 0)
  let first := raw[0]!.toNat
  if first ≥ 0xc0 then
    -- Legacy: the whole payload is the RLP list [nonce, gasPrice, gasLimit,
    -- to, value, data, v, r, s].
    let items ← (Rlp.decode raw).bind Rlp.Item.asList
    guard (items.length == 9)
    let nonce    := itemNat (← items[0]?)
    let gasPrice := itemNat (← items[1]?)
    let gasLimit := itemNat (← items[2]?)
    let recipient := parseTo (← items[3]?)
    let value    := itemNat (← items[4]?)
    let data     ← (← items[5]?).asBytes
    let v        := itemNat (← items[6]?)
    let r        := itemNat (← items[7]?)
    let s        := itemNat (← items[8]?)
    -- EIP-155: v = chainId·2 + 35 + yParity; pre-155: v ∈ {27, 28}.
    let (chainId, yParity) :=
      if v == 27 ∨ v == 28 then (none, v - 27)
      else if v ≥ 35 then (some ((v - 35) / 2), (v - 35) % 2)
      else (none, v)
    -- Signing preimage: [nonce, gasPrice, gasLimit, to, value, data] and,
    -- post-155, [chainId, 0, 0] appended.
    let core := items.take 6
    let preItems := match chainId with
      | some c => core ++ [.ofNat c, .ofNat 0, .ofNat 0]
      | none   => core
    let hash ← preimageHash none preItems
    let sender ← recoverFrom hash yParity r s
    pure { tx := { sender, recipient, value := UInt256.ofNat value, data,
                   gasLimit, gasPrice := UInt256.ofNat gasPrice,
                   nonce := UInt256.ofNat nonce }
           blobHashes := #[] }
  else if first == 0x01 ∨ first == 0x02 ∨ first == 0x03 ∨ first == 0x04 then
    -- Typed: strip the type byte, decode the body list. For every typed kind
    -- the signing preimage is `type ‖ rlp(body without the trailing
    -- [yParity, r, s])`.
    let body := raw.extract 1 raw.size
    let items ← (Rlp.decode body).bind Rlp.Item.asList
    let n := items.length
    guard (n ≥ 4)
    let yParity := itemNat (← items[n-3]?)
    let r       := itemNat (← items[n-2]?)
    let s       := itemNat (← items[n-1]?)
    let hash ← preimageHash (some first) (items.take (n - 3))
    let sender ← recoverFrom hash yParity r s
    if first == 0x01 then
      -- EIP-2930: [chainId, nonce, gasPrice, gasLimit, to, value, data,
      -- accessList, yParity, r, s].
      guard (n == 11)
      let nonce    := itemNat (← items[1]?)
      let gasPrice := itemNat (← items[2]?)
      let gasLimit := itemNat (← items[3]?)
      let recipient := parseTo (← items[4]?)
      let value    := itemNat (← items[5]?)
      let data     ← (← items[6]?).asBytes
      let accessList := parseAccessList (← items[7]?)
      pure { tx := { sender, recipient, value := UInt256.ofNat value, data,
                     gasLimit, gasPrice := UInt256.ofNat gasPrice,
                     nonce := UInt256.ofNat nonce, accessList }
             blobHashes := #[] }
    else if first == 0x02 then
      -- EIP-1559: [chainId, nonce, maxPrio, maxFee, gasLimit, to, value,
      -- data, accessList, yParity, r, s].
      guard (n == 12)
      let nonce    := itemNat (← items[1]?)
      let maxPrio  := itemNat (← items[2]?)
      let maxFee   := itemNat (← items[3]?)
      let gasLimit := itemNat (← items[4]?)
      let recipient := parseTo (← items[5]?)
      let value    := itemNat (← items[6]?)
      let data     ← (← items[7]?).asBytes
      let accessList := parseAccessList (← items[8]?)
      pure { tx := { sender, recipient, value := UInt256.ofNat value, data,
                     gasLimit, gasPrice := effectiveGasPrice maxFee maxPrio baseFee,
                     nonce := UInt256.ofNat nonce, accessList }
             blobHashes := #[] }
    else if first == 0x03 then
      -- EIP-4844 blob: [chainId, nonce, maxPrio, maxFee, gasLimit, to, value,
      -- data, accessList, maxFeePerBlobGas, blobVersionedHashes, yParity, r, s].
      guard (n == 14)
      let nonce    := itemNat (← items[1]?)
      let maxPrio  := itemNat (← items[2]?)
      let maxFee   := itemNat (← items[3]?)
      let gasLimit := itemNat (← items[4]?)
      let recipient := parseTo (← items[5]?)
      let value    := itemNat (← items[6]?)
      let data     ← (← items[7]?).asBytes
      let accessList := parseAccessList (← items[8]?)
      let maxFeePerBlobGas := itemNat (← items[9]?)
      let blobHashes := parseBlobHashes (← items[10]?)
      pure { tx := { sender, recipient, value := UInt256.ofNat value, data,
                     gasLimit, gasPrice := effectiveGasPrice maxFee maxPrio baseFee,
                     nonce := UInt256.ofNat nonce, accessList,
                     maxFeePerBlobGas := UInt256.ofNat maxFeePerBlobGas }
             blobHashes }
    else
      -- EIP-7702 set-code: [chainId, nonce, maxPrio, maxFee, gasLimit, to,
      -- value, data, accessList, authorizationList, yParity, r, s].
      guard (n == 13)
      let nonce    := itemNat (← items[1]?)
      let maxPrio  := itemNat (← items[2]?)
      let maxFee   := itemNat (← items[3]?)
      let gasLimit := itemNat (← items[4]?)
      let recipient := parseTo (← items[5]?)
      let value    := itemNat (← items[6]?)
      let data     ← (← items[7]?).asBytes
      let accessList := parseAccessList (← items[8]?)
      let authList := parseAuthList (← items[9]?)
      pure { tx := { sender, recipient, value := UInt256.ofNat value, data,
                     gasLimit, gasPrice := effectiveGasPrice maxFee maxPrio baseFee,
                     nonce := UInt256.ofNat nonce, accessList, authList }
             blobHashes := #[] }
  else
    none

----------------------------------------------------------------------------
-- Block-level system calls (shared design with the `blockchaintests` runner).
----------------------------------------------------------------------------

def beaconRootsAddress : AccountAddress :=
  AccountAddress.ofNat 0x000F3df6D732807Ef1319fB7B8bB8522d0Beac02
def historyStorageAddress : AccountAddress :=
  AccountAddress.ofNat 0x0000F90827F1C53a10cb7A02335B175320002935
def withdrawalRequestAddress : AccountAddress :=
  AccountAddress.ofNat 0x00000961Ef480Eb55e80D19ad83579A64c007002
def consolidationRequestAddress : AccountAddress :=
  AccountAddress.ofNat 0x0000BBdDc7CE488642fb579F8B00f3a590007251
def systemAddress : AccountAddress :=
  AccountAddress.ofNat 0xfffffffffffffffffffffffffffffffffffffffe

/-- Execute a block-level *system call*: run `target`'s code with `calldata`
    from `systemAddress`, committing its state writes but with no
    transaction-level accounting. A no-op if the target has no code; a
    reverting/failing system call leaves state unchanged. -/
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
      | .Exception _ => m
      | _            => sf.accountMap
    | .error _ => m

/-- EIP-7002 / EIP-7251 (Prague+) end-of-block request system calls. -/
def applyBlockEndRequests (m : AccountMap) (header : BlockHeader)
    (fork : Fork) : AccountMap :=
  if fork ≥ .Prague then
    let m := systemCall m header fork withdrawalRequestAddress ByteArray.empty
    systemCall m header fork consolidationRequestAddress ByteArray.empty
  else m

/-- Apply an `executionPayload`'s EIP-4895 withdrawals: credit each `address`
    with `amount` Gwei (`amount · 10⁹` wei). -/
def applyWithdrawals (m : AccountMap) (ep : Json) : AccountMap := Id.run do
  let mut m := m
  for w in jsonArr (subObj ep "withdrawals") do
    let addr := hexToAddress (strField w "address")
    let wei  := hexToNat (strField w "amount") * 1000000000
    if wei ≠ 0 then
      let acc := m addr
      m := m.set addr { acc with balance := acc.balance + UInt256.ofNat wei }
  return m

----------------------------------------------------------------------------
-- Engine-payload execution.
----------------------------------------------------------------------------

/-- Execute one `executionPayload` against `preMap`: block-start system calls
    (EIP-4788 beacon root from `parentBeaconRoot`, EIP-2935 block-hash history
    from `parentHash`), then every decoded transaction in order (threading the
    post-state), then the end-of-block request system calls, withdrawals and
    the (pre-Merge) block reward. `.error` for a fuel-exhausted run or an
    undecodable transaction (⇒ `INCON`). -/
def executePayload (preMap : AccountMap) (ep : Json) (parentBeaconRoot : String)
    (fork : Fork) (blobFrac : Nat)
    (blockHashFn : UInt256 → UInt256 := fun _ => ⟨0⟩) :
    Except String AccountMap := do
  let header := decodeEngineHeader ep blobFrac blockHashFn
  let baseFee := header.baseFeePerGas.toNat
  let mut m := preMap
  if fork ≥ .Cancun ∧ parentBeaconRoot ≠ "" then
    m := systemCall m header fork beaconRootsAddress (hexToBytes parentBeaconRoot)
  if fork ≥ .Prague then
    let parentHash := strField ep "parentHash"
    if parentHash ≠ "" then
      m := systemCall m header fork historyStorageAddress (hexToBytes parentHash)
  for txJson in jsonArr (subObj ep "transactions") do
    let raw := hexToBytes (jsonStr txJson)
    match decodeBlockTx raw baseFee with
    | none => throw "undecodable transaction"
    | some { tx, blobHashes } =>
      let fuel := 2 * tx.gasLimit + 100_000
      let result := EvmSemantics.Tx.execute m header tx fork fuel blobHashes (applyReward := false)
      match result.outcome with
      | .fuelExhausted => throw "fuel exhausted"
      | _ => m := result.finalAccounts
  m := applyBlockEndRequests m header fork
  m := applyWithdrawals m ep
  pure (Tx.applyBlockReward m header.coinbase fork)

----------------------------------------------------------------------------
-- Post-state comparison (mirrors the other runners).
----------------------------------------------------------------------------

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

/-- Run one engine blockchain test: build the genesis pre-state, process the
    `engineNewPayloads` chain (rejecting any payload flagged `validationError`),
    and compare the final world against `postState` (tiered) and the last
    applied payload's `stateRoot` (root tier). The active fork is resolved per
    payload from its `timestamp`. -/
def runTest (testObj : Json) : Outcome :=
  let network := strField testObj "network"
  let payloads := (jsonArr (subObj testObj "engineNewPayloads")).toList
  let config := subObj testObj "config"
  let preEntries := objEntries testObj "pre"
  let preMap : AccountMap :=
    preEntries.foldl
      (fun σ (addrStr, accJson) => σ.set (hexToAddress addrStr) (mkAccount accJson))
      AccountMap.empty
  -- Seed the BLOCKHASH number→hash map with the genesis header's hash.
  let genesisBh := subObj testObj "genesisBlockHeader"
  let genesisHashes : Std.HashMap Nat UInt256 :=
    (∅ : Std.HashMap Nat UInt256).insert
      (hexToNat (strField genesisBh "number")) (hexToUInt256 (strField genesisBh "hash"))
  let rec go (m : AccountMap) (lastRoot : String) (lastFork : Fork)
      (hashes : Std.HashMap Nat UInt256)
      : List Json → Except String (AccountMap × String × Fork)
    | []      => .ok (m, lastRoot, lastFork)
    | blk :: bs =>
      -- A payload the Engine API must reject: skip it, chain state unchanged.
      if hasField blk "validationError" then go m lastRoot lastFork hashes bs
      else
        let params := jsonArr (subObj blk "params")
        let ep := (params[0]?).getD Json.null
        let parentBeaconRoot := jsonStr ((params[2]?).getD Json.null)
        let timestamp := hexToNat (strField ep "timestamp")
        match resolveForkAt network timestamp with
        | none => .error s!"unmodelled fork {network}"
        | some fork =>
          let curNum := hexToNat (strField ep "blockNumber")
          -- BLOCKHASH exposes the 256 most-recent prior block hashes.
          let blockHashFn : UInt256 → UInt256 := fun n =>
            let k := n.toNat
            if k < curNum ∧ k + 256 ≥ curNum then hashes.getD k ⟨0⟩ else ⟨0⟩
          let blobFrac := blobUpdateFractionAt config network timestamp
          match executePayload m ep parentBeaconRoot fork blobFrac blockHashFn with
          | .error r => .error r
          | .ok m'   =>
            let hashes' := hashes.insert curNum (hexToUInt256 (strField ep "blockHash"))
            go m' (strField ep "stateRoot") fork hashes' bs
  let fork0 := (resolveForkAt network 0).getD .Frontier
  match go preMap (strField genesisBh "stateRoot") fork0 genesisHashes payloads with
  | .error r => .incon r
  | .ok (finalAccounts, lastRootStr, fork) =>
    let isPrecompileAddr (a : AccountAddress) : Bool :=
      decide (1 ≤ a.val) && decide (a.val ≤ 9)
    let wasInPreState : AccountAddress → Bool :=
      fun a => preMap.contains a && ¬ isPrecompileAddr a
    let post := objEntries testObj "postState"
    if post.isEmpty then
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
        let expRoot := hexToUInt256 lastRootStr
        match AccountMap.stateRoot finalAccounts fork wasInPreState with
        | some ourRoot =>
          if lastRootStr ≠ "" ∧ ourRoot.toNat == expRoot.toNat then .passRoot
          else .passFull
        | none => .passFull
      | _ => .passCore
    | msgs => .fail (String.intercalate "; " (msgs.take 3))

----------------------------------------------------------------------------
-- Tally + file/dir driver (mirrors the `blockchaintests` runner).
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

/-- Entry point: `blockchaintests_engine [-v] [-j N] [--timeout MS] <dir-or-file>`. -/
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

end BlockchainEngineTests

def main (args : List String) : IO Unit := BlockchainEngineTests.main args
