module

public import Lean.Data.Json
public import EvmSemantics
public import EvmSemantics.Data.Hex

/-!
`TransactionTestRunner` — JSON driver for the `ethereum/tests`
**TransactionTests** conformance suite.

Unlike the state-test runners, TransactionTests do *not* execute a
transaction. Each fixture supplies one raw RLP-encoded transaction
(`txbytes`) and, per fork, the expected verdict:

* a **valid** transaction lists `sender` (the ECDSA-recovered origin),
  `hash` (`keccak256(txbytes)`), and `intrinsicGas` (`g₀`);
* an **invalid** transaction has an `exception` field and `intrinsicGas`
  of `0x00`.

So the runner's job is: RLP-decode `txbytes` into a typed transaction,
statically validate it, recover the sender, compute the hash and the
intrinsic gas, and check the (valid/invalid, sender, hash, intrinsicGas)
tuple against the fixture — per fork.

Scope: legacy (pre- and post-EIP-155), EIP-2930 (type `0x01`) and
EIP-1559 (type `0x02`) transactions are decoded and validated. Other
typed envelopes (EIP-4844 blob `0x03`, EIP-7702 set-code `0x04`) are
reported `INCON` (skipped, not failed) so they land in the expected-
failures baseline rather than counting as regressions.
-/

@[expose] public section

namespace TransactionTests

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

/-- Whether the fixture object has key `k` at all (present ≠ empty). -/
def hasField (j : Json) (k : String) : Bool := (j.getObjVal? k).toOption.isSome

----------------------------------------------------------------------------
-- Fork parsing (exact match on the fork name used as a `result` key).
----------------------------------------------------------------------------

/-- Map a TransactionTests `result` fork key to a `Fork`. `none` for fork
    names the semantics doesn't model (skipped as `INCON`). -/
def parseFork (s : String) : Option Fork :=
  match s with
  | "Frontier"           => some .Frontier
  | "Homestead"          => some .Homestead
  | "EIP150"             => some .TangerineWhistle
  | "EIP158"             => some .SpuriousDragon
  | "Byzantium"          => some .Byzantium
  | "Constantinople"     => some .Constantinople
  | "ConstantinopleFix"  => some .Petersburg
  | "Istanbul"           => some .Istanbul
  | "Berlin"             => some .Berlin
  | "London"             => some .London
  | "Paris"              => some .Paris
  | "Merge"              => some .Paris
  | "Shanghai"           => some .Shanghai
  | "Cancun"             => some .Cancun
  | "Prague"             => some .Prague
  | "Osaka"              => some .Osaka
  | _                    => none

----------------------------------------------------------------------------
-- Typed transaction record (decode target).
----------------------------------------------------------------------------

/-- The transaction "kind" we decode, keyed by the EIP-2718 type byte. -/
inductive TxKind where
  | legacy
  | eip2930   -- type 0x01
  | eip1559   -- type 0x02
  deriving Repr, DecidableEq, Inhabited

/-- A decoded transaction, in the shape the validity / sender / gas
    computations need. Field presence follows the tx kind; `chainId` is
    `none` for a pre-EIP-155 legacy tx. -/
structure DecodedTx where
  kind        : TxKind
  chainId     : Option Nat
  nonce       : Nat
  gasLimit    : Nat
  /-- Legacy/2930 gasPrice, or (for 1559) the effective `maxFeePerGas`.
      Only its magnitude matters for the `< 2^256` validity checks; the
      intrinsic gas does not depend on it. -/
  gasPrice    : Nat
  /-- 1559 priority fee (`0` for other kinds). -/
  maxPriority : Nat
  /-- `none` for a contract-creating tx (`to` empty). -/
  recipient   : Option AccountAddress
  value       : Nat
  data        : ByteArray
  /-- `to` field byte length as decoded — used to reject non-20-byte
      addresses (`ADDRESS_TOO_SHORT`). -/
  toLen       : Nat
  /-- Number of (address, storageKeys) pairs / storage keys in the access
      list; drives EIP-2930 intrinsic-gas cost. `(0, 0)` for legacy. -/
  accessAddrs : Nat
  accessKeys  : Nat
  /-- Signature components. `yParity` is the normalised recovery id (0/1);
      `vRaw` is the raw legacy `v` (for EIP-155 chain-id extraction). -/
  yParity     : Nat
  vRaw        : Nat
  r           : Nat
  s           : Nat
  deriving Inhabited

----------------------------------------------------------------------------
-- RLP field extraction helpers.
----------------------------------------------------------------------------

/-- A byte-string RLP item is a *canonical* scalar iff it has no leading
    zero byte (the integer `0` is the empty string). Lists are never
    scalars. -/
def isCanonicalScalar : Rlp.Item → Bool
  | .bytes b => b.size == 0 || b[0]! != 0
  | .list _  => false

/-- Read the `i`-th element of a decoded RLP list, or `none` if out of
    range / not a list. -/
def nth (items : List Rlp.Item) (i : Nat) : Option Rlp.Item := items[i]?

/-- Decoded scalar at index `i`, requiring canonical (no-leading-zero)
    form. -/
def scalarAt (items : List Rlp.Item) (i : Nat) : Option Nat := do
  let it ← nth items i
  guard (isCanonicalScalar it)
  it.asNat

/-- Byte string at index `i`. -/
def bytesAt (items : List Rlp.Item) (i : Nat) : Option ByteArray := do
  (← nth items i).asBytes

/-- Parse the `to` field item into `(recipient, byteLen)`: empty → create
    tx (`none`, len 0); a 20-byte string → that address; any other length
    is returned as-is so the caller can reject it. -/
def parseTo (it : Rlp.Item) : Option (Option AccountAddress × Nat) := do
  let b ← it.asBytes
  if b.size == 0 then some (none, 0)
  else some (some (AccountAddress.ofNat (Data.Bytes.bytesToBigEndianNat b)), b.size)

/-- Count `(address, storageKeys)` entries and total storage keys in a
    decoded access list (`[[addr, [k,…]], …]`). Returns `none` if the
    shape is malformed. -/
def parseAccessList (it : Rlp.Item) : Option (Nat × Nat) := do
  let entries ← it.asList
  let mut addrs := 0
  let mut keys := 0
  for e in entries do
    let pair ← e.asList
    -- Each entry is [address (exactly 20 bytes), [storageKey (each 32
    -- bytes), …]]. A wrong-size address or key makes the tx invalid.
    let addr ← (← nth pair 0).asBytes
    guard (addr.size == 20)
    let ks ← (← nth pair 1).asList
    for k in ks do
      let kb ← k.asBytes
      guard (kb.size == 32)
    addrs := addrs + 1
    keys := keys + ks.length
  some (addrs, keys)

----------------------------------------------------------------------------
-- Per-kind RLP decoding.
----------------------------------------------------------------------------

/-- Decode a legacy transaction body `[nonce, gasPrice, gasLimit, to,
    value, data, v, r, s]`. -/
def decodeLegacy (items : List Rlp.Item) : Option DecodedTx := do
  guard (items.length == 9)
  let nonce    ← scalarAt items 0
  let gasPrice ← scalarAt items 1
  let gasLimit ← scalarAt items 2
  let (recip, toLen) ← parseTo (← nth items 3)
  let value    ← scalarAt items 4
  let data     ← bytesAt items 5
  let v        ← scalarAt items 6
  let r        ← scalarAt items 7
  let s        ← scalarAt items 8
  -- EIP-155: v = chainId·2 + 35 + yParity; pre-155: v ∈ {27, 28}.
  let (chainId, yParity) :=
    if v == 27 ∨ v == 28 then (none, v - 27)
    else if v ≥ 35 then (some ((v - 35) / 2), (v - 35) % 2)
    else (none, v)  -- malformed v; recovery will reject
  pure { kind := .legacy, chainId, nonce, gasLimit, gasPrice, maxPriority := 0,
         recipient := recip, value, data, toLen, accessAddrs := 0, accessKeys := 0,
         yParity, vRaw := v, r, s }

/-- Decode an EIP-2930 (type `0x01`) body `[chainId, nonce, gasPrice,
    gasLimit, to, value, data, accessList, yParity, r, s]`. -/
def decode2930 (items : List Rlp.Item) : Option DecodedTx := do
  guard (items.length == 11)
  let chainId  ← scalarAt items 0
  let nonce    ← scalarAt items 1
  let gasPrice ← scalarAt items 2
  let gasLimit ← scalarAt items 3
  let (recip, toLen) ← parseTo (← nth items 4)
  let value    ← scalarAt items 5
  let data     ← bytesAt items 6
  let (addrs, keys) ← parseAccessList (← nth items 7)
  let yParity  ← scalarAt items 8
  let r        ← scalarAt items 9
  let s        ← scalarAt items 10
  pure { kind := .eip2930, chainId := some chainId, nonce, gasLimit, gasPrice,
         maxPriority := 0, recipient := recip, value, data, toLen,
         accessAddrs := addrs, accessKeys := keys, yParity, vRaw := yParity, r, s }

/-- Decode an EIP-1559 (type `0x02`) body `[chainId, nonce,
    maxPriorityFeePerGas, maxFeePerGas, gasLimit, to, value, data,
    accessList, yParity, r, s]`. -/
def decode1559 (items : List Rlp.Item) : Option DecodedTx := do
  guard (items.length == 12)
  let chainId   ← scalarAt items 0
  let nonce     ← scalarAt items 1
  let maxPrio   ← scalarAt items 2
  let maxFee    ← scalarAt items 3
  let gasLimit  ← scalarAt items 4
  let (recip, toLen) ← parseTo (← nth items 5)
  let value     ← scalarAt items 6
  let data      ← bytesAt items 7
  let (addrs, keys) ← parseAccessList (← nth items 8)
  let yParity   ← scalarAt items 9
  let r         ← scalarAt items 10
  let s         ← scalarAt items 11
  pure { kind := .eip1559, chainId := some chainId, nonce, gasLimit,
         gasPrice := maxFee, maxPriority := maxPrio, recipient := recip, value,
         data, toLen, accessAddrs := addrs, accessKeys := keys, yParity,
         vRaw := yParity, r, s }

/-- Decode result: a typed transaction, an out-of-scope typed envelope
    (carrying its EIP-2718 type byte — its verdict is fork-dependent), or a
    malformed encoding (invalid on every fork). -/
inductive DecodeResult where
  | ok          : DecodedTx → DecodeResult
  | unsupported : Nat → DecodeResult  -- typed envelope this runner can't decode
  | bad         : DecodeResult         -- malformed / undecodable ⇒ invalid tx
  deriving Inhabited

/-- Whether the EIP-2718 transaction `type` byte is *activated* at `fork`.
    An envelope whose type is not activated is `TYPE_NOT_SUPPORTED` — invalid
    on that fork regardless of its body. `0x01`/`0x02` are handled directly
    by the decoder; this covers the out-of-scope defined types (`0x03`
    EIP-4844 blob, `0x04` EIP-7702 set-code) and the undefined/reserved range
    (`0x05`–`0x7f`, never activated). -/
def typedTypeActivated (typeByte : Nat) (fork : Fork) : Bool :=
  match typeByte with
  | 0x01 => fork ≥ .Berlin
  | 0x02 => fork ≥ .London
  | 0x03 => fork ≥ .Cancun
  | 0x04 => fork ≥ .Prague
  | _    => false

/-- Decode raw `txbytes` (already hex-decoded) into a `DecodedTx`. A
    leading byte `< 0x80` (in the EIP-2718 envelope range `0x00..0x7f`)
    marks a typed transaction; otherwise it is a legacy RLP list. -/
def decodeTxBytes (raw : ByteArray) : DecodeResult :=
  if raw.size == 0 then .bad
  else
    let first := raw[0]!.toNat
    if first ≥ 0xc0 then
      -- Legacy: the whole thing is an RLP list.
      match Rlp.decode raw with
      | some (.list items) => match decodeLegacy items with
                              | some tx => .ok tx
                              | none    => .bad
      | _                  => .bad
    else if first == 0x01 ∨ first == 0x02 then
      -- EIP-2930 / EIP-1559: strip the type byte, decode the RLP list.
      let body := raw.extract 1 raw.size
      match Rlp.decode body with
      | some (.list items) =>
        let decoded := if first == 0x01 then decode2930 items else decode1559 items
        match decoded with
        | some tx => .ok tx
        | none    => .bad
      | _                  => .bad
    else if first ≥ 0x03 ∧ first ≤ 0x7f then
      -- EIP-4844 (0x03), EIP-7702 (0x04), or a reserved type: out of scope.
      -- Its per-fork verdict is decided in `runFileResults` via
      -- `typedTypeActivated` (invalid where the type isn't activated).
      .unsupported first
    else
      -- Leading byte in 0x80..0xbf: a bare RLP string, not a valid tx.
      .bad

----------------------------------------------------------------------------
-- Signing hash, sender recovery, tx hash.
----------------------------------------------------------------------------

/-- `to` RLP item for a signing preimage: empty string for a create tx,
    else the 20-byte address. -/
def toItemOf (tx : DecodedTx) : Rlp.Item :=
  match tx.recipient with
  | none   => .bytes ByteArray.empty
  | some a => .ofAddress a

/-- Rebuild the access list as RLP items for the typed signing preimage.
    We only tracked counts, not the entries themselves, so we cannot
    reconstruct the exact preimage — instead the caller passes the raw
    decoded access-list item through. -/
def signingHash (tx : DecodedTx) (accessListItem : Rlp.Item) : Option UInt256 := do
  match tx.kind with
  | .legacy =>
    -- Post-EIP-155 preimage appends [chainId, 0, 0]; pre-155 omits them.
    let base : List Rlp.Item :=
      [.ofNat tx.nonce, .ofNat tx.gasPrice, .ofNat tx.gasLimit, toItemOf tx,
       .ofNat tx.value, .ofByteArray tx.data]
    let items :=
      match tx.chainId with
      | some c => base ++ [.ofNat c, .ofNat 0, .ofNat 0]
      | none   => base
    let enc ← Rlp.encodeList items
    pure (EvmSemantics.keccak256 enc)
  | .eip2930 =>
    let enc ← Rlp.encodeList
      [.ofNat (tx.chainId.getD 0), .ofNat tx.nonce, .ofNat tx.gasPrice,
       .ofNat tx.gasLimit, toItemOf tx, .ofNat tx.value, .ofByteArray tx.data,
       accessListItem]
    pure (EvmSemantics.keccak256 ((ByteArray.mk #[0x01]) ++ enc))
  | .eip1559 =>
    let enc ← Rlp.encodeList
      [.ofNat (tx.chainId.getD 0), .ofNat tx.nonce, .ofNat tx.maxPriority,
       .ofNat tx.gasPrice, .ofNat tx.gasLimit, toItemOf tx, .ofNat tx.value,
       .ofByteArray tx.data, accessListItem]
    pure (EvmSemantics.keccak256 ((ByteArray.mk #[0x02]) ++ enc))

/-- Recover the sender from `(yParity, r, s)` and the signing hash.
    `recoverAddress` wants `v ∈ {27, 28}`, so we pass `27 + yParity`. -/
def recoverSender (tx : DecodedTx) (accessListItem : Rlp.Item) :
    Option AccountAddress := do
  let hash ← signingHash tx accessListItem
  let padded32 ← Crypto.Ecrecover.recoverAddress hash.toNat (27 + tx.yParity) tx.r tx.s
  pure (AccountAddress.ofNat
    (Data.Bytes.bytesToBigEndianNat (padded32.extract 12 32)))

/-- The transaction hash is `keccak256` of the full raw encoding
    (including the EIP-2718 type byte for typed transactions). -/
def txHash (raw : ByteArray) : UInt256 := EvmSemantics.keccak256 raw

----------------------------------------------------------------------------
-- Intrinsic gas (with EIP-2930 access-list cost).
----------------------------------------------------------------------------

/-- Intrinsic gas `g₀`, extending `Tx.intrinsicGas` with the EIP-2930
    access-list surcharge (2400 per address + 1900 per storage key), which
    applies to type-`0x01`/`0x02` transactions from Berlin onwards. -/
def intrinsicGasOf (fork : Fork) (tx : DecodedTx) : Nat :=
  let isCreate := tx.recipient.isNone
  let base := Tx.intrinsicGas fork isCreate tx.data
  base + 2400 * tx.accessAddrs + 1900 * tx.accessKeys

----------------------------------------------------------------------------
-- Validity.
----------------------------------------------------------------------------

/-- secp256k1 group order `N` and the EIP-2 low-s bound `N/2`. -/
def secpN : Nat := Crypto.Secp256k1.N

/-- EIP-3860 (Shanghai+) init-code size cap: 2·24576 = 49152 bytes. -/
def maxInitCodeSize : Nat := 49152

/-- Static validity of a decoded transaction at `fork`. Returns `true`
    when the tx should be *accepted* (and thus has a `sender`/`hash`).
    This is a static, execution-free check: field ranges, signature
    bounds, and fork-gated rules (EIP-2 low-s, EIP-2930/1559 availability,
    EIP-3860 init-code cap, EIP-7825 gas cap). Balance/nonce-vs-account
    checks are out of scope (TransactionTests have no pre-state). -/
def isValid (fork : Fork) (tx : DecodedTx) : Bool := Id.run do
  -- Scalar field ranges: all must fit in 256 bits (nonce/gas fit in 64 in
  -- practice, but the fixtures only require `< 2^256`).
  if tx.nonce ≥ 2^256 ∨ tx.gasPrice ≥ 2^256 ∨ tx.value ≥ 2^256 then return false
  -- gasLimit is a 64-bit field; the nonce ceiling is `2^64 - 1` (EIP-2681:
  -- a valid tx must be able to increment its sender's nonce, so a nonce of
  -- `2^64 - 1` is already `NONCE_TOO_BIG`).
  if tx.gasLimit ≥ 2^64 ∨ tx.nonce ≥ 2^64 - 1 then return false
  -- The up-front gas cost `gasLimit · gasPrice` (or `· maxFeePerGas`) must
  -- fit in 256 bits (`GASLIMIT_PRICE_PRODUCT_OVERFLOW`).
  if tx.gasLimit * tx.gasPrice ≥ 2^256 then return false
  -- `to` must be empty (create) or exactly 20 bytes.
  if tx.toLen ≠ 0 ∧ tx.toLen ≠ 20 then return false
  -- Signature component bounds: r, s ∈ [1, N-1].
  if tx.r == 0 ∨ tx.r ≥ secpN ∨ tx.s == 0 ∨ tx.s ≥ secpN then return false
  -- EIP-2 (Homestead+): s must be ≤ N/2.
  if fork ≥ .Homestead ∧ tx.s > secpN / 2 then return false
  -- Legacy v must be a valid recovery id (27/28) or an EIP-155 encoding.
  match tx.kind with
  | .legacy =>
    let v := tx.vRaw
    let okPre155 := v == 27 ∨ v == 28
    let okEip155 := v ≥ 35 ∧ (v - 35) % 2 ≤ 1
    if ¬ (okPre155 ∨ okEip155) then return false
    -- EIP-155 replay protection is available only from Spurious Dragon.
    if v ≥ 35 ∧ fork < .SpuriousDragon then return false
    -- EIP-155: the encoded chain id must be mainnet (`1`); any other
    -- value is a replay-protection mismatch (`INVALID_CHAINID`).
    if let some c := tx.chainId then if c ≠ 1 then return false
  | .eip2930 =>
    if fork < .Berlin then return false
    if tx.yParity > 1 then return false
    if tx.chainId ≠ some 1 then return false
  | .eip1559 =>
    if fork < .London then return false
    if tx.yParity > 1 then return false
    if tx.chainId ≠ some 1 then return false
    -- maxFeePerGas must be ≥ maxPriorityFeePerGas.
    if tx.gasPrice < tx.maxPriority then return false
  -- EIP-3860 (Shanghai+): init-code (create-tx data) size cap.
  if fork ≥ .Shanghai ∧ tx.recipient.isNone ∧ tx.data.size > maxInitCodeSize then
    return false
  -- EIP-7825 (Osaka+): per-tx gas cap 2^24.
  if fork ≥ .Osaka ∧ tx.gasLimit > Tx.maxTransactionGas then return false
  -- Intrinsic gas must not exceed the gas limit.
  if intrinsicGasOf fork tx > tx.gasLimit then return false
  -- EIP-7623 (Prague+): the calldata data floor `21000 + 10·tokens` must
  -- also be affordable (`INTRINSIC_NO_FLOOR_GAS`). `Tx.dataFloorGas` is `0`
  -- before Prague, so this is a no-op on earlier forks.
  if Tx.dataFloorGas fork tx.data > tx.gasLimit then return false
  return true

----------------------------------------------------------------------------
-- Per-(test, fork) evaluation.
----------------------------------------------------------------------------

/-- Outcome of checking one (test, fork) pair. -/
inductive Outcome where
  | pass
  | fail  : String → Outcome
  | incon : String → Outcome
  deriving Inhabited

/-- Format a `UInt256` as a 0x-prefixed lowercase hex string of the given
    byte width (32 for a hash). -/
def hexOfBytes (bs : ByteArray) : String := "0x" ++ bytesToHex bs

/-- Compare our verdict for one fork against the fixture's expected
    `result` object for that fork. `raw` is the decoded txbytes;
    `accessListItem` is the decoded access-list RLP item (empty list for
    legacy) needed to rebuild the typed signing preimage. -/
def checkFork (fork : Fork) (raw : ByteArray) (tx : DecodedTx)
    (accessListItem : Rlp.Item) (expected : Json) : Outcome := Id.run do
  let expectValid := hasField expected "sender" && hasField expected "hash"
  -- A transaction is valid iff it passes the static checks *and* its
  -- signature recovers to a sender (a signature that yields the point at
  -- infinity or otherwise fails ECDSA recovery is `EC_RECOVERY_FAIL`).
  let staticValid := isValid fork tx
  let recovered := if staticValid then recoverSender tx accessListItem else none
  let valid := staticValid && recovered.isSome
  if expectValid ≠ valid then
    return .fail s!"validity mismatch: expected {expectValid}, got {valid}"
  if ¬ valid then
    return .pass  -- both agree it is invalid; sender/hash not checked
  -- Valid: check sender, hash, intrinsicGas.
  let expSender := (strField expected "sender").toLower
  let expHash   := (strField expected "hash").toLower
  let expGas    := hexToNat (strField expected "intrinsicGas")
  match recovered with
  | none => return .fail "sender recovery failed on a valid tx"
  | some s =>
    let gotSender := ("0x" ++ bytesToHex (Rlp.addressBytes s)).toLower
    if strip0x gotSender ≠ strip0x expSender then
      return .fail s!"sender mismatch: got {gotSender}, expected {expSender}"
    let gotHash := (hexOfBytes (Rlp.uint256ToBytes32 (txHash raw))).toLower
    if strip0x gotHash ≠ strip0x expHash then
      return .fail s!"hash mismatch: got {gotHash}, expected {expHash}"
    let gotGas := intrinsicGasOf fork tx
    if gotGas ≠ expGas then
      return .fail s!"intrinsicGas mismatch: got {gotGas}, expected {expGas}"
    return .pass

----------------------------------------------------------------------------
-- Tally, driver, CLI (mirrors GeneralStateTestRunner).
----------------------------------------------------------------------------

structure Tally where
  pass  : Nat := 0
  fail  : Nat := 0
  incon : Nat := 0
  crash : Nat := 0
  deriving Inhabited

def Tally.total (t : Tally) : Nat := t.pass + t.fail + t.incon + t.crash

partial def collectJson (dir : System.FilePath) : IO (Array System.FilePath) := do
  let mut out : Array System.FilePath := #[]
  for ent in (← dir.readDir) do
    let path := ent.path
    if (← path.isDir) then out := out ++ (← collectJson path)
    else if path.toString.endsWith ".json" then out := out.push path
  return out.qsort (fun a b => a.toString < b.toString)

/-- Sanitize a test name into an id-safe token (no spaces/colons). -/
def sanitize (s : String) : String := (s.replace " " "_").replace ":" "_"

/-- Access-list RLP item recovered from the raw bytes for the typed
    signing preimage; empty list for legacy. Recomputed here so the
    signing hash uses the exact decoded entries. -/
def accessListItemOf (raw : ByteArray) (tx : DecodedTx) : Rlp.Item :=
  match tx.kind with
  | .legacy  => .list []
  | _ =>
    match Rlp.decode (raw.extract 1 raw.size) with
    | some (.list items) =>
      -- access list is at index 7 (2930) or 8 (1559).
      let idx := if tx.kind == .eip2930 then 7 else 8
      (items[idx]?).getD (.list [])
    | _ => .list []

/-- Run every fork in one TransactionTests file; one `(tag, id, msg)` per
    (test, fork). -/
def runFileResults (path : System.FilePath) :
    IO (Array (String × String × String)) := do
  let txt ← IO.FS.readFile path
  match Json.parse txt with
  | .error e => return #[("CRASH", path.fileName.getD path.toString, s!"parse: {e}")]
  | .ok j =>
    let tests := match j with | .obj m => m.toArray.toList | _ => []
    let fileTag := ((path.fileName.getD "").replace ".json" "")
    let mut out := #[]
    for (testName, testObj) in tests do
      let txbytes := strField testObj "txbytes"
      let rawTxbytes := if txbytes ≠ "" then txbytes else strField testObj "rlp"
      let raw := hexToBytes rawTxbytes
      let decoded := decodeTxBytes raw
      for (forkName, expected) in objEntries testObj "result" do
        match parseFork forkName with
        | none => pure ()
        | some fork =>
          let id := s!"{fileTag}_{sanitize testName}_{forkName}"
          let r : String × String × String :=
            match decoded with
            | .unsupported tb =>
              -- A typed envelope we don't decode. If its type isn't activated
              -- on this fork it is `TYPE_NOT_SUPPORTED` (invalid), which we can
              -- check; if it *is* activated we can't validate its body ⇒ INCON.
              if typedTypeActivated tb fork then
                ("INCON", id, s!"unsupported typed envelope 0x{tb} (active at fork)")
              else
                let expectValid := hasField expected "sender" && hasField expected "hash"
                if expectValid then ("FAIL", id, s!"type 0x{tb} unexpectedly valid")
                else ("PASS", id, "")
            | .bad =>
              -- Undecodable ⇒ we treat the tx as invalid; that is correct
              -- iff the fixture also marks it invalid for this fork.
              let expectValid := hasField expected "sender" && hasField expected "hash"
              if expectValid then ("FAIL", id, "decode failed on a valid tx")
              else ("PASS", id, "")
            | .ok tx =>
              let ali := accessListItemOf raw tx
              match checkFork fork raw tx ali expected with
              | .pass    => ("PASS", id, "")
              | .fail m  => ("FAIL", id, m)
              | .incon m => ("INCON", id, m)
          out := out.push r
    return out

/-- Run `files` with up to `jobs` tasks in flight. -/
def runFiles (files : Array System.FilePath) (jobs : Nat) (verbose : Bool) :
    IO Tally := do
  let mut t : Tally := {}
  let n := files.size
  if n = 0 then return t
  let workers := Nat.max 1 jobs
  let mut slots : Array (Option (Task (Except IO.Error (Array (String × String × String))))) :=
    Array.replicate workers none
  let mut nextIdx : Nat := 0
  let mut remaining : Nat := n
  let fold : Tally → Except IO.Error (Array (String × String × String)) → IO Tally :=
    fun t r => do
      let mut t := t
      match r with
      | .ok results =>
        for (tag, name, msg) in results do
          match tag with
          | "PASS"  => t := { t with pass := t.pass + 1 }
          | "FAIL"  => t := { t with fail := t.fail + 1 }
                       if verbose then IO.println s!"FAIL {name}: {msg}"
          | "INCON" => t := { t with incon := t.incon + 1 }
                       if verbose then IO.println s!"INCON {name}: {msg}"
          | _       => t := { t with crash := t.crash + 1 }
                       if verbose then IO.println s!"CRASH {name}: {msg}"
      | .error e =>
        t := { t with crash := t.crash + 1 }
        if verbose then IO.println s!"CRASH (task): {e}"
      return t
  for i in [0:workers] do
    if nextIdx < n then
      let task ← IO.asTask (runFileResults files[nextIdx]!) Task.Priority.dedicated
      slots := slots.set! i (some task)
      nextIdx := nextIdx + 1
  while remaining > 0 do
    let mut progress := false
    for i in [0:workers] do
      match slots[i]! with
      | none => pure ()
      | some task =>
        if (← IO.hasFinished task) then
          t ← fold t (← IO.wait task)
          remaining := remaining - 1
          progress := true
          if nextIdx < n then
            let next ← IO.asTask (runFileResults files[nextIdx]!) Task.Priority.dedicated
            slots := slots.set! i (some next)
            nextIdx := nextIdx + 1
          else
            slots := slots.set! i none
    if !progress then IO.sleep 5
  return t

/-- Parse `-j N` out of `args`; returns `(jobs (0 = unset), remaining)`. -/
def parseFlags (args : List String) : Nat × List String := Id.run do
  let rec go : List String → Option Nat → List String → Nat × List String
    | [], j, acc => (j.getD 0, acc.reverse)
    | "-j" :: v :: rest, _, acc => go rest (some v.toNat!) acc
    | x :: rest, j, acc => go rest j (x :: acc)
  go args none []

/-- Entry point: `txtests [-v] [-j N] <dir-or-file>`. -/
def main (args : List String) : IO Unit := do
  let verbose := args.contains "-v"
  let (jobs0, rest) := parseFlags (args.filter (· != "-v"))
  let jobs ← if jobs0 > 0 then pure jobs0 else do
    match (← IO.getEnv "TXTESTS_JOBS") with
    | some s => pure (Nat.max 1 s.toNat!)
    | none   => pure 8
  let root : System.FilePath := rest.headD "."
  let files ← if (← root.isDir) then collectJson root else pure #[root]
  let t ← runFiles files jobs verbose
  IO.println s!"pass={t.pass} fail={t.fail} incon={t.incon} crash={t.crash} (total {t.total})"

end TransactionTests

def main (args : List String) : IO Unit := TransactionTests.main args
