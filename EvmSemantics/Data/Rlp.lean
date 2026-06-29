module

public import EvmSemantics.State.Account

/-!
`EvmSemantics.Rlp` — a full RLP **encoder** (decoder not included).

Yellow Paper §B / EIP-RLP defines the canonical encoding:

* A single byte `< 0x80` encodes as itself.
* A byte string of length `n ≤ 55` encodes as `0x80 + n` prepended.
* A byte string of length `56 ≤ n < 2^64` encodes as
  `0xb7 + |intToBytes n|` followed by the big-endian length and then
  the bytes.
* A list whose concatenated payload has length `n ≤ 55` encodes as
  `0xc0 + n` prepended.
* A list with `56 ≤ n < 2^64` total payload encodes as
  `0xf7 + |intToBytes n|` followed by the big-endian length and then
  the payload.

The length-prefix for the long-string / long-list cases is capped at 8
bytes by the spec (lengths fit in `Nat < 2^64`). The encoder
**panics** if asked to encode a string or list whose payload is `≥
2^64` bytes; in practice every EVM payload (memory, code, returndata)
is bounded by gas-limited block sizes well below this threshold.

This module is encoder-only — decoding would require a parser
plus round-trip / canonical-form proofs and is left to a future
extension when transaction processing / block validation / MPT state
proofs land.
-/

@[expose] public section

namespace EvmSemantics
namespace Rlp

----------------------------------------------------------------------------
-- Byte-level helpers (not RLP-specific).
----------------------------------------------------------------------------

/-- Big-endian byte representation of `n` with leading zeros stripped.
    `intToBytes 0 = ByteArray.empty` — RLP encodes the integer `0` as
    the empty byte string (whose RLP encoding is then the single byte
    `0x80`, via `encodeBytes` below). -/
partial def intToBytes (n : Nat) : ByteArray :=
  if n = 0 then .empty
  else
    let rec
      /-- Inner loop: peel off LSB-first while accumulating into `acc`
          (which is implicitly big-endian when read left-to-right). -/
      collect (k : Nat) (acc : List UInt8) : List UInt8 :=
      if k = 0 then acc
      else collect (k / 256) (UInt8.ofNat (k % 256) :: acc)
    ByteArray.mk (collect n []).toArray

/-- Big-endian *padded* representation of `n` into exactly `width`
    bytes. Used for fixed-width fields like `AccountAddress` (20 bytes)
    and 32-byte hash slots, where RLP wants the leading zeros kept.
    Bits above the `width`-byte window are silently truncated. -/
partial def natToBytesPadded (n width : Nat) : ByteArray := Id.run do
  let mut bs : Array UInt8 := Array.mkEmpty width
  let mut k := n
  let mut le : Array UInt8 := Array.mkEmpty width
  -- Pull off `width` little-endian bytes.
  for _ in [0:width] do
    le := le.push (UInt8.ofNat (k % 256))
    k := k / 256
  -- Reverse into big-endian.
  for i in [0:width] do bs := bs.push le[width - 1 - i]!
  return ByteArray.mk bs

/-- Big-endian 20-byte representation of an `AccountAddress`. The
    result is *always* exactly 20 bytes — leading zero bytes are
    preserved because an address is a fixed-width 20-byte field in
    RLP, not an integer with stripped leading zeros. -/
def addressBytes (addr : AccountAddress) : ByteArray :=
  natToBytesPadded addr.val 20

/-- Big-endian 32-byte representation of a `UInt256`. Used to lay out
    CREATE2's keccak preimage (`0xff || sender || salt(32) ||
    keccak256(initcode)(32)`). Leading zero bytes are preserved. -/
def uint256ToBytes32 (v : UInt256) : ByteArray :=
  natToBytesPadded v.toNat 32

----------------------------------------------------------------------------
-- Primitive byte-array encoders.
----------------------------------------------------------------------------

/-- Build the RLP length prefix for a string-or-list payload of size `n`.
    `tagSmall` is the short-form base byte (`0x80` for strings, `0xc0`
    for lists); `tagLarge` is the long-form base byte (`0xb7` / `0xf7`).

    Panics if `n ≥ 2^64` — the long-form length is encoded in at most
    8 bytes (the prefix byte adds `|lenBytes|` to `tagLarge`, and only
    8 of the 16 slots between `0xb7` and `0xc0` / `0xf7` and `0x100`
    are valid). In practice every EVM payload is bounded well below
    this by gas-limited block sizes, so this case is unreachable. -/
def lengthPrefix (tagSmall tagLarge : UInt8) (n : Nat) : ByteArray :=
  if n ≤ 55 then ByteArray.mk #[tagSmall + UInt8.ofNat n]
  else if n < 2^64 then
    let lenBytes := intToBytes n
    ByteArray.mk #[tagLarge + UInt8.ofNat lenBytes.size] ++ lenBytes
  else panic! s!"Rlp: payload length {n} exceeds 2^64 - 1 (unencodable per spec)"

/-- RLP-encode a byte string. Handles all length cases (single-byte,
    short-prefix, long-prefix). -/
def encodeBytes (bs : ByteArray) : ByteArray :=
  if bs.size = 1 && bs[0]! < 0x80 then bs
  else lengthPrefix 0x80 0xb7 bs.size ++ bs

/-- RLP-encode a list whose items are already individually RLP-encoded
    to `ByteArray`. Lower-level than `encodeList` — use that one with
    typed `Item`s in most cases. -/
def encodeRawList (encodedItems : List ByteArray) : ByteArray :=
  let payload := encodedItems.foldl (· ++ ·) ByteArray.empty
  lengthPrefix 0xc0 0xf7 payload.size ++ payload

----------------------------------------------------------------------------
-- Typed RLP items.
----------------------------------------------------------------------------

/-- An RLP item: either a byte string or a list of items. The encoder
    `Item.encode` is total over this tree (modulo the
    payload-size-< 2^64 invariant inherited from `lengthPrefix`). -/
inductive Item where
  | bytes : ByteArray → Item
  | list  : List Item → Item

namespace Item

/-- Encode a typed RLP item to its canonical byte representation. -/
partial def encode : Item → ByteArray
  | .bytes bs => encodeBytes bs
  | .list xs  => encodeRawList (xs.map encode)

/-- Lift a `Nat` as a stripped big-endian integer (RLP canonical form). -/
def ofNat (n : Nat) : Item := .bytes (intToBytes n)

/-- Lift a `UInt256` as a stripped integer (RLP canonical form). For
    contexts that need the value as a fixed-width 32-byte field
    (e.g. hash preimages), use `ofUInt256Bytes32`. -/
def ofUInt256 (v : UInt256) : Item := .bytes (intToBytes v.toNat)

/-- Lift a `UInt256` as a fixed-width 32-byte field, leading zeros
    preserved. Used inside hash preimages and MPT trie node encodings
    where leading zeros are significant. -/
def ofUInt256Bytes32 (v : UInt256) : Item := .bytes (uint256ToBytes32 v)

/-- Lift an `AccountAddress` as the 20-byte fixed-width string the
    Yellow Paper expects (leading zeros preserved). -/
def ofAddress (addr : AccountAddress) : Item := .bytes (addressBytes addr)

/-- Lift a raw byte array as-is. -/
def ofByteArray (bs : ByteArray) : Item := .bytes bs

/-- Lift a `Bool`: `false` → empty string (RLP `0x80`), `true` →
    single byte `0x01`. -/
def ofBool (b : Bool) : Item :=
  .bytes (if b then ByteArray.mk #[0x01] else ByteArray.empty)

end Item

----------------------------------------------------------------------------
-- Top-level convenience encoders.
----------------------------------------------------------------------------

/-- RLP-encode a `Nat` as a stripped big-endian integer. -/
def encodeNat (n : Nat) : ByteArray := (Item.ofNat n).encode

/-- RLP-encode a `UInt256` as a stripped big-endian integer. -/
def encodeUInt256 (v : UInt256) : ByteArray := (Item.ofUInt256 v).encode

/-- RLP-encode an `AccountAddress` as a 20-byte fixed-width string. -/
def encodeAddress (addr : AccountAddress) : ByteArray := (Item.ofAddress addr).encode

/-- RLP-encode a `Bool`. -/
def encodeBool (b : Bool) : ByteArray := (Item.ofBool b).encode

/-- RLP-encode a heterogeneous list of typed items. -/
def encodeList (items : List Item) : ByteArray := (Item.list items).encode

----------------------------------------------------------------------------
-- Backward-compat aliases for the existing CREATE / CREATE2 callers.
----------------------------------------------------------------------------

/-- RLP-encode a `Nat` (alias for `encodeNat`). -/
def encodeInt (n : Nat) : ByteArray := encodeNat n

/-- RLP-encode the two-element list `[address, nonce]`, as used by
    CREATE's address derivation:
    `keccak256(rlp([sender, sender.nonce]))[12:]`. -/
def encodeAddrNonce (addr : AccountAddress) (nonce : Nat) : ByteArray :=
  encodeList [.ofAddress addr, .ofNat nonce]

end Rlp
end EvmSemantics
