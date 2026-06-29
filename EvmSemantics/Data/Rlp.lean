module

public import EvmSemantics.State.Account

/-!
`EvmSemantics.Rlp` — a minimal RLP encoder sufficient for CREATE's
address derivation: `keccak256(rlp([sender, sender.nonce]))[12:]`. We
encode exactly the shape we need (a list of two items: a 20-byte
address and a `Nat`-valued nonce), so the encoder is closed-form and
doesn't need to handle the long-string / long-list path.

Encoding rules (Yellow Paper §B / EIP-RLP):
* A single byte `< 0x80` encodes as itself.
* A byte string of length `n ≤ 55` encodes as `0x80 + n` prepended.
* A list whose concatenated payload has length `n ≤ 55` encodes as
  `0xc0 + n` prepended.
* The `> 55` cases (length-of-length prefixes `0xb7+ℓ` / `0xf7+ℓ`) are
  not reachable here: a `[20-byte address, ≤8-byte nonce]` payload
  tops out at 30 bytes.
-/

@[expose] public section

namespace EvmSemantics
namespace Rlp

/-- Big-endian byte representation of `n` with leading zeros stripped.
    `intToBytes 0 = ByteArray.empty` — RLP encodes the integer `0` as
    the empty byte string (whose RLP encoding is then the single byte
    `0x80`, via `encodeBytes` below). -/
partial def intToBytes (n : Nat) : ByteArray :=
  if n = 0 then .empty
  else
    -- Build the byte list little-endian by repeated `n / 256`, then
    -- reverse into big-endian.
    let rec collect (k : Nat) (acc : List UInt8) : List UInt8 :=
      if k = 0 then acc
      else collect (k / 256) (UInt8.ofNat (k % 256) :: acc)
    ByteArray.mk (collect n []).toArray

/-- Big-endian 20-byte representation of an `AccountAddress`. Unlike
    `intToBytes`, the result is *always* exactly 20 bytes — leading
    zero bytes are preserved, because an address is a fixed-width
    20-byte field in RLP, not an integer with stripped leading zeros. -/
partial def addressBytes (addr : AccountAddress) : ByteArray := Id.run do
  let mut bs : Array UInt8 := Array.mkEmpty 20
  let mut k := addr.val
  let mut le : Array UInt8 := Array.mkEmpty 20
  -- Pull off 20 little-endian bytes.
  for _ in [0:20] do
    le := le.push (UInt8.ofNat (k % 256))
    k := k / 256
  -- Reverse into big-endian.
  for i in [0:20] do bs := bs.push le[19 - i]!
  return ByteArray.mk bs

/-- RLP-encode a byte string. Handles all length cases:
    * single-byte values `< 0x80` are emitted bare;
    * lengths `0..55` use the short prefix `0x80 + n`;
    * lengths `56+` use the long prefix `0xb7 + |lenBytes|` followed by
      the big-endian length and then the bytes. -/
def encodeBytes (bs : ByteArray) : ByteArray :=
  if bs.size = 1 && bs[0]! < 0x80 then bs
  else if bs.size ≤ 55 then
    ByteArray.mk #[UInt8.ofNat (0x80 + bs.size)] ++ bs
  else
    let lenBytes := intToBytes bs.size
    ByteArray.mk #[UInt8.ofNat (0xb7 + lenBytes.size)] ++ lenBytes ++ bs

/-- RLP-encode a list whose items are already individually RLP-encoded.
    Short payloads (`≤ 55` total) use the `0xc0 + len` prefix; longer
    payloads use the `0xf7 + |lenBytes|` long-list prefix. -/
def encodeList (items : List ByteArray) : ByteArray :=
  let payload := items.foldl (· ++ ·) ByteArray.empty
  if payload.size ≤ 55 then
    ByteArray.mk #[UInt8.ofNat (0xc0 + payload.size)] ++ payload
  else
    let lenBytes := intToBytes payload.size
    ByteArray.mk #[UInt8.ofNat (0xf7 + lenBytes.size)] ++ lenBytes ++ payload

/-- RLP-encode a `Nat` as a stripped big-endian integer. `0` becomes
    `#[0x80]` (the empty-string encoding), `n < 0x80` becomes the
    single byte `n`, otherwise short-string-prefixed bytes. -/
def encodeInt (n : Nat) : ByteArray := encodeBytes (intToBytes n)

/-- RLP-encode an `AccountAddress` as a 20-byte fixed-width string. -/
def encodeAddress (addr : AccountAddress) : ByteArray :=
  encodeBytes (addressBytes addr)

/-- Big-endian 32-byte representation of a `UInt256`. Used to lay out
    CREATE2's keccak preimage (`0xff || sender || salt(32) ||
    keccak256(initcode)(32)`). Leading zero bytes are preserved. -/
partial def uint256ToBytes32 (v : UInt256) : ByteArray := Id.run do
  let mut bs : Array UInt8 := Array.mkEmpty 32
  let mut le : Array UInt8 := Array.mkEmpty 32
  let mut k := v.toNat
  for _ in [0:32] do
    le := le.push (UInt8.ofNat (k % 256))
    k := k / 256
  for i in [0:32] do bs := bs.push le[31 - i]!
  return ByteArray.mk bs

/-- RLP-encode the two-element list `[address, nonce]`. -/
def encodeAddrNonce (addr : AccountAddress) (nonce : Nat) : ByteArray :=
  encodeList [encodeAddress addr, encodeInt nonce]

end Rlp
end EvmSemantics
