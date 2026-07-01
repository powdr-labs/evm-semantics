module

public import Init.Data.ByteArray

/-!
`EvmSemantics.Data.Bytes` — bytes ↔ `Nat` conversion helpers shared
across the codebase.

The counterpart family — `Nat` → `ByteArray` (padded / stripped) —
lives in `EvmSemantics.Data.Rlp` as `natToBytesPadded` /
`intToBytes`. This module hosts the inverse direction, plus any
additional byte utilities that are broadly useful without pulling
in RLP's `State.Account` dependency.
-/

@[expose] public section

namespace EvmSemantics.Data.Bytes

/-- Decode a big-endian `ByteArray` as a `Nat`. The empty byte array
    encodes `0`. Inverse of `natToBytesPadded` (modulo the
    leading-zero convention: `bytesToBigEndianNat` ignores the
    number of leading zero bytes; the padded encoding fixes the
    width). Used by `MLOAD`, `CALLDATALOAD`, the MODEXP precompile
    input parser, the keccak-256 result packer, the bytecode
    decoder's `PUSHN` immediate reader, and the MPT trie
    intermediary. -/
def bytesToBigEndianNat (bs : ByteArray) : Nat :=
  bs.toList.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- Inner loop of `intToBytes`: peel off LSB-first into `acc` (which
    is implicitly big-endian when read left-to-right). Terminates
    because `k / 256 < k` whenever `k ≠ 0`. -/
def intToBytesAux (k : Nat) (acc : List UInt8) : List UInt8 :=
  if h : k = 0 then acc
  else intToBytesAux (k / 256) (UInt8.ofNat (k % 256) :: acc)
termination_by k
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

/-- Big-endian byte representation of `n` with leading zeros stripped.
    `intToBytes 0 = ByteArray.empty`. RLP's length prefix and the
    integer encoder use this shape. -/
def intToBytes (n : Nat) : ByteArray := ByteArray.mk (intToBytesAux n []).toArray

/-- Big-endian *padded* representation of `n` into exactly `width`
    bytes. Used for fixed-width fields like an `AccountAddress`
    (20 bytes) and 32-byte hash slots, where RLP / trie encoders
    want the leading zeros kept. Bits above the `width`-byte
    window are silently truncated. -/
def natToBytesPadded (n width : Nat) : ByteArray := Id.run do
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

end EvmSemantics.Data.Bytes
