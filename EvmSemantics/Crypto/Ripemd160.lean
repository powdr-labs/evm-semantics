module

public import Init.Data.ByteArray

/-!
`EvmSemantics.Crypto.Ripemd160` — a self-contained implementation of
RIPEMD-160 (Dobbertin/Bosselaers/Preneel 1996), used by Ethereum's
precompile at address `0x03`.

Layout mirrors `Sha256`, with two structural twists that distinguish
RIPEMD-160 from the SHA family:

1. **Two parallel lines.** Each 512-bit block runs through two
   independent five-round chains ("left" and "right") that start from
   the same hash state but use different round-constants, message-word
   selectors, rotation counts, and non-linear `f_j` functions (left
   uses `f₁..f₅` in order 0→4, right uses them in reverse 4→0). The
   two chains' final `(A..E)` and `(A'..E')` states are combined into
   the block's output by a fixed cross-permutation.

2. **Little-endian everywhere.** SHA-256 packs its 32-bit words big-
   endian; RIPEMD-160 packs them little-endian for both message
   parsing and the output digest.

The result is a 160-bit digest, delivered as 20 bytes little-endian.
The precompile at `0x03` zero-pads it to 32 bytes with 12 *leading*
zero bytes (right-justified in the 32-byte return window).

Reference: Bosselaers–Dobbertin–Preneel, "The RIPEMD-160
cryptographic hash function", CryptoBytes 3(2), 1997 §2 / RFC 4634-
like publication.
-/

@[expose] public section

namespace EvmSemantics.Crypto.Ripemd160

/-- Initial hash values (`H[0..4]`), same as MD4/MD5. -/
def H0 : Array UInt32 := #[
  0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0]

/-- Left-line round constants (one per group of 16 rounds, five groups).
    Values are `⌊2^30 · √(2, 3, 5, 7)⌋` and the last is 0 (round 0). -/
def K : Array UInt32 := #[
  0x00000000, 0x5A827999, 0x6ED9EBA1, 0x8F1BBCDC, 0xA953FD4E]

/-- Right-line round constants: `⌊2^30 · ∛(2, 3, 5, 7)⌋` then 0. -/
def KP : Array UInt32 := #[
  0x50A28BE6, 0x5C4DD124, 0x6D703EF3, 0x7A6D76E9, 0x00000000]

/-- Left-line message-word selectors `r[0..79]` (per RIPEMD-160 spec). -/
def r : Array Nat := #[
   0,  1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15,
   7,  4, 13,  1, 10,  6, 15,  3, 12,  0,  9,  5,  2, 14, 11,  8,
   3, 10, 14,  4,  9, 15,  8,  1,  2,  7,  0,  6, 13, 11,  5, 12,
   1,  9, 11, 10,  0,  8, 12,  4, 13,  3,  7, 15, 14,  5,  6,  2,
   4,  0,  5,  9,  7, 12,  2, 10, 14,  1,  3,  8, 11,  6, 15, 13]

/-- Right-line message-word selectors `r'[0..79]`. -/
def rP : Array Nat := #[
   5, 14,  7,  0,  9,  2, 11,  4, 13,  6, 15,  8,  1, 10,  3, 12,
   6, 11,  3,  7,  0, 13,  5, 10, 14, 15,  8, 12,  4,  9,  1,  2,
  15,  5,  1,  3,  7, 14,  6,  9, 11,  8, 12,  2, 10,  0,  4, 13,
   8,  6,  4,  1,  3, 11, 15,  0,  5, 12,  2, 13,  9,  7, 10, 14,
  12, 15, 10,  4,  1,  5,  8,  7,  6,  2, 13, 14,  0,  3,  9, 11]

/-- Left-line rotation counts `s[0..79]`. -/
def s : Array Nat := #[
  11, 14, 15, 12,  5,  8,  7,  9, 11, 13, 14, 15,  6,  7,  9,  8,
   7,  6,  8, 13, 11,  9,  7, 15,  7, 12, 15,  9, 11,  7, 13, 12,
  11, 13,  6,  7, 14,  9, 13, 15, 14,  8, 13,  6,  5, 12,  7,  5,
  11, 12, 14, 15, 14, 15,  9,  8,  9, 14,  5,  6,  8,  6,  5, 12,
   9, 15,  5, 11,  6,  8, 13, 12,  5, 12, 13, 14, 11,  8,  5,  6]

/-- Right-line rotation counts `s'[0..79]`. -/
def sP : Array Nat := #[
   8,  9,  9, 11, 13, 15, 15,  5,  7,  7,  8, 11, 14, 14, 12,  6,
   9, 13, 15,  7, 12,  8,  9, 11,  7,  7, 12,  7,  6, 15, 13, 11,
   9,  7, 15, 11,  8,  6,  6, 14, 12, 13,  5, 14, 13, 13,  7,  5,
  15,  5,  8, 11, 14, 14,  6, 14,  6,  9, 12,  9, 12,  5, 15,  8,
   8,  5, 12,  9, 12,  5, 14,  6,  8, 13,  6,  5, 15, 13, 11, 11]

/-- Left-rotate a 32-bit word by `n` bits (`n < 32`). -/
@[inline] def rotl32 (x : UInt32) (n : Nat) : UInt32 :=
  (x <<< UInt32.ofNat n) ||| (x >>> UInt32.ofNat (32 - n))

/-- One-bit complement of a 32-bit word (`¬x` in bitwise Prop-land). -/
@[inline] def bnot32 (x : UInt32) : UInt32 := x ^^^ 0xFFFFFFFF

/-- The five non-linear round functions, selected by round-group `j ∈ [0,5)`.
    Left line runs `f 0..4` in order; right line runs `f 4..0` (reverse). -/
@[inline] def f (j : Nat) (x y z : UInt32) : UInt32 :=
  match j with
  | 0 => x ^^^ y ^^^ z
  | 1 => (x &&& y) ||| (bnot32 x &&& z)
  | 2 => (x ||| bnot32 y) ^^^ z
  | 3 => (x &&& z) ||| (y &&& bnot32 z)
  | _ => x ^^^ (y ||| bnot32 z)

/-- Read 4 bytes from `bs` at `off` as a little-endian `UInt32`,
    zero-padding past the end. -/
def readLE32 (bs : ByteArray) (off : Nat) : UInt32 := Id.run do
  let mut w : UInt32 := 0
  for i in [0:4] do
    let b : UInt32 := if h : off + i < bs.size then bs[off + i].toUInt32 else 0
    w := w ||| (b <<< UInt32.ofNat (8 * i))
  return w

/-- Write a `UInt32` as 4 little-endian bytes appended to `acc`. -/
def writeLE32 (acc : ByteArray) (w : UInt32) : ByteArray := Id.run do
  let mut acc := acc
  for i in [0:4] do
    acc := acc.push (((w >>> UInt32.ofNat (8 * i)) &&& 0xff).toUInt8)
  return acc

/-- Process one 64-byte block, updating the 5-word hash state.
    Runs the two parallel round chains and combines their final
    working states with the incoming `H` via the RIPEMD-160
    cross-permutation. -/
def compressBlock (H : Array UInt32) (bs : ByteArray) (blockOff : Nat) :
    Array UInt32 := Id.run do
  -- 16 little-endian words of the block form the message array X.
  let mut X : Array UInt32 := Array.replicate 16 0
  for t in [0:16] do
    X := X.set! t (readLE32 bs (blockOff + t * 4))
  -- Left line: 80 rounds, five function-groups.
  let mut a := H[0]!; let mut b := H[1]!; let mut c := H[2]!
  let mut d := H[3]!; let mut e := H[4]!
  for i in [0:80] do
    let j := i / 16
    let t := a + f j b c d + X[r[i]!]! + K[j]!
    let t := rotl32 t s[i]! + e
    a := e; e := d; d := rotl32 c 10; c := b; b := t
  -- Right line: 80 rounds with reversed function order (j' = 4 - j).
  let mut aP := H[0]!; let mut bP := H[1]!; let mut cP := H[2]!
  let mut dP := H[3]!; let mut eP := H[4]!
  for i in [0:80] do
    let j := i / 16
    let jP := 4 - j
    let t := aP + f jP bP cP dP + X[rP[i]!]! + KP[j]!
    let t := rotl32 t sP[i]! + eP
    aP := eP; eP := dP; dP := rotl32 cP 10; cP := bP; bP := t
  -- RIPEMD-160 cross-permutation combining the two lines with the
  -- incoming state. Each new h_i mixes h_{i+1}, one left-line
  -- working var, and one right-line working var (with a shift by
  -- one position between them).
  return #[
    H[1]! + c + dP,
    H[2]! + d + eP,
    H[3]! + e + aP,
    H[4]! + a + bP,
    H[0]! + b + cP]

/-- The RIPEMD-160 hash of `bs` as a 20-byte little-endian `ByteArray`.

    Padding follows the MD4/RIPEMD convention: append one `0x80` byte,
    then zero bytes until the running length is 56 mod 64, then the
    64-bit *little-endian* bit-length of the original input. -/
def hash (bs : ByteArray) : ByteArray := Id.run do
  let mut H := H0
  -- Absorb every complete 64-byte block from the input.
  let nFull := bs.size / 64
  for blk in [0:nFull] do
    H := compressBlock H bs (blk * 64)
  -- Assemble the padded tail.
  let remBase := nFull * 64
  let rem := bs.size - remBase
  let mut tail : ByteArray := ByteArray.empty
  for i in [0:rem] do tail := tail.push bs[remBase + i]!
  tail := tail.push 0x80
  while tail.size % 64 ≠ 56 do
    tail := tail.push 0
  -- 64-bit little-endian bit-length (input.size * 8).
  let bitLen : Nat := bs.size * 8
  for i in [0:8] do
    let shift : Nat := 8 * i
    tail := tail.push ((bitLen >>> shift) &&& 0xff).toUInt8
  -- Absorb the tail's one or two blocks.
  let tailBlocks := tail.size / 64
  for blk in [0:tailBlocks] do
    H := compressBlock H tail (blk * 64)
  -- Emit the 5 hash words as 20 little-endian bytes.
  let mut out : ByteArray := ByteArray.empty
  for i in [0:5] do
    out := writeLE32 out H[i]!
  return out

end EvmSemantics.Crypto.Ripemd160
