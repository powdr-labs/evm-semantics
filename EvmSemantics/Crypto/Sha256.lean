module

public import Init.Data.ByteArray

/-!
`EvmSemantics.Crypto.Sha256` — a self-contained implementation of the
SHA-256 cryptographic hash (FIPS 180-4), used by Ethereum's precompile
at address `0x02`.

Layout mirrors `Keccak256`:

* Constants `H0` (initial hash) and `K` (64 round constants).
* Bit-level helpers (`rotr32`, `shr32`, byte-endian I/O).
* The round functions `Ch`, `Maj`, `Σ0`, `Σ1`, `σ0`, `σ1`.
* A per-block compression function operating on the (a…h) 8-word state.
* Byte-level driver `sha256Bytes : ByteArray → ByteArray` that handles
  the FIPS padding (`0x80` sentinel, zero pad to 56 mod 64, 8-byte
  big-endian bit-length) and outputs the 32-byte digest.

Performance is not the goal — the implementation is straightforward
functional Lean, correctness against known test vectors is what
matters. If a faster backend is later needed, `@[implemented_by]`
against a native binding is the usual escape hatch (as we do for
Keccak256), but the precompile call rate is low enough in practice
that the pure-Lean version is fine.
-/

@[expose] public section

namespace EvmSemantics.Crypto.Sha256

/-- SHA-256 initial hash values (`H^(0)_0..7`, FIPS 180-4 §5.3.3):
    the first 32 bits of the fractional parts of the square roots of
    the first eight primes. -/
def H0 : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-- SHA-256 round constants (`K[0..63]`, FIPS 180-4 §4.2.2): the first
    32 bits of the fractional parts of the cube roots of the first
    64 primes. -/
def K : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
  0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
  0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
  0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
  0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
  0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
  0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
  0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
  0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- Right-rotate a 32-bit word by `n` bits (`n < 32`). -/
@[inline] def rotr32 (x : UInt32) (n : Nat) : UInt32 :=
  (x >>> UInt32.ofNat n) ||| (x <<< UInt32.ofNat (32 - n))

/-- Logical right shift by `n` bits. -/
@[inline] def shr32 (x : UInt32) (n : Nat) : UInt32 := x >>> UInt32.ofNat n

/-- `Ch(x,y,z) = (x ∧ y) ⊕ (¬x ∧ z)`. -/
@[inline] def Ch (x y z : UInt32) : UInt32 := (x &&& y) ^^^ ((x ^^^ 0xffffffff) &&& z)

/-- `Maj(x,y,z) = (x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z)`. -/
@[inline] def Maj (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- `Σ0(x) = ROTR²(x) ⊕ ROTR¹³(x) ⊕ ROTR²²(x)`. -/
@[inline] def bigSigma0 (x : UInt32) : UInt32 := rotr32 x 2 ^^^ rotr32 x 13 ^^^ rotr32 x 22

/-- `Σ1(x) = ROTR⁶(x) ⊕ ROTR¹¹(x) ⊕ ROTR²⁵(x)`. -/
@[inline] def bigSigma1 (x : UInt32) : UInt32 := rotr32 x 6 ^^^ rotr32 x 11 ^^^ rotr32 x 25

/-- `σ0(x) = ROTR⁷(x) ⊕ ROTR¹⁸(x) ⊕ SHR³(x)`. -/
@[inline] def smallSigma0 (x : UInt32) : UInt32 := rotr32 x 7 ^^^ rotr32 x 18 ^^^ shr32 x 3

/-- `σ1(x) = ROTR¹⁷(x) ⊕ ROTR¹⁹(x) ⊕ SHR¹⁰(x)`. -/
@[inline] def smallSigma1 (x : UInt32) : UInt32 := rotr32 x 17 ^^^ rotr32 x 19 ^^^ shr32 x 10

/-- Read 4 bytes from `bs` starting at `off` as a big-endian `UInt32`,
    zero-padding past the end. -/
def readBE32 (bs : ByteArray) (off : Nat) : UInt32 := Id.run do
  let mut w : UInt32 := 0
  for i in [0:4] do
    let b : UInt32 := if h : off + i < bs.size then bs[off + i].toUInt32 else 0
    w := (w <<< 8) ||| b
  return w

/-- Write a `UInt32` as 4 big-endian bytes appended to `acc`. -/
def writeBE32 (acc : ByteArray) (w : UInt32) : ByteArray := Id.run do
  let mut acc := acc
  for i in [0:4] do
    let shift : UInt32 := UInt32.ofNat (8 * (3 - i))
    acc := acc.push (((w >>> shift) &&& 0xff).toUInt8)
  return acc

/-- Process one 64-byte block, updating the 8-word hash state.
    `blockOff` points at the block's first byte in `bs`. -/
def compressBlock (H : Array UInt32) (bs : ByteArray) (blockOff : Nat) :
    Array UInt32 := Id.run do
  -- Build the 64-word message schedule `W`.
  let mut W : Array UInt32 := Array.replicate 64 0
  for t in [0:16] do
    W := W.set! t (readBE32 bs (blockOff + t * 4))
  for t in [16:64] do
    let w := smallSigma1 W[t - 2]! + W[t - 7]! + smallSigma0 W[t - 15]! + W[t - 16]!
    W := W.set! t w
  -- Working variables initialized from the current hash.
  let mut a := H[0]!
  let mut b := H[1]!
  let mut c := H[2]!
  let mut d := H[3]!
  let mut e := H[4]!
  let mut f := H[5]!
  let mut g := H[6]!
  let mut h := H[7]!
  -- 64 compression rounds.
  for t in [0:64] do
    let T1 := h + bigSigma1 e + Ch e f g + K[t]! + W[t]!
    let T2 := bigSigma0 a + Maj a b c
    h := g; g := f; f := e
    e := d + T1
    d := c; c := b; b := a
    a := T1 + T2
  -- Fold the working state back into the hash.
  return #[H[0]! + a, H[1]! + b, H[2]! + c, H[3]! + d,
           H[4]! + e, H[5]! + f, H[6]! + g, H[7]! + h]

/-- The SHA-256 hash of `bs` as a 32-byte `ByteArray`.

    Padding (FIPS 180-4 §5.1.1): append one `0x80` byte, then zeros
    until the length is 56 mod 64, then the original bit-length as an
    8-byte big-endian integer. -/
def hash (bs : ByteArray) : ByteArray := Id.run do
  let mut H := H0
  -- Absorb every complete 64-byte block from the input.
  let nFull := bs.size / 64
  for blk in [0:nFull] do
    H := compressBlock H bs (blk * 64)
  -- Build the padded final block(s). Between 1 and 2 blocks depending
  -- on how many bytes the sentinel + length leave for zero-padding.
  let remBase := nFull * 64
  let rem := bs.size - remBase
  let mut tail : ByteArray := ByteArray.empty
  for i in [0:rem] do tail := tail.push bs[remBase + i]!
  -- Sentinel bit `1` (0x80 byte).
  tail := tail.push 0x80
  -- Pad zeros until the tail is 56 mod 64.
  while tail.size % 64 ≠ 56 do
    tail := tail.push 0
  -- Append the 64-bit big-endian bit-length (input.size * 8).
  let bitLen : Nat := bs.size * 8
  for i in [0:8] do
    let shift : Nat := 8 * (7 - i)
    tail := tail.push ((bitLen >>> shift) &&& 0xff).toUInt8
  -- Absorb the tail's block(s).
  let tailBlocks := tail.size / 64
  for blk in [0:tailBlocks] do
    H := compressBlock H tail (blk * 64)
  -- Emit the 8 hash words as 32 big-endian bytes.
  let mut out : ByteArray := ByteArray.empty
  for i in [0:8] do
    out := writeBE32 out H[i]!
  return out

end EvmSemantics.Crypto.Sha256
