module

public import EvmSemantics.Data.UInt256
public import EvmSemantics.Data.Bytes

/-!
`EvmSemantics.Crypto.Keccak256` — a minimal, self-contained implementation
of the **original** Keccak-256 hash function (the variant Ethereum uses,
with the original `0x01` padding delimiter rather than NIST FIPS 202
SHA-3's `0x06`).

This file defines:

* the Keccak-f[1600] permutation (state = 25 × 64-bit lanes, 24 rounds
  of θ-ρ-π-χ-ι);
* the sponge `absorb`/`squeeze` driver specialised to Keccak-256 (rate
  1088 bits = 136 bytes, capacity 512 bits, output 256 bits);
* the byte-level driver `keccak256Bytes : ByteArray → ByteArray` that
  takes care of padding and produces the 32-byte digest;
* the runtime realisation `keccak256Impl : ByteArray → UInt256` (big-
  endian packing of the digest), wired via `@[implemented_by]` to the
  opaque `EvmSemantics.keccak256` declared at the bottom — so the
  relational `Step` rules are independent of the hash, while `stepF`
  computes real values.

Performance is not a goal here (the array updates are pure-functional,
not in-place), only correctness against the Ethereum test vectors.
-/

@[expose] public section

namespace EvmSemantics.Crypto.Keccak

/-- Keccak-f[1600] round constants (24 values). -/
def RC : Array UInt64 := #[
  0x0000000000000001, 0x0000000000008082, 0x800000000000808a, 0x8000000080008000,
  0x000000000000808b, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
  0x000000000000008a, 0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
  0x000000008000808b, 0x800000000000008b, 0x8000000000008089, 0x8000000000008003,
  0x8000000000008002, 0x8000000000000080, 0x000000000000800a, 0x800000008000000a,
  0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

/-- ρ rotation offsets (in bits), indexed by `lane = x + 5·y` (`0 ≤ x,y < 5`). -/
def rotOff : Array Nat := #[
   0,  1, 62, 28, 27,
  36, 44,  6, 55, 20,
   3, 10, 43, 25, 39,
  41, 45, 15, 21,  8,
  18,  2, 61, 56, 14]

/-- Left-rotate a 64-bit lane by `n` bit positions (`n < 64`). -/
def rotl64 (x : UInt64) (n : Nat) : UInt64 :=
  if n = 0 then x
  else (x <<< UInt64.ofNat n) ||| (x >>> UInt64.ofNat (64 - n))

/-- One Keccak-f round (θ-ρ-π-χ-ι) on a 25-lane state. -/
def round (A : Array UInt64) (rc : UInt64) : Array UInt64 := Id.run do
  -- θ: column-parity diffusion.
  let mut C : Array UInt64 := Array.replicate 5 0
  for x in [0:5] do
    C := C.set! x (A[x]! ^^^ A[x+5]! ^^^ A[x+10]! ^^^ A[x+15]! ^^^ A[x+20]!)
  let mut D : Array UInt64 := Array.replicate 5 0
  for x in [0:5] do
    D := D.set! x (C[(x + 4) % 5]! ^^^ rotl64 C[(x + 1) % 5]! 1)
  let mut B : Array UInt64 := A
  for x in [0:5] do
    for y in [0:5] do
      B := B.set! (x + 5*y) (B[x + 5*y]! ^^^ D[x]!)
  -- ρ + π combined: B'[π(x,y)] = rotl(B[x,y], ρ[x,y]).
  let mut B' : Array UInt64 := Array.replicate 25 0
  for x in [0:5] do
    for y in [0:5] do
      let src := x + 5*y
      let dst := y + 5 * ((2 * x + 3 * y) % 5)
      B' := B'.set! dst (rotl64 B[src]! rotOff[src]!)
  -- χ: non-linear step (row-wise).
  let mut A' : Array UInt64 := Array.replicate 25 0
  for y in [0:5] do
    for x in [0:5] do
      A' := A'.set! (x + 5*y)
              (B'[x + 5*y]! ^^^
                ((B'[((x + 1) % 5) + 5*y]! ^^^ 0xffffffffffffffff) &&&
                 B'[((x + 2) % 5) + 5*y]!))
  -- ι: XOR round constant into lane (0,0).
  return A'.set! 0 (A'[0]! ^^^ rc)

/-- The Keccak-f[1600] permutation: 24 rounds with the round constants above. -/
def permute (A : Array UInt64) : Array UInt64 := Id.run do
  let mut A := A
  for i in [0:24] do
    A := round A RC[i]!
  return A

/-- Read 8 bytes from `bs` starting at `off` as a little-endian `UInt64`,
    zero-padding past the end. -/
def readLE64 (bs : ByteArray) (off : Nat) : UInt64 := Id.run do
  let mut w : UInt64 := 0
  for i in [0:8] do
    let b : UInt64 := if h : off + i < bs.size then bs[off + i].toUInt64 else 0
    w := w ||| (b <<< UInt64.ofNat (8 * i))
  return w

/-- Write a `UInt64` as 8 little-endian bytes appended to `acc`. -/
def writeLE64 (acc : ByteArray) (w : UInt64) : ByteArray := Id.run do
  let mut acc := acc
  for i in [0:8] do
    acc := acc.push (((w >>> UInt64.ofNat (8 * i)) &&& 0xff).toUInt8)
  return acc

/-- The Keccak-256 hash of `bs` as a 32-byte `ByteArray`, using Ethereum's
    original-Keccak padding delimiter `0x01` (not NIST SHA-3's `0x06`). -/
def hash (bs : ByteArray) : ByteArray := Id.run do
  -- Rate = 1088 bits = 136 bytes; capacity = 512 bits = 64 bytes.
  let rate := 136
  let mut state : Array UInt64 := Array.replicate 25 0
  -- Absorb full blocks.
  let nFull := bs.size / rate
  for blk in [0:nFull] do
    let base := blk * rate
    for j in [0:rate / 8] do
      let lane := readLE64 bs (base + j * 8)
      state := state.set! j (state[j]! ^^^ lane)
    state := permute state
  -- Build the padded final block (always exactly `rate` bytes).
  let remBase := nFull * rate
  let rem := bs.size - remBase
  let mut block : ByteArray := ByteArray.mk (Array.replicate rate 0)
  for i in [0:rem] do
    block := block.set! i bs[remBase + i]!
  -- Keccak `0x01||10*1` padding: 0x01 at the boundary, 0x80 at byte rate-1
  -- (they collapse to 0x81 when only one slot is left).
  block := block.set! rem (block[rem]! ^^^ 0x01)
  block := block.set! (rate - 1) (block[rate - 1]! ^^^ 0x80)
  -- Absorb the padded block.
  for j in [0:rate / 8] do
    let lane := readLE64 block (j * 8)
    state := state.set! j (state[j]! ^^^ lane)
  state := permute state
  -- Squeeze 32 bytes (one rate-portion is enough for the 256-bit output).
  let mut out : ByteArray := ByteArray.empty
  for j in [0:4] do  -- 4 lanes × 8 bytes = 32 bytes
    out := writeLE64 out state[j]!
  return out

end EvmSemantics.Crypto.Keccak

namespace EvmSemantics

/-- Executable realisation of Ethereum's keccak256: original-Keccak hash of
    the input bytes, with the 32-byte digest packed big-endian into a
    `UInt256`. -/
def keccak256Impl (bs : ByteArray) : UInt256 :=
  UInt256.ofNat (Data.Bytes.bytesToBigEndianNat (Crypto.Keccak.hash bs))

/-- The opaque keccak-256 hash function. The relational `Step` rules see
    this only as an arbitrary `ByteArray → UInt256`, so soundness is
    independent of any particular hash; the executable evaluator runs
    `keccak256Impl` thanks to `@[implemented_by]`. -/
@[implemented_by keccak256Impl]
opaque keccak256 : ByteArray → UInt256

end EvmSemantics
