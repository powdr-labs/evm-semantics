module

public import Init.Data.ByteArray

/-!
`EvmSemantics.Crypto.Blake2f` — the BLAKE2b compression function `F`,
used by Ethereum's precompile at address `0x09` (EIP-152, Istanbul).

Unlike the SHA-256 / RIPEMD-160 precompiles, `0x09` does *not* hash a
byte string: it exposes a *single* invocation of BLAKE2b's core round
function `F` on caller-supplied state. The caller passes the round
count, the 8-word chaining state `h`, the 16-word message block `m`,
the 2-word offset counter `t`, and the final-block flag `f`; the
precompile runs `rounds` mixing rounds and returns the updated 8-word
state.

BLAKE2b operates on 64-bit little-endian words (`UInt64`). Layout
mirrors `Sha256`:

* The initialisation vector `IV` (BLAKE2b, = SHA-512's IV).
* The message-permutation schedule `SIGMA` (10 rows; round `i` uses
  row `i mod 10`, per EIP-152).
* The 64-bit right-rotate `rotr64` and the quarter-round `mixG`.
* `compress` — the `F` function over the (`rounds`, `h`, `m`, `t`, `f`)
  inputs, returning the 8-word output state.
* `compressBytes` — the byte-level driver: it parses the 213-byte
  precompile input (little-endian words) into `F`'s arguments, runs
  `compress`, and serialises the 8 output words back to 64
  little-endian bytes.

Correctness is checked against the EIP-152 test vectors (see
`tests/Blake2fTest.lean`); performance is not a goal.
-/

@[expose] public section

namespace EvmSemantics.Crypto.Blake2f

/-- BLAKE2b initialisation vector (`IV[0..7]`, RFC 7693 §2.6): the
    first 64 bits of the fractional parts of the square roots of the
    first eight primes (identical to SHA-512's IV). -/
def IV : Array UInt64 := #[
  0x6a09e667f3bcc908, 0xbb67ae8584caa73b,
  0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
  0x510e527fade682d1, 0x9b05688c2b3e6c1f,
  0x1f83d9abfb41bd6b, 0x5be0cd19137e2179]

/-- BLAKE2b message-word permutation schedule `SIGMA` (RFC 7693 §2.7).
    Ten rows of the 16-element permutation of `{0..15}`. Mixing round
    `i` selects the message words through row `i mod 10` — BLAKE2b's
    full 12-round schedule reuses rows `0` and `1` for rounds 10 and
    11, and EIP-152 generalises this to arbitrary round counts via the
    same modulo-10 rule. -/
def SIGMA : Array (Array Nat) := #[
  #[ 0,  1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15],
  #[14, 10,  4,  8,  9, 15, 13,  6,  1, 12,  0,  2, 11,  7,  5,  3],
  #[11,  8, 12,  0,  5,  2, 15, 13, 10, 14,  3,  6,  7,  1,  9,  4],
  #[ 7,  9,  3,  1, 13, 12, 11, 14,  2,  6,  5, 10,  4,  0, 15,  8],
  #[ 9,  0,  5,  7,  2,  4, 10, 15, 14,  1, 11, 12,  6,  8,  3, 13],
  #[ 2, 12,  6, 10,  0, 11,  8,  3,  4, 13,  7,  5, 15, 14,  1,  9],
  #[12,  5,  1, 15, 14, 13,  4, 10,  0,  7,  6,  3,  9,  2,  8, 11],
  #[13, 11,  7, 14, 12,  1,  3,  9,  5,  0, 15,  4,  8,  6,  2, 10],
  #[ 6, 15, 14,  9, 11,  3,  0,  8, 12,  2, 13,  7,  1,  4, 10,  5],
  #[10,  2,  8,  4,  7,  6,  1,  5, 15, 11,  9, 14,  3, 12, 13,  0]]

/-- Right-rotate a 64-bit word by `n` bits (`0 < n < 64`). -/
@[inline] def rotr64 (x : UInt64) (n : UInt64) : UInt64 :=
  (x >>> n) ||| (x <<< (64 - n))

/-- BLAKE2b quarter-round `G` (RFC 7693 §3.1), operating in place on
    the 16-word work vector `v` at indices `a b c d` with message
    words `x y`. The four rotation amounts `32, 24, 16, 63` are
    BLAKE2b's (BLAKE2s uses `16, 12, 8, 7`). -/
def mixG (v : Array UInt64) (a b c d : Nat) (x y : UInt64) :
    Array UInt64 := Id.run do
  let mut v := v
  v := v.set! a (v[a]! + v[b]! + x)
  v := v.set! d (rotr64 (v[d]! ^^^ v[a]!) 32)
  v := v.set! c (v[c]! + v[d]!)
  v := v.set! b (rotr64 (v[b]! ^^^ v[c]!) 24)
  v := v.set! a (v[a]! + v[b]! + y)
  v := v.set! d (rotr64 (v[d]! ^^^ v[a]!) 16)
  v := v.set! c (v[c]! + v[d]!)
  v := v.set! b (rotr64 (v[b]! ^^^ v[c]!) 63)
  return v

/-- The BLAKE2b compression function `F` (EIP-152 / RFC 7693 §3.2).

    * `rounds` — number of mixing rounds to run (12 for standard
      BLAKE2b; the precompile lets the caller pick any count).
    * `h` — 8-word chaining state.
    * `m` — 16-word message block.
    * `t0`, `t1` — low/high words of the 128-bit offset counter.
    * `f` — final-block flag; when set, `v[14]` is complemented.

    Returns the updated 8-word state `h'[i] = h[i] ⊕ v[i] ⊕ v[i+8]`. -/
def compress (rounds : Nat) (h m : Array UInt64) (t0 t1 : UInt64)
    (f : Bool) : Array UInt64 := Id.run do
  -- Initialise the 16-word work vector: `h` then `IV`.
  let mut v : Array UInt64 := Array.mkEmpty 16
  for i in [0:8] do v := v.push h[i]!
  for i in [0:8] do v := v.push IV[i]!
  -- Mix the offset counter into `v[12..13]`.
  v := v.set! 12 (v[12]! ^^^ t0)
  v := v.set! 13 (v[13]! ^^^ t1)
  -- Final block: invert all bits of `v[14]`.
  if f then v := v.set! 14 (v[14]! ^^^ 0xffffffffffffffff)
  -- `rounds` mixing rounds, each two columns + two diagonals.
  for r in [0:rounds] do
    let s := SIGMA[r % 10]!
    v := mixG v 0 4  8 12 m[s[0]!]!  m[s[1]!]!
    v := mixG v 1 5  9 13 m[s[2]!]!  m[s[3]!]!
    v := mixG v 2 6 10 14 m[s[4]!]!  m[s[5]!]!
    v := mixG v 3 7 11 15 m[s[6]!]!  m[s[7]!]!
    v := mixG v 0 5 10 15 m[s[8]!]!  m[s[9]!]!
    v := mixG v 1 6 11 12 m[s[10]!]! m[s[11]!]!
    v := mixG v 2 7  8 13 m[s[12]!]! m[s[13]!]!
    v := mixG v 3 4  9 14 m[s[14]!]! m[s[15]!]!
  -- Fold the two halves of `v` back into `h`.
  let mut out : Array UInt64 := Array.mkEmpty 8
  for i in [0:8] do out := out.push (h[i]! ^^^ v[i]! ^^^ v[i + 8]!)
  return out

/-- Read 8 bytes from `bs` starting at `off` as a little-endian
    `UInt64`, zero-padding past the end. -/
def readLE64 (bs : ByteArray) (off : Nat) : UInt64 := Id.run do
  let mut w : UInt64 := 0
  for i in [0:8] do
    let b : UInt64 := if _ : off + i < bs.size then bs[off + i].toUInt64 else 0
    w := w ||| (b <<< UInt64.ofNat (8 * i))
  return w

/-- Write a `UInt64` as 8 little-endian bytes appended to `acc`. -/
def writeLE64 (acc : ByteArray) (w : UInt64) : ByteArray := Id.run do
  let mut acc := acc
  for i in [0:8] do
    let shift : UInt64 := UInt64.ofNat (8 * i)
    acc := acc.push ((w >>> shift) &&& 0xff).toUInt8
  return acc

/-- Byte-level driver for the `0x09` precompile. `input` is the
    213-byte precompile payload (the caller has already validated its
    length and the final-flag byte); `rounds` is the pre-parsed round
    count (read big-endian from `input[0..4)` by the caller for gas
    accounting). Parses the little-endian words and returns the
    64-byte little-endian output state.

    Field layout (EIP-152):
    * `[0..4)`   `rounds`  (4-byte big-endian, parsed by the caller)
    * `[4..68)`  `h`       (8 little-endian 64-bit words)
    * `[68..196)` `m`      (16 little-endian 64-bit words)
    * `[196..212)` `t`     (2 little-endian 64-bit words)
    * `[212]`    `f`       (1-byte final-block flag) -/
def compressBytes (input : ByteArray) (rounds : Nat) : ByteArray := Id.run do
  let mut h : Array UInt64 := Array.mkEmpty 8
  for i in [0:8] do h := h.push (readLE64 input (4 + i * 8))
  let mut m : Array UInt64 := Array.mkEmpty 16
  for i in [0:16] do m := m.push (readLE64 input (68 + i * 8))
  let t0 := readLE64 input 196
  let t1 := readLE64 input 204
  let f := input[212]! == 1
  let out := compress rounds h m t0 t1 f
  let mut res : ByteArray := ByteArray.empty
  for i in [0:8] do res := writeLE64 res out[i]!
  return res

end EvmSemantics.Crypto.Blake2f
