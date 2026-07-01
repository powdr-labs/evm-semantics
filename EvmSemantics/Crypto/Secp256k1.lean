module

public import Init.Data.ByteArray

/-!
`EvmSemantics.Crypto.Secp256k1` — a self-contained implementation of the
secp256k1 elliptic-curve arithmetic Ethereum uses for ECRECOVER (0x01).

secp256k1 is the Weierstrass curve `y² = x³ + 7` (mod `p`) with:

* `p = 2^256 − 2^32 − 977` — the prime field modulus.
* `N = 2^256 − 432420386565659656852420866394968145599` — the group
  order (order of the generator `G`).
* `G = (Gx, Gy)` — the standard base point.

Everything here operates on `Nat`s reduced modulo either `p` (field
arithmetic) or `N` (scalar arithmetic). We keep affine coordinates
(pairs of field elements plus an explicit `Infinity` marker) rather
than Jacobian projective — a factor-of-5 slowdown for point addition,
but ~half the code and no back-and-forth conversion. Performance
target is "seconds, not minutes" for a full `ecrecover` call; the
critical operation (a modular inverse per point addition) uses
Fermat's little theorem via square-and-multiply, which runs in ~256
multiplications.

Not a goal: side-channel resistance, constant-time behaviour. The
runtime realisation is meant for verification, not for signing.
-/

@[expose] public section

namespace EvmSemantics.Crypto.Secp256k1

/-- The secp256k1 field prime `p = 2^256 - 2^32 - 977`. -/
def p : Nat :=
  0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F

/-- The secp256k1 group order `N` (order of `G`). -/
def N : Nat :=
  0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

/-- Generator `x`-coordinate. -/
def Gx : Nat :=
  0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798

/-- Generator `y`-coordinate. -/
def Gy : Nat :=
  0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8

----------------------------------------------------------------------------
-- Modular arithmetic (mod m for a runtime m; we specialise at m = p, N).
----------------------------------------------------------------------------

/-- `a + b mod m`. -/
@[inline] def modAdd (a b m : Nat) : Nat := (a + b) % m

/-- `a - b mod m`; wraps into `[0, m)` via the standard `(a + m − b)` trick. -/
@[inline] def modSub (a b m : Nat) : Nat := (a + (m - b % m)) % m

/-- `a * b mod m`. -/
@[inline] def modMul (a b m : Nat) : Nat := (a * b) % m

/-- Negation `−a mod m`. -/
@[inline] def modNeg (a m : Nat) : Nat := (m - a % m) % m

/-- Square-and-multiply modular exponentiation: `base^e mod m`. -/
partial def modPow (base e m : Nat) : Nat :=
  let rec go (b acc e : Nat) : Nat :=
    if e = 0 then acc
    else
      let acc' := if e % 2 = 1 then (acc * b) % m else acc
      go ((b * b) % m) acc' (e / 2)
  go (base % m) 1 e

/-- Modular inverse via the extended Euclidean algorithm.

    Iterates the standard `(rᵢ, tᵢ)` recurrence, keeping `t` reduced
    into `[0, m)` at every step (so we never leave `Nat`). Roughly
    an order of magnitude faster than the Fermat-via-square-and-multiply
    alternative (`a^(m−2)` — 256 modular multiplications for
    secp256k1's 256-bit `m`) because the number of Euclidean
    reduction steps is `O(log₂ m)` and each step's arithmetic is
    just a division plus one multiply, not a full modular multiply.

    Returns `0` for `a ≡ 0 mod m` (undefined behaviour for callers
    that don't pre-check — for our use `r`, `s` are gated `∈ [1, N−1]`
    and doubling never invokes `modInv 0`). -/
partial def modInv (a m : Nat) : Nat :=
  let rec go (r0 r1 t0 t1 : Nat) : Nat :=
    if r1 = 0 then t0
    else
      let q := r0 / r1
      let qt1 := (q * t1) % m
      let t := if t0 ≥ qt1 then t0 - qt1 else t0 + (m - qt1)
      go r1 (r0 - q * r1) t1 t
  go m (a % m) 0 1

/-- Modular square root when `m ≡ 3 mod 4`: `sqrt(a) = a^((m+1)/4) mod m`.
    Returns *some* square root — the other is `m − result`. The caller
    picks the right one via a parity check.

    Only correct when `a` is a quadratic residue; callers must verify
    by squaring the returned value. -/
@[inline] def modSqrt (a m : Nat) : Nat := modPow a ((m + 1) / 4) m

----------------------------------------------------------------------------
-- Points and curve operations.
----------------------------------------------------------------------------

/-- A point on secp256k1 in affine coordinates, plus a distinguished
    `infinity` (the identity of the group). -/
inductive Point where
  | infinity
  | affine (x y : Nat)
  deriving Inhabited

/-- Double a point (`2P`), returning `infinity` when `P = infinity` or
    when `P.y = 0` (the tangent is vertical). For secp256k1 with
    `a = 0` the doubling formula is
    `λ = 3·x² / (2·y);  x' = λ² − 2·x;  y' = λ·(x − x') − y`. -/
def doublePoint : Point → Point
  | .infinity => .infinity
  | .affine x y =>
    if y = 0 then .infinity
    else
      let lam := modMul (modMul 3 (modMul x x p) p) (modInv (modMul 2 y p) p) p
      let x' := modSub (modMul lam lam p) (modMul 2 x p) p
      let y' := modSub (modMul lam (modSub x x' p) p) y p
      .affine x' y'

/-- Add two affine points. Handles the special cases (identity, opposite
    points, doubling) explicitly rather than via the generic slope
    formula, which would divide by zero. -/
def addPoint : Point → Point → Point
  | .infinity, Q => Q
  | P, .infinity => P
  | .affine x1 y1, .affine x2 y2 =>
    if x1 = x2 then
      if (y1 + y2) % p = 0 then .infinity
      else doublePoint (.affine x1 y1)
    else
      let lam := modMul (modSub y2 y1 p) (modInv (modSub x2 x1 p) p) p
      let x3 := modSub (modSub (modMul lam lam p) x1 p) x2 p
      let y3 := modSub (modMul lam (modSub x1 x3 p) p) y1 p
      .affine x3 y3

/-- Scalar multiplication `k · P` via left-to-right double-and-add.
    Terminates because the loop-count parameter `bits` decreases
    monotonically to 0. -/
def scalarMul (k : Nat) (P : Point) : Point := Id.run do
  let mut R : Point := .infinity
  let mut base : Point := P
  let mut e := k
  while e ≠ 0 do
    if e % 2 = 1 then R := addPoint R base
    base := doublePoint base
    e := e / 2
  return R

/-- The secp256k1 generator point `G`. -/
def G : Point := .affine Gx Gy

/-- Simultaneous double-scalar multiplication `k₁·P + k₂·Q` via
    Shamir's trick: interleave the two scalars' bits so we only pay
    for one doubling chain (~256 doublings) rather than two. Adds are
    picked from a 4-entry precomputed table keyed by the current bit
    of each scalar.

    Correctness follows from the double-and-add invariant applied to
    the pair `(k₁, k₂)` simultaneously: `2·Q + [i-th bit combo]` at
    each iteration builds `k₁·P + k₂·Q` MSB-to-LSB. -/
def scalarMul2 (k1 : Nat) (P1 : Point) (k2 : Nat) (P2 : Point) : Point := Id.run do
  let P1plus2 := addPoint P1 P2
  -- Choose the doubling-chain length as the bit-width of the larger scalar.
  let mut bitlen : Nat := 0
  let mut m := Nat.max k1 k2
  while m ≠ 0 do
    bitlen := bitlen + 1
    m := m / 2
  let mut Q : Point := .infinity
  let mut i := bitlen
  while i ≠ 0 do
    i := i - 1
    Q := doublePoint Q
    let b1 : Bool := (k1 >>> i) &&& 1 = 1
    let b2 : Bool := (k2 >>> i) &&& 1 = 1
    match b1, b2 with
    | false, false => pure ()
    | true,  false => Q := addPoint Q P1
    | false, true  => Q := addPoint Q P2
    | true,  true  => Q := addPoint Q P1plus2
  return Q

/-- Check that `(x, y)` lies on the curve `y² = x³ + 7 mod p`. -/
def onCurve (x y : Nat) : Bool :=
  (modMul y y p) = (modAdd (modMul x (modMul x x p) p) 7 p)

/-- Given an `x`-coordinate and a parity bit `y_odd`, recover the unique
    curve point `(x, y)` with `y mod 2 = y_odd`, or `none` if no such
    point exists (i.e. `x³ + 7` is not a quadratic residue mod `p`).

    secp256k1's prime `p ≡ 3 mod 4`, so we can use the direct
    exponentiation `sqrt(a) = a^((p+1)/4)` for the square root; if the
    resulting `y'` satisfies `y'² = x³ + 7` it's a valid root, otherwise
    `x` is not a valid `x`-coordinate on the curve. -/
def decompress (x : Nat) (yOdd : Bool) : Option Point :=
  let α := modAdd (modMul x (modMul x x p) p) 7 p     -- x³ + 7 mod p
  let β := modSqrt α p
  if modMul β β p ≠ α then none
  else
    let y := if (β % 2 = 1) = yOdd then β else p - β
    some (.affine x y)

end EvmSemantics.Crypto.Secp256k1
