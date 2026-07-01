module

public import Init.Data.ByteArray

/-!
`EvmSemantics.Crypto.EC` — shared modular arithmetic and Weierstrass
curve operations, parameterised by a `Curve` record.

Ethereum uses two short-Weierstrass curves with the `a = 0` shape
`y² = x³ + b` (mod `p`):

* **secp256k1** (`b = 7`, `p ≈ 2^256`) — for ECRECOVER (0x01).
* **alt_bn128 / BN254** (`b = 3`, `p ≈ 2^254`) — for ECADD (0x06),
  ECMUL (0x07), and ECPAIRING (0x08).

Both live in the same family, so this file provides *curve-generic*
point arithmetic; each specific curve then narrows down to constants
in its own module (`Secp256k1.lean`, `Bn254.lean`).

Design choices:

* **Affine coordinates** with an explicit `infinity` marker. A
  factor-of-5 slowdown for point addition vs. Jacobian projective,
  but half the code and no back-and-forth conversion. Performance
  target is "seconds, not minutes" per precompile call.
* **`Nat` field elements** — Lean's `Nat` is GMP-backed and handles
  256-bit inputs without effort. No fixed-width big-int type.
* **Explicit modulus argument** on `modAdd` / `modSub` / `modMul` /
  etc. — the same helpers are reused for both field arithmetic
  (`mod p`) and scalar arithmetic (`mod N`).

Not a goal: side-channel resistance, constant-time behaviour. The
runtime realisation is meant for verification, not for signing.
-/

@[expose] public section

namespace EvmSemantics.Crypto.EC

----------------------------------------------------------------------------
-- Modular arithmetic (`m` supplied at call site — used with the
-- field modulus `p` for point ops, and with the group order `N`
-- for scalar ops).
----------------------------------------------------------------------------

/-- `a + b mod m`. -/
@[inline] def modAdd (a b m : Nat) : Nat := (a + b) % m

/-- `a - b mod m`; wraps into `[0, m)` via the standard `(a + m − b)` trick. -/
@[inline] def modSub (a b m : Nat) : Nat := (a + (m - b % m)) % m

/-- `a * b mod m`. -/
@[inline] def modMul (a b m : Nat) : Nat := (a * b) % m

/-- Negation `−a mod m`. -/
@[inline] def modNeg (a m : Nat) : Nat := (m - a % m) % m

/-- Inner square-and-multiply loop for `modPow`: `acc · b^e mod m`,
    with the base repeatedly squared and the exponent halved. -/
partial def modPow.go (m b acc e : Nat) : Nat :=
  if e = 0 then acc
  else
    let acc' := if e % 2 = 1 then (acc * b) % m else acc
    modPow.go m ((b * b) % m) acc' (e / 2)

/-- Square-and-multiply modular exponentiation: `base^e mod m`. -/
def modPow (base e m : Nat) : Nat := modPow.go m (base % m) 1 e

/-- Inner extended-Euclidean loop for `modInv`: keeps the standard
    `(rᵢ, tᵢ)` recurrence, reducing `t` into `[0, m)` at every step so
    all intermediate values stay in `Nat`. Terminates when `r₁ = 0`;
    the surviving `t₀` is the modular inverse of the original input. -/
partial def modInv.go (m r0 r1 t0 t1 : Nat) : Nat :=
  if r1 = 0 then t0
  else
    let q := r0 / r1
    let qt1 := (q * t1) % m
    let t := if t0 ≥ qt1 then t0 - qt1 else t0 + (m - qt1)
    modInv.go m r1 (r0 - q * r1) t1 t

/-- Modular inverse via the extended Euclidean algorithm.

    Roughly an order of magnitude faster than the Fermat-via-square-
    and-multiply alternative (`a^(m−2)` — 256 modular multiplications
    for a 256-bit `m`) because the number of Euclidean reduction
    steps is `O(log₂ m)` and each step's arithmetic is just a
    division plus one multiply, not a full modular multiply.

    Returns `0` for `a ≡ 0 mod m` (undefined behaviour for callers
    that don't pre-check — for our uses `r`, `s` are gated `∈ [1, N−1]`
    and doubling never invokes `modInv 0`). -/
def modInv (a m : Nat) : Nat := modInv.go m m (a % m) 0 1

/-- Modular square root when `m ≡ 3 mod 4`: `sqrt(a) = a^((m+1)/4) mod m`.
    Returns *some* square root — the other is `m − result`. The caller
    picks the right one via a parity check and by squaring the result
    to verify it's a quadratic residue.

    Both secp256k1 and alt_bn128 have primes `p ≡ 3 mod 4`, so this
    is the natural square-root routine for their `decompress`. -/
@[inline] def modSqrt (a m : Nat) : Nat := modPow a ((m + 1) / 4) m

----------------------------------------------------------------------------
-- Curve parameters.
----------------------------------------------------------------------------

/-- A short-Weierstrass curve `y² = x³ + b` over `F_p` (i.e. `a = 0`).
    Sufficient for the two curves Ethereum uses at precompile scope. -/
structure Curve where
  /-- Field modulus `p`. Both our curves have `p ≡ 3 mod 4`, so
      `modSqrt` is well-defined for `decompress`. -/
  p : Nat
  /-- Coefficient `b` in the curve equation `y² = x³ + b`. -/
  b : Nat
  deriving Inhabited

----------------------------------------------------------------------------
-- Point type + curve operations.
----------------------------------------------------------------------------

/-- A point on a `Curve` in affine coordinates, plus a distinguished
    `infinity` (the group identity). The type is *not* indexed by the
    `Curve` — we keep it plain to avoid dependent-type friction; the
    curve is passed explicitly to every operation. -/
inductive Point where
  | infinity
  | affine (x y : Nat)
  deriving Inhabited, Repr

/-- `(x, y)` lies on `y² = x³ + b mod p`. -/
def onCurve (c : Curve) (x y : Nat) : Bool :=
  modMul y y c.p = modAdd (modMul x (modMul x x c.p) c.p) c.b c.p

/-- Double a point (`2P`), returning `infinity` when `P = infinity` or
    when `P.y = 0` (the tangent is vertical). For an `a = 0`
    short-Weierstrass curve the doubling formula is
    `λ = 3·x² / (2·y);  x' = λ² − 2·x;  y' = λ·(x − x') − y`. -/
def doublePoint (c : Curve) : Point → Point
  | .infinity => .infinity
  | .affine x y =>
    if y = 0 then .infinity
    else
      let p := c.p
      let lam := modMul (modMul 3 (modMul x x p) p) (modInv (modMul 2 y p) p) p
      let x' := modSub (modMul lam lam p) (modMul 2 x p) p
      let y' := modSub (modMul lam (modSub x x' p) p) y p
      .affine x' y'

/-- Add two affine points. Handles the special cases (identity,
    opposite points, doubling) explicitly rather than via the generic
    slope formula, which would divide by zero. -/
def addPoint (c : Curve) : Point → Point → Point
  | .infinity, Q => Q
  | P, .infinity => P
  | .affine x1 y1, .affine x2 y2 =>
    let p := c.p
    if x1 = x2 then
      if (y1 + y2) % p = 0 then .infinity
      else doublePoint c (.affine x1 y1)
    else
      let lam := modMul (modSub y2 y1 p) (modInv (modSub x2 x1 p) p) p
      let x3 := modSub (modSub (modMul lam lam p) x1 p) x2 p
      let y3 := modSub (modMul lam (modSub x1 x3 p) p) y1 p
      .affine x3 y3

/-- Scalar multiplication `k · P` via right-to-left double-and-add. -/
def scalarMul (c : Curve) (k : Nat) (P : Point) : Point := Id.run do
  let mut R : Point := .infinity
  let mut base : Point := P
  let mut e := k
  while e ≠ 0 do
    if e % 2 = 1 then R := addPoint c R base
    base := doublePoint c base
    e := e / 2
  return R

/-- Simultaneous double-scalar multiplication `k₁·P₁ + k₂·P₂` via
    Shamir's trick: process both scalars' bits together so we pay
    for one doubling chain (~ bitlen doublings) rather than two,
    with adds picked from a 4-entry `{∞, P₁, P₂, P₁+P₂}` precomputed
    table keyed by the current bit-pair. -/
def scalarMul2 (c : Curve) (k1 : Nat) (P1 : Point) (k2 : Nat) (P2 : Point) : Point :=
  Id.run do
  let P1plus2 := addPoint c P1 P2
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
    Q := doublePoint c Q
    let b1 : Bool := (k1 >>> i) &&& 1 = 1
    let b2 : Bool := (k2 >>> i) &&& 1 = 1
    match b1, b2 with
    | false, false => pure ()
    | true,  false => Q := addPoint c Q P1
    | false, true  => Q := addPoint c Q P2
    | true,  true  => Q := addPoint c Q P1plus2
  return Q

/-- Given an `x`-coordinate and a parity bit `y_odd`, recover the
    unique curve point `(x, y)` with `y mod 2 = y_odd`, or `none` if
    no such point exists (i.e. `x³ + b` is not a quadratic residue
    mod `p`).

    Requires `c.p ≡ 3 mod 4` so the direct-exponentiation `modSqrt`
    is a valid square root. Both secp256k1 (`b = 7`) and alt_bn128
    (`b = 3`) satisfy this. -/
def decompress (c : Curve) (x : Nat) (yOdd : Bool) : Option Point :=
  let p := c.p
  let α := modAdd (modMul x (modMul x x p) p) c.b p
  let β := modSqrt α p
  if modMul β β p ≠ α then none
  else
    let y := if (β % 2 = 1) = yOdd then β else p - β
    some (.affine x y)

end EvmSemantics.Crypto.EC
