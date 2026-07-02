module

public import EvmSemantics.Crypto.Fp2

/-!
`EvmSemantics.Crypto.G2` — the twist curve `G₂` for pairing-friendly
curves, polymorphic in the base-field prime `p`.

Both BN254 and BLS12-381 have a G₂ over `F_p²` of shape
`E': y² = x³ + b'` — same doubling / addition formulas, only the
twist coefficient `b'` differs (BN254: `b' = 3/(9+u)`, D-type;
BLS12-381: `b' = 4·(1+u)`, M-type). We factor `b'` out into a
`Curve p` structure carrying it, so this module serves both curves
without duplication. Each concrete curve module defines its own
`Curve` value and re-exports the ops under its namespace.

Points are affine `Fp2 p` pairs plus an `infinity` marker.

For the pairing spec's on-curve check, callers pass a `Curve p`
whose `b` is the correct twist coefficient. `doublePoint / addPoint
/ negate` don't consume the coefficient (curve `a = 0` and the
doubling / addition formulas depend only on `a`), so they take just
the Point.
-/

@[expose] public section

namespace EvmSemantics.Crypto.G2

/-- The twist coefficient bundle for a curve's G₂ — just `b'`, since
    all our curves are `a = 0` short-Weierstrass. -/
structure Curve (p : Nat) where
  /-- The twist coefficient `b' ∈ Fp2 p`. -/
  b : Fp2 p

/-- Point on a G₂ twist in affine form (or infinity). -/
inductive Point (p : Nat) where
  | infinity
  | affine (x y : Fp2 p)

instance {p : Nat} : Inhabited (Point p) := ⟨.infinity⟩

/-- `(x, y) ∈ E'(Fp²)` iff `y² = x³ + b'`. -/
def onCurve {p : Nat} [NeZero p] (c : Curve p) (x y : Fp2 p) : Bool :=
  Fp2.eq (y^2) (x * x^2 + c.b)

/-- Double a G₂ point. Formula for `a = 0` short-Weierstrass, over
    `Fp2` this time. -/
def doublePoint {p : Nat} [NeZero p] : Point p → Point p
  | .infinity => .infinity
  | .affine x y =>
    if Fp2.eq y 0 then .infinity
    else
      let lam := (3 * x^2) * (2 * y)⁻¹
      let x' := lam^2 - 2 * x
      let y' := lam * (x - x') - y
      .affine x' y'

/-- Add two G₂ points. -/
def addPoint {p : Nat} [NeZero p] : Point p → Point p → Point p
  | .infinity, Q => Q
  | P, .infinity => P
  | .affine x1 y1, .affine x2 y2 =>
    if Fp2.eq x1 x2 then
      if Fp2.eq (y1 + y2) 0 then .infinity
      else doublePoint (.affine x1 y1)
    else
      let lam := (y2 - y1) * (x2 - x1)⁻¹
      let x3 := lam^2 - x1 - x2
      let y3 := lam * (x1 - x3) - y1
      .affine x3 y3

/-- Negate a G₂ point: `-P = (x, -y)`. -/
@[inline] def negate {p : Nat} : Point p → Point p
  | .infinity => .infinity
  | .affine x y => .affine x (-y)

/-- Scalar multiplication `k · P` via right-to-left double-and-add.
    Mirrors `Weierstrass.scalarMul` for the twist. Used for the
    prime-order-subgroup membership check `[N]Q = ∞` that EIP-197 /
    EIP-2537 require on every G₂ input (the twist curve has non-
    trivial cofactor, so on-curve does not imply in-subgroup). -/
def scalarMul {p : Nat} [NeZero p] (k : Nat) (P : Point p) : Point p :=
  Id.run do
  let mut R : Point p := .infinity
  let mut base : Point p := P
  let mut e := k
  while e ≠ 0 do
    if e % 2 = 1 then R := addPoint R base
    base := doublePoint base
    e := e / 2
  return R

/-- `Q` lies in the prime-order subgroup of order `n` iff `[n]Q = ∞`.
    Naive `O(log n)` scalar-mul; a Frobenius shortcut exists for
    specific curves but is not worth the code complexity here. -/
def inSubgroup {p : Nat} [NeZero p] (n : Nat) (P : Point p) : Bool :=
  match scalarMul n P with
  | .infinity => true
  | .affine _ _ => false

end EvmSemantics.Crypto.G2
