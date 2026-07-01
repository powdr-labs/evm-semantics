module

public import EvmSemantics.Crypto.EC
public import EvmSemantics.Crypto.FF

/-!
`EvmSemantics.Crypto.Weierstrass` — short-Weierstrass curve arithmetic
`y² = x³ + b` (i.e. `a = 0`) over `F_p`, in affine coordinates.

The whole file is generic in `p` (any prime, given `[NeZero p]`);
concrete curves (`Secp256k1` with `b = 7`, `Bn254` with `b = 3`)
supply a `Curve p` value and re-export the ops under their own
namespace.

Both Ethereum curves this codebase touches (secp256k1 and BN254) are
of this shape, hence "short Weierstrass" in the file name — no
Montgomery, twisted-Edwards, or general-`a` support is provided or
needed. `Point` (the affine-plus-infinity container) lives in
`EvmSemantics.Crypto.EC`; field extensions of `Fin p` (`Inv`,
`HPow`, `sqrt`) live in `EvmSemantics.Crypto.FF`.
-/

@[expose] public section

namespace EvmSemantics.Crypto.Weierstrass

open EvmSemantics.Crypto.EC (Point)
open EvmSemantics.Crypto.FF (sqrt)

/-- A short-Weierstrass curve `y² = x³ + b` over `F_p`. -/
structure Curve (p : Nat) where
  /-- The curve equation coefficient. -/
  b : Fin p

/-- `(x, y) ∈ E(F_p)` iff `y² = x³ + b`. `[NeZero p]` is required
    for the operator resolution (the linter can't see through
    typeclass instance elaboration, hence `nolint`). -/
@[nolint unusedArguments]
def onCurve {p : Nat} [NeZero p] (c : Curve p) (x y : Fin p) : Bool :=
  y * y = x * (x * x) + c.b

/-- Double a curve point. Formula for `a = 0` short-Weierstrass:
    `λ = 3·x² / (2·y);  x' = λ² − 2·x;  y' = λ·(x − x') − y`.
    The `Curve` argument is unused (doubling only needs `a = 0`,
    baked in) but kept for API symmetry with `addPoint c`. -/
@[nolint unusedArguments]
def doublePoint {p : Nat} [NeZero p] (_c : Curve p) :
    Point (Fin p) → Point (Fin p)
  | .infinity => .infinity
  | .affine x y =>
    if y = 0 then .infinity
    else
      let lam := (3 * x * x) * (2 * y)⁻¹
      let x' := lam * lam - 2 * x
      let y' := lam * (x - x') - y
      .affine x' y'

/-- Add two affine points. Handles identity / opposite / doubling
    cases explicitly so we never divide by zero. -/
def addPoint {p : Nat} [NeZero p] (c : Curve p) :
    Point (Fin p) → Point (Fin p) → Point (Fin p)
  | .infinity, Q => Q
  | P, .infinity => P
  | .affine x1 y1, .affine x2 y2 =>
    if x1 = x2 then
      if y1 + y2 = 0 then .infinity
      else doublePoint c (.affine x1 y1)
    else
      let lam := (y2 - y1) * (x2 - x1)⁻¹
      let x3 := lam * lam - x1 - x2
      let y3 := lam * (x1 - x3) - y1
      .affine x3 y3

/-- Scalar multiplication `k · P` via right-to-left double-and-add. -/
def scalarMul {p : Nat} [NeZero p] (c : Curve p) (k : Nat)
    (P : Point (Fin p)) : Point (Fin p) :=
  Id.run do
  let mut R : Point (Fin p) := .infinity
  let mut base : Point (Fin p) := P
  let mut e := k
  while e ≠ 0 do
    if e % 2 = 1 then R := addPoint c R base
    base := doublePoint c base
    e := e / 2
  return R

/-- Simultaneous double-scalar multiplication `k₁·P₁ + k₂·P₂` via
    Shamir's trick. -/
def scalarMul2 {p : Nat} [NeZero p] (c : Curve p)
    (k1 : Nat) (P1 : Point (Fin p)) (k2 : Nat) (P2 : Point (Fin p)) :
    Point (Fin p) :=
  Id.run do
  let P1plus2 := addPoint c P1 P2
  let mut bitlen : Nat := 0
  let mut m := Nat.max k1 k2
  while m ≠ 0 do
    bitlen := bitlen + 1
    m := m / 2
  let mut Q : Point (Fin p) := .infinity
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

/-- Given `x` and a parity bit `yOdd`, recover the unique `(x, y)` on
    the curve with `y mod 2 = yOdd`, or `none` if `x³ + b` is not a
    quadratic residue. Requires `p ≡ 3 mod 4`. -/
def decompress {p : Nat} [NeZero p] (c : Curve p) (x : Fin p) (yOdd : Bool) :
    Option (Point (Fin p)) :=
  let α := x * x * x + c.b
  let β := sqrt α
  if β * β ≠ α then none
  else
    let y : Fin p := if (β.val % 2 = 1) = yOdd then β else -β
    some (.affine x y)

end EvmSemantics.Crypto.Weierstrass
