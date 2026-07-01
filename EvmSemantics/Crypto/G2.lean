module

public import EvmSemantics.Crypto.Bn254

/-!
`EvmSemantics.Crypto.G2` — the twist curve `G₂` for BN254 pairing.

BN254's `G₂` is the group of points on the sextic twist
`E': y² = x³ + b'` over `F_p²`, where `b' = b / ξ = 3 / (9 + u)`.
Points are affine `Fp2 Bn254.p` pairs plus an `infinity` marker.

EIP-197 wire format for a `G₂` point is 128 bytes:
`X.c1 ‖ X.c0 ‖ Y.c1 ‖ Y.c0` — imaginary part first per `Fp2`
coefficient. The precompile driver handles that swap; this file
stays "natural" `(c0, c1)`.

EIP-197's validity conditions on `G₂` inputs:
* Every 32-byte coordinate fragment is `< p`.
* Either `(0, 0)` — infinity — or on `E'`.

We deliberately do **not** enforce subgroup membership (`N·P = ∞`);
the spec only requires on-curve.
-/

@[expose] public section

namespace EvmSemantics.Crypto.G2

open EvmSemantics.Crypto.Bn254 (Fp2)

/-- Point on the BN254 twist in affine form (or infinity). -/
inductive Point where
  | infinity
  | affine (x y : Fp2)
  deriving Inhabited

/-- The twist coefficient `b' = 3 / (9 + u)` on `Fp2 Bn254.p`. -/
def twistB : Fp2 := _root_.Fp2.mulByFp
  (_root_.Fp2.inv { c0 := 9, c1 := 1 }) 3

/-- `(x, y) ∈ E'(Fp²)` iff `y² = x³ + b'`. -/
def onCurve (x y : Fp2) : Bool :=
  _root_.Fp2.eq (y^2) (x * x^2 + twistB)

/-- Double a G₂ point. -/
def doublePoint : Point → Point
  | .infinity => .infinity
  | .affine x y =>
    if _root_.Fp2.eq y 0 then .infinity
    else
      let lam := (3 * x^2) * (2 * y)⁻¹
      let x' := lam^2 - 2 * x
      let y' := lam * (x - x') - y
      .affine x' y'

/-- Add two G₂ points. -/
def addPoint : Point → Point → Point
  | .infinity, Q => Q
  | P, .infinity => P
  | .affine x1 y1, .affine x2 y2 =>
    if _root_.Fp2.eq x1 x2 then
      if _root_.Fp2.eq (y1 + y2) 0 then .infinity
      else doublePoint (.affine x1 y1)
    else
      let lam := (y2 - y1) * (x2 - x1)⁻¹
      let x3 := lam^2 - x1 - x2
      let y3 := lam * (x1 - x3) - y1
      .affine x3 y3

/-- Negate a G₂ point: `-P = (x, -y)`. -/
@[inline] def negate : Point → Point
  | .infinity => .infinity
  | .affine x y => .affine x (-y)

end EvmSemantics.Crypto.G2
