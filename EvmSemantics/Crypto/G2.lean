module

public import EvmSemantics.Crypto.Fp2
public import EvmSemantics.Crypto.Bn254

/-!
`EvmSemantics.Crypto.G2` — the twist curve `G₂` for BN254 pairing.

BN254's `G₂` is the group of points on the sextic twist
`E': y² = x³ + b'` over `F_p²`, where `b' = b / ξ = 3 / (9 + u)`.
Points are represented in affine coordinates with an `infinity`
marker, exactly mirroring the `G₁` shape in `EvmSemantics.Crypto.EC`,
but with `Fp2` coordinates instead of `Nat`.

EIP-197 wire format for a `G₂` point is 128 bytes:
`X.c1 ‖ X.c0 ‖ Y.c1 ‖ Y.c0` — *imaginary* (coeff of `u`) part first
for each `Fp2` coefficient. The precompile driver handles the swap;
this file stays "natural" `(c0, c1)`.

EIP-197's validity conditions on `G₂` inputs are:
* Every 32-byte coordinate fragment is `< p`.
* Either `(0, 0)` — infinity — or on `E'` (the on-curve check below).

We deliberately do **not** enforce subgroup membership (`N·P = ∞`).
The spec only requires on-curve, and a fast subgroup check via
Frobenius would need extra pairing-machinery constants we don't yet
have.
-/

@[expose] public section

namespace EvmSemantics.Crypto.G2

open EvmSemantics.Crypto.Fp2
open EvmSemantics.Crypto.Bn254 (p)

/-- Point on the BN254 twist in affine form (or infinity). -/
inductive Point where
  | infinity
  | affine (x y : Fp2)
  deriving Inhabited

/-- The twist coefficient `b' = 3 / (9 + u)` as an `Fp2`.

    Computed via `3 · (9 + u)⁻¹`: the inverse of `9 + u` under the
    `Fp2` norm formula. Cached as a `def` — the compiler evaluates it
    once at load time. -/
def twistB : Fp2 :=
  Fp2.mulByFp p (Fp2.inv p { c0 := 9, c1 := 1 }) 3

/-- `(x, y) ∈ E'(Fp²)` iff `y² = x³ + b'`. -/
def onCurve (x y : Fp2) : Bool :=
  let lhs := Fp2.square p y
  let rhs := Fp2.add p (Fp2.mul p x (Fp2.square p x)) twistB
  Fp2.eq lhs rhs

/-- Double a G₂ point. Same formula as `G₁`, lifted over `Fp2`. -/
def doublePoint : Point → Point
  | .infinity => .infinity
  | .affine x y =>
    if Fp2.eq y Fp2.zero then .infinity
    else
      let x2 := Fp2.square p x
      let threeX2 := Fp2.add p (Fp2.add p x2 x2) x2
      let twoY := Fp2.add p y y
      let lam := Fp2.mul p threeX2 (Fp2.inv p twoY)
      let x' := Fp2.sub p (Fp2.square p lam) (Fp2.add p x x)
      let y' := Fp2.sub p (Fp2.mul p lam (Fp2.sub p x x')) y
      .affine x' y'

/-- Add two G₂ points. -/
def addPoint : Point → Point → Point
  | .infinity, Q => Q
  | P, .infinity => P
  | .affine x1 y1, .affine x2 y2 =>
    if Fp2.eq x1 x2 then
      if Fp2.eq (Fp2.add p y1 y2) Fp2.zero then .infinity
      else doublePoint (.affine x1 y1)
    else
      let lam := Fp2.mul p (Fp2.sub p y2 y1) (Fp2.inv p (Fp2.sub p x2 x1))
      let x3 := Fp2.sub p (Fp2.sub p (Fp2.square p lam) x1) x2
      let y3 := Fp2.sub p (Fp2.mul p lam (Fp2.sub p x1 x3)) y1
      .affine x3 y3

/-- Negate a G₂ point: `-P = (x, -y)`. -/
@[inline] def negate : Point → Point
  | .infinity => .infinity
  | .affine x y => .affine x (Fp2.neg p y)

end EvmSemantics.Crypto.G2
