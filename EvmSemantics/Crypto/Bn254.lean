module

public import EvmSemantics.Crypto.EC
public import EvmSemantics.Crypto.Fp2
public import EvmSemantics.Crypto.Fp6
public import EvmSemantics.Crypto.Fp12

/-!
`EvmSemantics.Crypto.Bn254` — the alt_bn128 / BN254 curve constants.

BN254 is the short-Weierstrass curve `y² = x³ + 3` (mod `p`) — the pairing-
friendly curve Ethereum uses for the Byzantium-era zkSNARK precompiles
ECADD (0x06), ECMUL (0x07), and ECPAIRING (0x08).

Numeric parameters (EIP-196 / EIP-197):

* `p = 21888242871839275222246405745257275088696311157297823662689037894645226208583`
  — the base field prime. `p ≡ 3 (mod 4)`, so the direct-exponentiation
  `modSqrt` from `EC` is valid.
* `N = 21888242871839275222246405745257275088548364400416034343698204186575808495617`
  — the group (subgroup) order. Not currently used by ECADD/ECMUL (they
  accept arbitrary-size scalars), but recorded here for symmetry with
  `Secp256k1.lean`.
* `G = (1, 2)` — the standard generator on the base curve.
* `a = 0`, `b = 3`.

Point arithmetic is inherited from `EvmSemantics.Crypto.EC` via the
generic `Curve` structure. The precompile drivers live in `Ecadd.lean`
and `Ecmul.lean`.
-/

@[expose] public section

namespace EvmSemantics.Crypto.Bn254

open EvmSemantics.Crypto.EC

/-- BN254 base-field prime. -/
def p : Nat :=
  21888242871839275222246405745257275088696311157297823662689037894645226208583

/-- BN254 group order (order of `G`). -/
def N : Nat :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

/-- Generator `x`-coordinate. -/
def Gx : Nat := 1

/-- Generator `y`-coordinate. -/
def Gy : Nat := 2

/-- The BN254 curve packaged for the generic `EC` operations. -/
def curve : Curve := { p := p, b := 3 }

/-- The BN254 generator point `G = (1, 2)`. -/
def G : Point := .affine Gx Gy

/-- Double a BN254 point. -/
@[inline] def doublePoint (P : Point) : Point := EC.doublePoint curve P

/-- Add two BN254 points. -/
@[inline] def addPoint (P Q : Point) : Point := EC.addPoint curve P Q

/-- Scalar multiplication on BN254. -/
@[inline] def scalarMul (k : Nat) (P : Point) : Point := EC.scalarMul curve k P

/-- Curve-membership check on BN254. -/
@[inline] def onCurve (x y : Nat) : Bool := EC.onCurve curve x y

end EvmSemantics.Crypto.Bn254

/-!
## Numeric-tower typeclass instances

The pairing tower `Fp2 → Fp6 → Fp12` is used exclusively by BN254
(no other curve in the codebase touches it), so we pin the modulus
`Bn254.p` in the standard `Add/Sub/Mul/Neg/Zero/One/Inv/HPow`
instances. `Fp2.mul p a b` etc. remain the underlying implementation
— callers that want the raw curve-generic form can still spell it
that way. But `Pairing.lean` and other BN254 consumers can now write
`a * b + c * d` instead of `Fp*.add p (Fp*.mul p a b) (Fp*.mul p c d)`.

Specialised algorithms (`square`, `pow`, `frobenius`, `mulByXi`,
`mulByV`, `mulBy01`, `mulBy014`, `conj`) stay as named methods —
`x * x` would work for squaring but loses the faster
half-square formula, and Frobenius / sparse multiplication have no
natural operator symbol.
-/

open EvmSemantics.Crypto.Fp2  (Fp2)
open EvmSemantics.Crypto.Fp6  (Fp6)
open EvmSemantics.Crypto.Fp12 (Fp12)

namespace EvmSemantics.Crypto.Fp2
@[inline] instance : Add Fp2 := ⟨Fp2.add EvmSemantics.Crypto.Bn254.p⟩
@[inline] instance : Sub Fp2 := ⟨Fp2.sub EvmSemantics.Crypto.Bn254.p⟩
@[inline] instance : Mul Fp2 := ⟨Fp2.mul EvmSemantics.Crypto.Bn254.p⟩
@[inline] instance : Neg Fp2 := ⟨Fp2.neg EvmSemantics.Crypto.Bn254.p⟩
@[inline] instance : Zero Fp2 := ⟨Fp2.zero⟩
@[inline] instance : One Fp2 := ⟨Fp2.one⟩
end EvmSemantics.Crypto.Fp2

namespace EvmSemantics.Crypto.Fp6
@[inline] instance : Add Fp6 := ⟨Fp6.add EvmSemantics.Crypto.Bn254.p⟩
@[inline] instance : Sub Fp6 := ⟨Fp6.sub EvmSemantics.Crypto.Bn254.p⟩
@[inline] instance : Mul Fp6 := ⟨Fp6.mul EvmSemantics.Crypto.Bn254.p⟩
@[inline] instance : Neg Fp6 := ⟨Fp6.neg EvmSemantics.Crypto.Bn254.p⟩
@[inline] instance : Zero Fp6 := ⟨Fp6.zero⟩
@[inline] instance : One Fp6 := ⟨Fp6.one⟩
end EvmSemantics.Crypto.Fp6

namespace EvmSemantics.Crypto.Fp12
@[inline] instance : Add Fp12 := ⟨Fp12.add EvmSemantics.Crypto.Bn254.p⟩
@[inline] instance : Sub Fp12 := ⟨Fp12.sub EvmSemantics.Crypto.Bn254.p⟩
@[inline] instance : Mul Fp12 := ⟨Fp12.mul EvmSemantics.Crypto.Bn254.p⟩
@[inline] instance : Neg Fp12 := ⟨Fp12.neg EvmSemantics.Crypto.Bn254.p⟩
@[inline] instance : Zero Fp12 := ⟨Fp12.zero⟩
@[inline] instance : One Fp12 := ⟨Fp12.one⟩
@[inline] instance : Inv Fp12 := ⟨Fp12.inv EvmSemantics.Crypto.Bn254.p⟩
@[inline] instance : HPow Fp12 Nat Fp12 := ⟨Fp12.pow EvmSemantics.Crypto.Bn254.p⟩
end EvmSemantics.Crypto.Fp12
