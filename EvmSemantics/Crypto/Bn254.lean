module

public import EvmSemantics.Crypto.EC

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
