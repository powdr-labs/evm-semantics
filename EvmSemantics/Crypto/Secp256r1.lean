module

public import EvmSemantics.Crypto.Weierstrass

/-!
`EvmSemantics.Crypto.Secp256r1` — the secp256r1 (NIST P-256) curve
constants + concrete `Fp := Fin Secp256r1.p` / `Curve p` bindings.

P-256 is the short-Weierstrass curve `y² = x³ + a·x + b (mod p)` with
`a = −3`, used by EIP-7951's `P256VERIFY` precompile (`0x100`). Unlike
the codebase's other curves (secp256k1 / BN254 / BLS12-381 G1, all
`a = 0`), P-256 has `a ≠ 0`, which is why `Crypto.Weierstrass` carries
the `a` coefficient. Field extensions of `Fin p` live in `Crypto.FF`;
the generic point operations live in `Crypto.Weierstrass`. This module
just pins the numeric parameters and re-exports the ops `P256VERIFY`
needs.
-/

@[expose] public section

namespace EvmSemantics.Crypto.Secp256r1

/-- The P-256 field prime `p = 2²⁵⁶ − 2²²⁴ + 2¹⁹² + 2⁹⁶ − 1`. Hex:
    `0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff`. -/
def p : Nat := 2^256 - 2^224 + 2^192 + 2^96 - 1

/-- The P-256 group order `N` (no short closed form). Hex:
    `0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551`. -/
def N : Nat := 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551

/-- `p` is nonzero — required for `Fin p`'s numeric-tower instances. -/
instance : NeZero p := ⟨by unfold p; omega⟩

/-- `N` is nonzero — for scalar-field (`Fin N`) modular arithmetic. -/
instance : NeZero N := ⟨by unfold N; decide⟩

/-- Linear coefficient `a = −3 mod p`. -/
def aCoeff : Nat := p - 3

/-- Constant coefficient `b`. -/
def bCoeff : Nat := 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b

/-- Generator `x`-coordinate. -/
def Gx : Nat := 0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296

/-- Generator `y`-coordinate. -/
def Gy : Nat := 0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5

/-- Field elements over `F_p`. -/
abbrev Fp := Fin p

/-- Curve point over `Fp`. -/
abbrev Point := EvmSemantics.Crypto.EC.Point Fp

/-- The P-256 curve packaged for the generic point operations. -/
def curve : EvmSemantics.Crypto.Weierstrass.Curve p :=
  { a := Fin.ofNat _ aCoeff, b := Fin.ofNat _ bCoeff }

/-- The P-256 generator point `G`. -/
def G : Point := .affine (Fin.ofNat _ Gx) (Fin.ofNat _ Gy)

/-- Simultaneous double-scalar multiplication `k₁·G + k₂·Q` (Shamir). -/
@[inline] def scalarMul2 (k1 : Nat) (P1 : Point) (k2 : Nat) (P2 : Point) : Point :=
  EvmSemantics.Crypto.Weierstrass.scalarMul2 curve k1 P1 k2 P2

/-- Curve-membership check `y² = x³ + a·x + b`. -/
@[inline] def onCurve (x y : Fp) : Bool :=
  EvmSemantics.Crypto.Weierstrass.onCurve curve x y

end EvmSemantics.Crypto.Secp256r1
