module

public import EvmSemantics.Crypto.Weierstrass

/-!
`EvmSemantics.Crypto.Secp256k1` — the secp256k1 curve constants +
concrete `Fp := Fin Secp256k1.p` / `Curve p` bindings.

secp256k1 is the short-Weierstrass curve `y² = x³ + 7` (mod `p`) with
`a = 0`, used by Ethereum's ECRECOVER (0x01). All modular arithmetic
and generic point operations live in `EvmSemantics.Crypto.Weierstrass`; this
module just pins the numeric parameters and re-exports the concrete
type-instantiations of the ops.
-/

@[expose] public section

namespace EvmSemantics.Crypto.Secp256k1

/-- The secp256k1 field prime `p = 2²⁵⁶ − 2³² − 977` (pseudo-Mersenne
    form — enables the fast reduction used by libsecp256k1). Hex:
    `0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F`. -/
def p : Nat := 2^256 - 2^32 - 977

/-- The secp256k1 group order `N`. Hex:
    `0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141`. -/
def N : Nat :=
  0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

/-- `p` is nonzero — required for `Fin p`'s numeric-tower instances
    to resolve. -/
instance : NeZero p := ⟨by unfold p; omega⟩

/-- `N` is nonzero — same story as `p` but for the *scalar* field
    `Fin N`, used by `Ecrecover` to do modular arithmetic on the
    signature components. -/
instance : NeZero N := ⟨by unfold N; decide⟩

/-- Generator `x`-coordinate. -/
def Gx : Nat :=
  0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798

/-- Generator `y`-coordinate. -/
def Gy : Nat :=
  0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8

/-- Field elements over `F_p`. Type-alias to `Fin p` so the compiler
    can distinguish secp256k1 coordinates from BN254 ones — accepting
    a raw `Nat` in place of an `Fp` here is a type error. -/
abbrev Fp := Fin p

/-- Curve point over `Fp`. -/
abbrev Point := EvmSemantics.Crypto.EC.Point Fp

/-- The secp256k1 curve packaged for the generic point operations. -/
def curve : EvmSemantics.Crypto.Weierstrass.Curve p := { b := Fin.ofNat _ 7 }

/-- The secp256k1 generator point `G`. -/
def G : Point := .affine (Fin.ofNat _ Gx) (Fin.ofNat _ Gy)

/-- Double a secp256k1 point. -/
@[inline] def doublePoint (P : Point) : Point :=
  EvmSemantics.Crypto.Weierstrass.doublePoint curve P

/-- Add two secp256k1 points. -/
@[inline] def addPoint (P Q : Point) : Point :=
  EvmSemantics.Crypto.Weierstrass.addPoint curve P Q

/-- Scalar multiplication on secp256k1. -/
@[inline] def scalarMul (k : Nat) (P : Point) : Point :=
  EvmSemantics.Crypto.Weierstrass.scalarMul curve k P

/-- Simultaneous double-scalar multiplication (Shamir's trick). -/
@[inline] def scalarMul2 (k1 : Nat) (P1 : Point) (k2 : Nat) (P2 : Point) : Point :=
  EvmSemantics.Crypto.Weierstrass.scalarMul2 curve k1 P1 k2 P2

/-- Curve-membership check. -/
@[inline] def onCurve (x y : Fp) : Bool :=
  EvmSemantics.Crypto.Weierstrass.onCurve curve x y

/-- Point decompression: recover `y` from `x` and a parity bit. -/
@[inline] def decompress (x : Fp) (yOdd : Bool) : Option Point :=
  EvmSemantics.Crypto.Weierstrass.decompress curve x yOdd

end EvmSemantics.Crypto.Secp256k1
