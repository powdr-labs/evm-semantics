module

public import EvmSemantics.Crypto.EC

/-!
`EvmSemantics.Crypto.Secp256k1` — the secp256k1 curve constants.

secp256k1 is the short-Weierstrass curve `y² = x³ + 7` (mod `p`), with
`a = 0`, used by Ethereum's ECRECOVER (0x01). All the modular
arithmetic and generic point operations live in
`EvmSemantics.Crypto.EC`; this module just pins the numeric parameters
and re-exports the `EC` helpers under this namespace so the existing
`Ecrecover` call sites (`modInv _ N`, `scalarMul2 …`, …) keep working.
-/

@[expose] public section

namespace EvmSemantics.Crypto.Secp256k1

open EvmSemantics.Crypto.EC

/-- The secp256k1 field prime `p = 2^256 − 2^32 − 977`. -/
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

/-- The secp256k1 curve packaged for the generic `EC` operations. -/
def curve : Curve := { p := p, b := 7 }

/-- The secp256k1 generator point `G`. -/
def G : Point := .affine Gx Gy

/-- Double a secp256k1 point. -/
@[inline] def doublePoint (P : Point) : Point := EC.doublePoint curve P

/-- Add two secp256k1 points. -/
@[inline] def addPoint (P Q : Point) : Point := EC.addPoint curve P Q

/-- Scalar multiplication on secp256k1. -/
@[inline] def scalarMul (k : Nat) (P : Point) : Point := EC.scalarMul curve k P

/-- Simultaneous double-scalar multiplication on secp256k1. -/
@[inline] def scalarMul2 (k1 : Nat) (P1 : Point) (k2 : Nat) (P2 : Point) : Point :=
  EC.scalarMul2 curve k1 P1 k2 P2

/-- Curve-membership check on secp256k1. -/
@[inline] def onCurve (x y : Nat) : Bool := EC.onCurve curve x y

/-- Point decompression for secp256k1. -/
@[inline] def decompress (x : Nat) (yOdd : Bool) : Option Point :=
  EC.decompress curve x yOdd

end EvmSemantics.Crypto.Secp256k1
