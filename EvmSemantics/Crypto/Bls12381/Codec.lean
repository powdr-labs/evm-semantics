module

public import EvmSemantics.Crypto.Bls12381.Curve
public import EvmSemantics.Data.Bytes

/-!
`EvmSemantics.Crypto.Bls12381Codec` — EIP-2537 wire codecs for
BLS12-381 field elements and G₁ / G₂ points.

Encoding conventions (EIP-2537 §"Data types"):

* An `Fp` element is 64 bytes: 16 leading zero bytes + 48 bytes
  big-endian value. Decoding rejects if the top 16 bytes aren't
  zero (the "wrong" leading pattern is invalid input) or if the
  48-byte value is `≥ p`.
* An `Fp2` element is 128 bytes: `c0 ‖ c1` in that order (note
  this is *opposite* to EIP-197's BN254 convention, which puts
  the imaginary part first). Each half is a 64-byte `Fp`.
* A `G₁` point is 128 bytes: `x ‖ y` (two `Fp`s).
* A `G₂` point is 256 bytes: `X.c0 ‖ X.c1 ‖ Y.c0 ‖ Y.c1`
  (an `Fp2` for `X` then an `Fp2` for `Y`).
* The wire form `(0, 0)` for G₁ / `(0, 0, 0, 0)` for G₂ decodes to
  the point at infinity — every other pair must be on the curve.

Any failure in this module returns `none` — the precompile
dispatcher maps that to `.outOfGas` per EIP-2537's
all-gas-consumed-on-invalid-input convention.
-/

@[expose] public section

namespace EvmSemantics.Crypto.Bls12381Codec

open EvmSemantics.Crypto.Bls12381 (p Fp Fp2)
open EvmSemantics.Data.Bytes (bytesToBigEndianNat natToBytesPadded)

/-- Wire size (bytes) of one `Fp` element. -/
def fpBytes : Nat := 64

/-- Wire size of one `Fp2` element. -/
def fp2Bytes : Nat := 128

/-- Wire size of one G₁ point. -/
def g1Bytes : Nat := 128

/-- Wire size of one G₂ point. -/
def g2Bytes : Nat := 256

/-- Decode an `Fp` element from `input[off..off+64)`. Rejects if
    the top 16 bytes are non-zero or the value `≥ p`. -/
def decodeFp (input : ByteArray) (off : Nat) : Option Fp :=
  if off + fpBytes > input.size then none
  else
    -- Top 16 bytes must be zero (EIP-2537 padding rule).
    let topZero : Bool := Id.run do
      for i in [0:16] do
        if input[off + i]! ≠ 0 then return false
      return true
    if ¬ topZero then none
    else
      let n := bytesToBigEndianNat (input.extract (off + 16) (off + 64))
      if n ≥ p then none else some (Fin.ofNat _ n)

/-- Decode an `Fp2` element from `input[off..off+128)`.
    Order: `c0 ‖ c1`. -/
def decodeFp2 (input : ByteArray) (off : Nat) : Option Fp2 :=
  match decodeFp input off, decodeFp input (off + fpBytes) with
  | some c0, some c1 => some { c0 := c0, c1 := c1 }
  | _, _ => none

/-- Encode an `Fp` element as 64 wire bytes (16 zero + 48 value). -/
def encodeFp (a : Fp) : ByteArray := natToBytesPadded a.val fpBytes

/-- Encode an `Fp2` element as 128 wire bytes: `c0 ‖ c1`. -/
def encodeFp2 (a : Fp2) : ByteArray := encodeFp a.c0 ++ encodeFp a.c1

end EvmSemantics.Crypto.Bls12381Codec
