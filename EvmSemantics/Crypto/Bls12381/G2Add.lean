module

public import EvmSemantics.Crypto.Bls12381.Curve
public import EvmSemantics.Crypto.Bls12381.Codec

/-!
`EvmSemantics.Crypto.Bls12381G2Add` — EIP-2537 `0x0D BLS12_G2ADD`.

Wire format (512 bytes in, 256 bytes out):

* `input[0:256]`   — first addend, a G₂ point.
* `input[256:512]` — second addend, a G₂ point.

Each 256-byte G₂ point is `X.c0 ‖ X.c1 ‖ Y.c0 ‖ Y.c1` (four 64-byte
`Fp` elements — EIP-2537 puts `c0` (real) *before* `c1` (imaginary),
opposite the EIP-197 BN254 order). The pair
`(0,0,0,0)` is the wire encoding of infinity.

Output: 256-byte encoding of the sum (`(0,0,0,0)` for infinity).

Gas: flat 600 (EIP-2537).
-/

@[expose] public section

namespace EvmSemantics.Crypto.Bls12381G2Add

open EvmSemantics.Crypto.Bls12381 (Fp2 G2Point g2Curve)
open EvmSemantics.Crypto.G2 (addPoint onCurve)
open EvmSemantics.Crypto.Bls12381Codec (decodeFp2 encodeFp2 g2Bytes fp2Bytes)

/-- Decode a G₂ point from `input[off..off+256)`. -/
def decodePoint (input : ByteArray) (off : Nat) : Option G2Point := do
  let X ← decodeFp2 input off
  let Y ← decodeFp2 input (off + fp2Bytes)
  if X.c0.val = 0 ∧ X.c1.val = 0 ∧ Y.c0.val = 0 ∧ Y.c1.val = 0 then
    some .infinity
  else if onCurve g2Curve X Y then some (.affine X Y)
  else none

/-- Encode a G₂ point back to the 256-byte wire form. -/
def encodePoint : G2Point → ByteArray
  | .infinity => encodeFp2 0 ++ encodeFp2 0
  | .affine X Y => encodeFp2 X ++ encodeFp2 Y

/-- Run the 0x0D G2ADD precompile core. -/
def run? (input : ByteArray) : Option ByteArray := do
  if input.size ≠ 2 * g2Bytes then none
  else
    let P ← decodePoint input 0
    let Q ← decodePoint input g2Bytes
    some (encodePoint (addPoint P Q))

end EvmSemantics.Crypto.Bls12381G2Add
