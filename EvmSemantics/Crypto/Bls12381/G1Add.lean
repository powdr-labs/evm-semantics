module

public import EvmSemantics.Crypto.Bls12381.Curve
public import EvmSemantics.Crypto.Bls12381.Codec

/-!
`EvmSemantics.Crypto.Bls12381G1Add` — EIP-2537 `0x0B BLS12_G1ADD`.

Wire format (256 bytes in, 128 bytes out):

* `input[0:128]`   — first addend, a G₁ point.
* `input[128:256]` — second addend, a G₁ point.

Each 128-byte G₁ point is `x ‖ y` (two 64-byte `Fp` elements). The
pair `(0, 0)` is the wire encoding of the point at infinity; every
other pair must be on `E: y² = x³ + 4` (mod `p`).

Output: 128-byte encoding of the sum (`(0, 0)` for infinity).

Gas: flat 375 (EIP-2537). Invalid input → all-gas-consumed
(`.outOfGas` in the dispatcher).
-/

@[expose] public section

namespace EvmSemantics.Crypto.Bls12381G1Add

open EvmSemantics.Crypto.Bls12381 (Fp Point addPoint onCurve)
open EvmSemantics.Crypto.Bls12381Codec (decodeFp encodeFp g1Bytes fpBytes)

/-- Decode a G₁ point from `input[off..off+128)`. Returns `none` on
    out-of-field or off-curve. `(0, 0)` decodes to infinity. -/
def decodePoint (input : ByteArray) (off : Nat) : Option Point := do
  let x ← decodeFp input off
  let y ← decodeFp input (off + fpBytes)
  if x.val = 0 ∧ y.val = 0 then some .infinity
  else if onCurve x y then some (.affine x y)
  else none

/-- Encode a G₁ point back to the 128-byte wire form. Infinity → all
    zeros. -/
def encodePoint : Point → ByteArray
  | .infinity => encodeFp 0 ++ encodeFp 0
  | .affine x y => encodeFp x ++ encodeFp y

/-- Run the 0x0B ECADD precompile core. -/
def run? (input : ByteArray) : Option ByteArray := do
  if input.size ≠ 2 * g1Bytes then none
  else
    let P ← decodePoint input 0
    let Q ← decodePoint input g1Bytes
    some (encodePoint (addPoint P Q))

end EvmSemantics.Crypto.Bls12381G1Add
