module

public import EvmSemantics.Crypto.EC
public import EvmSemantics.Crypto.Bn254.Curve
public import EvmSemantics.Crypto.Bytes

/-!
`EvmSemantics.Crypto.Ecadd` — Ethereum's `0x06 ECADD` precompile,
alt_bn128 point addition (EIP-196, Byzantium+).

Wire format (128 bytes in, 64 bytes out):

* `input[0:32]  = x1`, `input[32:64] = y1` — first addend.
* `input[64:96] = x2`, `input[96:128] = y2` — second addend.
* Short input is right-padded with zeros (CALLDATALOAD convention);
  long input is truncated.
* Each coordinate is a 32-byte big-endian `Nat`; a coordinate is
  **valid** iff it is `< p` (the alt_bn128 field prime). Anything else
  is invalid input — the precompile fails and all provided gas is
  consumed (EIP-196 §"invalid input").
* The pair `(0, 0)` is the wire encoding of the *point at infinity*.
  Every other pair must satisfy `y² = x³ + 3 (mod p)` — otherwise the
  precompile fails with all-gas-consumed.

Output: `writeBE result.x 32 ++ writeBE result.y 32`, where `(∞, ∞)`
maps back to `(0, 0)`.
-/

@[expose] public section

namespace EvmSemantics.Crypto.Ecadd

open EvmSemantics.Crypto.EC
open EvmSemantics.Crypto.Bn254
open EvmSemantics.Crypto.Bytes

/-- Decode a `(x, y)` pair from the wire into a BN254 `Point`.
    Returns `none` if either coordinate is out-of-field (`≥ p`), or
    if the pair is not the wire-form of infinity `(0, 0)` and does
    not lie on the curve. -/
def decodePoint (x y : Nat) : Option Point :=
  if x ≥ p ∨ y ≥ p then none
  else if x = 0 ∧ y = 0 then some .infinity
  else
    let xF : Fp := Fin.ofNat _ x
    let yF : Fp := Fin.ofNat _ y
    if onCurve xF yF then some (.affine xF yF) else none

/-- Encode a `Point` back into the 64-byte wire form. Infinity goes
    to `(0, 0)`; every other point goes to its affine coordinates
    written MSB-first. `.val` peels the `Fp` back to `Nat` for the
    byte serialiser. -/
def encodePoint : Point → ByteArray
  | .infinity => writeBE 0 32 ++ writeBE 0 32
  | .affine x y => writeBE x.val 32 ++ writeBE y.val 32

/-- ECADD core: parse the (padded/truncated) 128-byte input, validate,
    and return `some 64-byte-output` on success or `none` if the input
    was invalid.

    On `none` the caller (the precompile dispatcher) treats the call
    as all-gas-consumed / no output, per EIP-196. -/
def run? (input : ByteArray) : Option ByteArray := do
  let x1 := readBE input 0   32
  let y1 := readBE input 32  32
  let x2 := readBE input 64  32
  let y2 := readBE input 96  32
  let P ← decodePoint x1 y1
  let Q ← decodePoint x2 y2
  some (encodePoint (addPoint P Q))

end EvmSemantics.Crypto.Ecadd
