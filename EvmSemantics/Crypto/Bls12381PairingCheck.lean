module

public import EvmSemantics.Crypto.Bls12381
public import EvmSemantics.Crypto.Bls12381Pairing
public import EvmSemantics.Crypto.Bls12381Codec
public import EvmSemantics.Crypto.Bls12381G1Add
public import EvmSemantics.Crypto.Bls12381G2Add
public import EvmSemantics.Data.Bytes

/-!
`EvmSemantics.Crypto.Bls12381PairingCheck` — EIP-2537
`0x0F BLS12_PAIRING_CHECK`.

Wire format: `k · 384` bytes for `k ≥ 0`, arranged as `k` pairs of
`(G₁, G₂)`:

  Pair layout (384 bytes)
    ┌─────────────────────────────────┐
    │ G₁ point (128 B): x ‖ y          │  each 64-byte `Fp`
    ├─────────────────────────────────┤
    │ G₂ point (256 B):                │
    │   X.c0 ‖ X.c1 ‖ Y.c0 ‖ Y.c1      │
    └─────────────────────────────────┘

Output: 32 bytes — `0x…01` if `∏ᵢ e(Pᵢ, Qᵢ) = 1 ∈ F_p¹²`, else
`0x…00`. Empty input (`k = 0`) → `0x…01` (empty product).

Gas (EIP-2537): `32600 + 43000 · k`. Invalid input (wrong length,
out-of-field coordinate, off-curve point, subgroup violation)
→ `.outOfGas` in the dispatcher.

Note: unlike EIP-197 (BN254 ECPAIRING), EIP-2537 *requires* that
each input point lies in the correct prime-order subgroup, not just
on the curve. We currently only check on-curve — a proper subgroup
check would require multiplying by `N` (the group order) and
verifying the result is infinity, or using an Frobenius-based
shortcut. Out of scope for this initial implementation.
-/

@[expose] public section

namespace EvmSemantics.Crypto.Bls12381PairingCheck

open EvmSemantics.Crypto.Bls12381 (Point G2Point Fp12)
open EvmSemantics.Crypto.Bls12381Pairing (multiPairing)
open EvmSemantics.Crypto.Bls12381G1Add (decodePoint)
open EvmSemantics.Data.Bytes (natToBytesPadded)

/-- Pair size (bytes). -/
def pairBytes : Nat := 384

/-- Decode `k` pairs of `(G₁, G₂)`. Returns `none` if length isn't a
    multiple of 384 or any point is malformed / off-curve. -/
def decodePairs (input : ByteArray) : Option (List (Point × G2Point)) :=
  Id.run do
    let sz := input.size
    if sz % pairBytes ≠ 0 then return none
    let k := sz / pairBytes
    let mut acc : List (Point × G2Point) := []
    for i in [0:k] do
      let off := i * pairBytes
      match Bls12381G1Add.decodePoint input off,
            Bls12381G2Add.decodePoint input (off + 128) with
      | some P, some Q => acc := (P, Q) :: acc
      | _, _ => return none
    return some acc.reverse

/-- Run the 0x0F PAIRING_CHECK precompile core. -/
def run? (input : ByteArray) : Option ByteArray :=
  match decodePairs input with
  | none => none
  | some pairs =>
    let result := multiPairing pairs
    let isOne : Bool := decide (result = (1 : Fp12))
    some (natToBytesPadded (if isOne then 1 else 0) 32)

end EvmSemantics.Crypto.Bls12381PairingCheck
