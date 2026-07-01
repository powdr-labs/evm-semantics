module

public import EvmSemantics.Crypto.Bls12381.Curve
public import EvmSemantics.Crypto.Bls12381.Codec
public import EvmSemantics.Crypto.Bls12381.G1Add
public import EvmSemantics.Data.Bytes

/-!
`EvmSemantics.Crypto.Bls12381G1Msm` — EIP-2537 `0x0C
BLS12_G1MSM`, multi-scalar multiplication on G₁.

Wire format: `k · 160` bytes for `k ≥ 1` (empty input is invalid),
arranged as `k` pairs `(P_i, s_i)`:

  Pair layout (160 bytes)
    ┌────────────────────────────────┐
    │ G₁ point (128 B): x ‖ y         │
    ├────────────────────────────────┤
    │ scalar (32 B): big-endian Nat   │
    └────────────────────────────────┘

Output: 128-byte encoding of `∑ᵢ s_i · P_i` (`(0, 0)` for
infinity).

Gas: EIP-2537 defines a *discounted* table
`gas = k · 12000 · discount(k) / 1000` where `discount(k)` starts
at ~1000 for `k = 1` and drops for larger `k` (batching efficiency).
For simplicity this implementation uses the flat per-pair cost
(`gas = 12000 · k`) — the discount only *lowers* the price, so this
is a conservative overestimate. Refining to match the exact
EIP-2537 curve is a follow-up.
-/

@[expose] public section

namespace EvmSemantics.Crypto.Bls12381G1Msm

open EvmSemantics.Crypto.Bls12381 (Point addPoint scalarMul)
open EvmSemantics.Crypto.Bls12381Codec (g1Bytes)
open EvmSemantics.Crypto.Bls12381G1Add (decodePoint encodePoint)
open EvmSemantics.Data.Bytes (bytesToBigEndianNat)

/-- Wire size (bytes) of one `(G₁, scalar)` pair. -/
def pairBytes : Nat := 160

/-- Number of pairs `k` in the input, or `none` if the input length
    isn't a positive multiple of 160. -/
def numPairs (input : ByteArray) : Option Nat :=
  if input.size = 0 ∨ input.size % pairBytes ≠ 0 then none
  else some (input.size / pairBytes)

/-- Run `0x0C BLS12_G1MSM` core: parse, scalar-mul + accumulate. -/
def run? (input : ByteArray) : Option ByteArray := Id.run do
  match numPairs input with
  | none => return none
  | some k =>
    let mut acc : Point := .infinity
    for i in [0:k] do
      let off := i * pairBytes
      match decodePoint input off with
      | none => return none
      | some P =>
        let s := bytesToBigEndianNat (input.extract (off + g1Bytes) (off + pairBytes))
        acc := addPoint acc (scalarMul s P)
    return some (encodePoint acc)

end EvmSemantics.Crypto.Bls12381G1Msm
