module

public import EvmSemantics.Crypto.Bls12381.Curve
public import EvmSemantics.Crypto.Bls12381.Codec
public import EvmSemantics.Crypto.Bls12381.G2Add
public import EvmSemantics.Data.Bytes

/-!
`EvmSemantics.Crypto.Bls12381G2Msm` — EIP-2537 `0x0E
BLS12_G2MSM`, multi-scalar multiplication on G₂.

Wire format: `k · 288` bytes for `k ≥ 1`, arranged as `k` pairs
`(Q_i, s_i)`:

  Pair layout (288 bytes)
    ┌────────────────────────────────┐
    │ G₂ point (256 B):               │
    │   X.c0 ‖ X.c1 ‖ Y.c0 ‖ Y.c1     │
    ├────────────────────────────────┤
    │ scalar (32 B)                   │
    └────────────────────────────────┘

Output: 256-byte encoding of `∑ᵢ s_i · Q_i`.

Gas: as with G1MSM, EIP-2537 uses a discounted per-pair table with
base cost 22500. This implementation uses the flat
`gas = 22500 · k` (conservative overestimate).
-/

@[expose] public section

namespace EvmSemantics.Crypto.Bls12381G2Msm

open EvmSemantics.Crypto.Bls12381 (G2Point g2Curve)
open EvmSemantics.Crypto.G2 (addPoint)
open EvmSemantics.Crypto.Bls12381Codec (g2Bytes)
open EvmSemantics.Crypto.Bls12381G2Add (decodePoint encodePoint)
open EvmSemantics.Data.Bytes (bytesToBigEndianNat)

/-- Wire size (bytes) of one `(G₂, scalar)` pair. -/
def pairBytes : Nat := 288

/-- Number of pairs, or `none` if the input length isn't a positive
    multiple of 288. -/
def numPairs (input : ByteArray) : Option Nat :=
  if input.size = 0 ∨ input.size % pairBytes ≠ 0 then none
  else some (input.size / pairBytes)

/-- G₂ scalar multiplication `k · P` via right-to-left double-and-add. -/
def scalarMulG2 (k : Nat) (P : G2Point) : G2Point := Id.run do
  let mut R : G2Point := .infinity
  let mut base : G2Point := P
  let mut e := k
  while e ≠ 0 do
    if e % 2 = 1 then R := addPoint R base
    base := addPoint base base
    e := e / 2
  return R

/-- Run `0x0E BLS12_G2MSM` core. -/
def run? (input : ByteArray) : Option ByteArray := Id.run do
  match numPairs input with
  | none => return none
  | some k =>
    let mut acc : G2Point := .infinity
    for i in [0:k] do
      let off := i * pairBytes
      match decodePoint input off with
      | none => return none
      | some Q =>
        let s := bytesToBigEndianNat (input.extract (off + g2Bytes) (off + pairBytes))
        acc := addPoint acc (scalarMulG2 s Q)
    return some (encodePoint acc)

end EvmSemantics.Crypto.Bls12381G2Msm
