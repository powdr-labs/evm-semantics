module

public import EvmSemantics.Crypto.EC
public import EvmSemantics.Crypto.Fp2
public import EvmSemantics.Crypto.Fp12
public import EvmSemantics.Crypto.G2
public import EvmSemantics.Crypto.Bn254.Curve
public import EvmSemantics.Crypto.Bytes
public import EvmSemantics.Crypto.Bn254.Pairing

/-!
`EvmSemantics.Crypto.Bn254.Ecpairing` — Ethereum's `0x08 ECPAIRING`
precompile driver (EIP-197, Byzantium+). **This is the precompile
wrapper — wire format, input validation, boolean output.** The
underlying pairing algebra (Miller loop + final exponentiation on
BN254 `Fp12`) lives in `EvmSemantics.Crypto.Bn254.Pairing`.

Wire format: input is `k · 192` bytes for some `k ≥ 0`, arranged as
`k` back-to-back point pairs:

  Pair layout (192 bytes)
    ┌───────────────────────────────┐
    │ G₁ point (64 B): X ‖ Y         │  each 32-byte big-endian
    ├───────────────────────────────┤
    │ G₂ point (128 B):              │
    │   X.imag ‖ X.real ‖            │  each 32-byte big-endian
    │   Y.imag ‖ Y.real              │
    └───────────────────────────────┘

Output is 32 bytes: `0x…01` if `∏ᵢ e(P_i, Q_i) = 1 ∈ F_p¹²`, else
`0x…00`. Empty input `k = 0` is treated as an empty product `= 1`,
so output is `0x…01`.

Invalid input (wrong length, coordinate out of field, point not on
curve) makes the precompile fail with all-gas consumed (mapped to
`.outOfGas` in the dispatcher).
-/

@[expose] public section

namespace EvmSemantics.Crypto.Ecpairing

open EvmSemantics.Crypto.EC
open EvmSemantics.Crypto.Pairing (Fp2Bn Fp12Bn)
open EvmSemantics.Crypto.G2
open EvmSemantics.Crypto.Bn254 (p Fp)
open EvmSemantics.Crypto.Bytes

/-- Decode a G₁ point from `input[off..off+64)`. Returns `none` on
    out-of-field or off-curve. `(0, 0)` decodes to infinity. -/
def decodeG1 (input : ByteArray) (off : Nat) : Option Bn254.Point :=
  let x := readBE input off 32
  let y := readBE input (off + 32) 32
  if x ≥ p ∨ y ≥ p then none
  else if x = 0 ∧ y = 0 then some .infinity
  else
    let xF : Fp := Fin.ofNat _ x
    let yF : Fp := Fin.ofNat _ y
    if Bn254.onCurve xF yF then some (.affine xF yF) else none

/-- Decode a G₂ point from `input[off..off+128)`. Layout matches
    EIP-197: `X.c1 ‖ X.c0 ‖ Y.c1 ‖ Y.c0` (imaginary before real).
    `(0, 0, 0, 0)` decodes to infinity. -/
def decodeG2 (input : ByteArray) (off : Nat) : Option Bn254.G2Point :=
  let x1 := readBE input off          32  -- X.imag
  let x0 := readBE input (off +  32)  32  -- X.real
  let y1 := readBE input (off +  64)  32  -- Y.imag
  let y0 := readBE input (off +  96)  32  -- Y.real
  if x0 ≥ p ∨ x1 ≥ p ∨ y0 ≥ p ∨ y1 ≥ p then none
  else if x0 = 0 ∧ x1 = 0 ∧ y0 = 0 ∧ y1 = 0 then some .infinity
  else
    let X : Fp2Bn := { c0 := Fin.ofNat _ x0, c1 := Fin.ofNat _ x1 }
    let Y : Fp2Bn := { c0 := Fin.ofNat _ y0, c1 := Fin.ofNat _ y1 }
    if G2.onCurve Bn254.g2Curve X Y then some (.affine X Y)
    else none

/-- Decode `k` pairs of `(G₁, G₂)` from `input`. Returns `none` if
    length ≠ multiple of 192 or any coord/on-curve check fails. -/
def decodePairs (input : ByteArray) : Option (List (Bn254.Point × Bn254.G2Point)) := Id.run do
  let sz := input.size
  if sz % 192 ≠ 0 then return none
  let k := sz / 192
  let mut acc : List (Bn254.Point × Bn254.G2Point) := []
  for i in [0:k] do
    let off := i * 192
    match decodeG1 input off, decodeG2 input (off + 64) with
    | some P, some Q => acc := (P, Q) :: acc
    | _, _ => return none
  return some acc.reverse

/-- ECPAIRING core: parse input, validate, compute
    `∏ e(P_i, Q_i)`, and produce the 32-byte boolean output.
    Returns `none` on invalid input (caller maps to `.outOfGas`). -/
def run? (input : ByteArray) : Option ByteArray :=
  match decodePairs input with
  | none => none
  | some pairs =>
    let result := EvmSemantics.Crypto.Pairing.multiPairing pairs
    let isOne := Fp12.eq result Fp12.one
    some (writeBE (if isOne then 1 else 0) 32)

end EvmSemantics.Crypto.Ecpairing
