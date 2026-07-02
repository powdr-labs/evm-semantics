module

public import EvmSemantics.Crypto.Secp256r1
public import EvmSemantics.Crypto.Bytes
public import EvmSemantics.Data.Bytes

/-!
`EvmSemantics.Crypto.P256Verify` — secp256r1 (P-256) ECDSA signature
verification, backing EIP-7951's `P256VERIFY` precompile (`0x100`).

Input is `160` bytes = `h ‖ r ‖ s ‖ qx ‖ qy` (each 32-byte big-endian):
the message hash, signature `(r, s)`, and public-key point `(qx, qy)`.
Output is the 32-byte value `1` for a valid signature, or the empty
byte string for an invalid signature / malformed input.
-/

@[expose] public section

namespace EvmSemantics.Crypto.P256Verify

open EvmSemantics.Crypto
open EvmSemantics.Crypto.Secp256r1 (p N Point G)

/-- ECDSA verification on P-256, per EIP-7951. `h r s qx qy` are the raw
    big-endian integers. Returns `true` iff every validity check passes:

    * `0 < r < N` and `0 < s < N`;
    * `0 ≤ qx < p` and `0 ≤ qy < p`;
    * `(qx, qy)` is not the point at infinity (encoded `(0, 0)`);
    * `(qx, qy)` lies on the curve;
    * with `w = s⁻¹ mod N`, `u₁ = h·w mod N`, `u₂ = r·w mod N`, the point
      `R = u₁·G + u₂·Q` is not infinity and `R.x mod N = r`. -/
def verify (h r s qx qy : Nat) : Bool := Id.run do
  -- Signature scalars: 0 < r,s < N.
  if r = 0 ∨ N ≤ r ∨ s = 0 ∨ N ≤ s then return false
  -- Public-key coordinates: 0 ≤ qx,qy < p.
  if p ≤ qx ∨ p ≤ qy then return false
  -- Reject the point at infinity (encoded (0,0)).
  if qx = 0 ∧ qy = 0 then return false
  let qxF : Secp256r1.Fp := Fin.ofNat _ qx
  let qyF : Secp256r1.Fp := Fin.ofNat _ qy
  -- Public key must satisfy the curve equation.
  if !Secp256r1.onCurve qxF qyF then return false
  let Q : Point := .affine qxF qyF
  -- w = s⁻¹ mod N; u₁ = h·w mod N; u₂ = r·w mod N; R = u₁·G + u₂·Q.
  let w := EvmSemantics.Crypto.FF.modInv s N
  let u1 := (h * w) % N
  let u2 := (r * w) % N
  match Secp256r1.scalarMul2 u1 G u2 Q with
  | .infinity   => return false
  | .affine x _ => return x.val % N == r

/-- Run `P256VERIFY` on `input`: parse the five 32-byte big-endian
    fields (input must be exactly 160 bytes) and return the 32-byte
    `1` on a valid signature, else the empty byte string. -/
def run (input : ByteArray) : ByteArray :=
  if input.size == 160 &&
      verify (EvmSemantics.Crypto.Bytes.readBE input 0 32)
             (EvmSemantics.Crypto.Bytes.readBE input 32 32)
             (EvmSemantics.Crypto.Bytes.readBE input 64 32)
             (EvmSemantics.Crypto.Bytes.readBE input 96 32)
             (EvmSemantics.Crypto.Bytes.readBE input 128 32) then
    Data.Bytes.natToBytesPadded 1 32
  else ByteArray.empty

end EvmSemantics.Crypto.P256Verify
