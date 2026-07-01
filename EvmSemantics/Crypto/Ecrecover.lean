module

public import EvmSemantics.Crypto.Secp256k1
public import EvmSemantics.Crypto.Keccak256
public import EvmSemantics.Crypto.Bytes

/-!
`EvmSemantics.Crypto.Ecrecover` — the ECDSA public-key recovery used by
Ethereum's `0x01 ECRECOVER` precompile.

Given a 32-byte message hash `h`, a recovery id `v ∈ {27, 28}` and the
signature components `(r, s)`, return the 20-byte Ethereum address of
the signer — or the empty byte-string on any validation failure
(malformed `v`, `r` / `s` out of range, non-recoverable point).

Recovery formula (RFC 6979 / SEC 1 §4.1.6):

1. Reject unless `v ∈ {27, 28}` (Ethereum's convention: `v − 27` is
   the point's `y`-parity bit, aka the recovery id).
2. Reject unless `r ∈ [1, N−1]` and `s ∈ [1, N−1]`.
3. Recover the curve point `R` whose `x`-coord is `r` and whose
   `y`-parity matches `v − 27`. Fail if no such point exists (`x³ + 7`
   is not a quadratic residue mod `p`).
4. Interpret `h` as a `Nat` in big-endian and reduce mod `N` — call it
   `e`.
5. Let `r⁻¹` be `r`'s inverse mod `N`. Then the recovered public key
   is `Q = r⁻¹ · (s·R − e·G)`.
6. If `Q = ∞`, fail.
7. The address is the low 20 bytes of `keccak256(Q.x || Q.y)` (64
   bytes big-endian).

The precompile pads the resulting address to 32 bytes with 12 leading
zeros; failure returns the empty byte-string (`ByteArray.empty`) so
the CALL-family caller sees `returnData.size = 0`.
-/

@[expose] public section

namespace EvmSemantics.Crypto.Ecrecover

open EvmSemantics.Crypto.EC
open EvmSemantics.Crypto.FF (modMul modNeg modInv)
open EvmSemantics.Crypto.Secp256k1
open EvmSemantics.Crypto.Bytes

/-- Zero-pad the 20-byte address into a 32-byte precompile output
    (12 leading zeros). -/
def padAddress (addr20 : ByteArray) : ByteArray := Id.run do
  let mut acc : ByteArray := ByteArray.empty
  for _ in [0:12] do acc := acc.push 0
  acc ++ addr20

/-- The ECRECOVER core. Takes the 4 field/scalar inputs already
    reduced (or trivially bounded) and returns `some address` on
    success, `none` on any validation or recovery failure. -/
def recoverAddress (h v r s : Nat) : Option ByteArray := do
  -- Ethereum's v-convention: 27 = even-y R, 28 = odd-y R.
  if v ≠ 27 ∧ v ≠ 28 then none
  else if r = 0 ∨ r ≥ N then none
  else if s = 0 ∨ s ≥ N then none
  else
    -- Recover R by decompressing (r, yOdd = v==28).
    let R ← decompress (FF.ofNat r) (v = 28)
    -- e = h mod N.
    let e := h % N
    let rInv := modInv r N
    -- Q = r⁻¹ · (s · R − e · G) = r⁻¹·s·R + r⁻¹·(−e)·G
    let u1 := modMul (modNeg e N) rInv N
    let u2 := modMul s rInv N
    match scalarMul2 u1 G u2 R with
    | .infinity => none
    | .affine qx qy =>
      -- Address = keccak256(qx ‖ qy)[12:32]. `.val` peels the FF
      -- wrapper back to a Nat so we can serialise the 32-byte words.
      let preimage := writeBE qx.val 32 ++ writeBE qy.val 32
      let digest := Keccak.hash preimage
      -- Take the last 20 bytes.
      let mut addr : ByteArray := ByteArray.empty
      for i in [12:32] do addr := addr.push digest[i]!
      some (padAddress addr)

/-- Precompile-shaped ECRECOVER: parses the 128-byte call input into
    `(h, v, r, s)`, returns the 32-byte padded address on success and
    `ByteArray.empty` on failure (matching YP §9.4.1: a failed recovery
    yields empty return-data, not an error).

    Input longer than 128 bytes is truncated; shorter input is
    zero-padded (handled by `readBE`). -/
def run (input : ByteArray) : ByteArray :=
  let h := readBE input 0 32
  let v := readBE input 32 32
  let r := readBE input 64 32
  let s := readBE input 96 32
  match recoverAddress h v r s with
  | some out => out
  | none     => ByteArray.empty

end EvmSemantics.Crypto.Ecrecover
