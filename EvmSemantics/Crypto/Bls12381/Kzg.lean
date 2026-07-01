module

public import EvmSemantics.Crypto.Bls12381.Curve
public import EvmSemantics.Crypto.Bls12381.Pairing
public import EvmSemantics.Crypto.Bls12381.G1Add
public import EvmSemantics.Crypto.Bls12381.MapFp2ToG2
public import EvmSemantics.Crypto.Sha256
public import EvmSemantics.Data.Bytes
public import EvmSemantics.Crypto.FF

/-!
`EvmSemantics.Crypto.BlsKzg` — EIP-4844 `0x0A` KZG point-evaluation
precompile.

Wire format (192 bytes in, 64 bytes out):

* `input[0:32]`    versioned hash `h`. Must equal
                   `0x01 ‖ sha256(commitment)[1:]`.
* `input[32:64]`   evaluation point `z` (Fr scalar mod BLS_MODULUS).
* `input[64:96]`   claimed value `y = f(z)`.
* `input[96:144]`  commitment `C` (48-byte compressed G₁).
* `input[144:192]` opening proof `π` (48-byte compressed G₁).

Verification (KZG10):
`e(π, [τ]G₂ − [z]G₂) · e([y]G₁ − C, G₂) = 1`
where `[τ]G₂` is the Ethereum KZG-ceremony trusted-setup point.

Output on success: 64 bytes = `FIELD_ELEMENTS_PER_BLOB (=4096)`
big-endian ‖ `BLS_MODULUS (=N)` big-endian.

Gas: flat 50000 (EIP-4844). Invalid input → `.outOfGas`.

The `[τ]G₂` point is decompressed once at module load from the
mainnet trusted-setup file
(`c-kzg-4844/src/trusted_setup.txt` line 4100, the 2nd G₂ point =
setup[1]). Requires an Fp2 square-root — we reuse the ETAS/8th-
roots dance from `Bls12381MapFp2ToG2`.
-/

@[expose] public section

namespace EvmSemantics.Crypto.BlsKzg

open EvmSemantics.Crypto.Bls12381
  (p N Fp Fp2 Point G2Point G addPoint scalarMul g2Curve)
open EvmSemantics.Crypto.G2 (negate)
open EvmSemantics.Crypto.Bls12381Pairing (multiPairing)
open EvmSemantics.Crypto.Bls12381MapFp2ToG2
  (pSqMinus9Div16 positiveEighthRoots etas)
open EvmSemantics.Data.Bytes (bytesToBigEndianNat natToBytesPadded)

/-! ## Compressed-G₁ decoding. -/

/-- G₁ compressed encoding: 48 bytes = `x` in `[0, p)` with top 3
    bits used for metadata:
    * bit 7 (0x80): compression flag (always 1 for compressed).
    * bit 6 (0x40): infinity flag.
    * bit 5 (0x20): sign of `y` (1 = larger of the two roots).
    Decompression solves `y² = x³ + 4` and picks the correct root. -/
def decompressG1 (bs : ByteArray) (off : Nat) : Option Point := do
  if off + 48 > bs.size then none
  else
    let b0 := bs[off]!
    let compressed := b0 &&& 0x80 ≠ 0
    let isInf     := b0 &&& 0x40 ≠ 0
    let signY     := b0 &&& 0x20 ≠ 0
    if ¬ compressed then none
    else if isInf then some .infinity
    else
      -- Strip metadata bits from byte 0, then read x as big-endian.
      let mut buf : ByteArray := ByteArray.empty
      buf := buf.push (b0 &&& 0x1F)
      for i in [1:48] do buf := buf.push bs[off + i]!
      let x := bytesToBigEndianNat buf
      if x ≥ p then none
      else
        let xF : Fp := Fin.ofNat _ x
        let rhs := xF^3 + 4                         -- y² = x³ + 4
        let y0 := Fin.ofNat _ (EvmSemantics.Crypto.FF.modSqrt rhs.val p)
        if y0 * y0 ≠ rhs then none
        else
          -- y0.val is the smaller root when val < p/2, larger otherwise.
          let ySmaller : Bool := y0.val * 2 < p
          let y : Fp := if signY = ¬ ySmaller then y0 else -y0
          some (.affine xF y)

/-! ## Fp2 square root via ETAS. -/

/-- Try to find `s ∈ Fp2` with `s² = t`. Returns `some s` if `t` is
    a square, `none` otherwise. Uses the same ETAS dance as
    `Bls12381MapFp2ToG2.sswuG2`. -/
def fp2Sqrt (t : Fp2) : Option Fp2 :=
  let cand := Fp2.pow t pSqMinus9Div16 * t
  positiveEighthRoots.foldl
    (fun acc root =>
      match acc with
      | some _ => acc
      | none   =>
        let s := root * cand
        if s * s = t then some s else none) none
    |> fun r =>
      match r with
      | some _ => r
      | none =>
        etas.foldl
          (fun acc η =>
            match acc with
            | some _ => acc
            | none   =>
              let s := η * cand
              if s * s = t then some s else none) none

/-- Compressed-G₂ decoding: 96 bytes. Bytes are `x.c1 ‖ x.c0`, with
    the same 3 metadata bits at the top of byte 0 as for G₁. -/
def decompressG2 (bs : ByteArray) (off : Nat) : Option G2Point := do
  if off + 96 > bs.size then none
  else
    let b0 := bs[off]!
    let compressed := b0 &&& 0x80 ≠ 0
    let isInf     := b0 &&& 0x40 ≠ 0
    let signY     := b0 &&& 0x20 ≠ 0
    if ¬ compressed then none
    else if isInf then some .infinity
    else
      let mut buf1 : ByteArray := ByteArray.empty
      buf1 := buf1.push (b0 &&& 0x1F)
      for i in [1:48] do buf1 := buf1.push bs[off + i]!
      let x_c1 := bytesToBigEndianNat buf1
      let x_c0 := bytesToBigEndianNat (bs.extract (off + 48) (off + 96))
      if x_c0 ≥ p ∨ x_c1 ≥ p then none
      else
        let x : Fp2 := { c0 := Fin.ofNat _ x_c0, c1 := Fin.ofNat _ x_c1 }
        let rhs := x^2 * x + { c0 := Fin.ofNat _ 4, c1 := Fin.ofNat _ 4 }  -- y² = x³ + 4(1+u)
        match fp2Sqrt rhs with
        | none => none
        | some y0 =>
          let ySmaller : Bool := y0.c1.val * 2 < p ||
            (y0.c1.val = 0 && y0.c0.val * 2 < p)
          let y : Fp2 := if signY = ¬ ySmaller then y0 else -y0
          some (.affine x y)

/-! ## Trusted-setup point `[τ]G₂` from Ethereum's KZG ceremony. -/

/-- The compressed `[τ]G₂` from `c-kzg-4844/src/trusted_setup.txt`
    line 4100 (i.e. `setup[1]` in the G₂ list, since `setup[0] = G₂`
    itself). Format: `x.c1 ‖ x.c0` (48 + 48 = 96 bytes) with 3
    metadata bits at the top of byte 0. -/
def tauG2Compressed : ByteArray := Id.run do
  -- Hex-encoded 96 bytes:
  -- b5bfd7dd8cdeb128843bc287230af38926187075cbfbefa81009a2ce615ac53d2914e5870cb452d2afaaab24f3499f72
  -- 185cbfee53492714734429b7b38608e23926c911cceceac9a36851477ba4c60b087041de621000edc98edada20c1def2
  let hex :=
    "b5bfd7dd8cdeb128843bc287230af38926187075cbfbefa81009a2ce615ac53d2914e5870cb452d2afaaab24f3499f72" ++
    "185cbfee53492714734429b7b38608e23926c911cceceac9a36851477ba4c60b087041de621000edc98edada20c1def2"
  let mut acc : ByteArray := ByteArray.empty
  let hexArr := hex.toList.toArray
  for i in [0:96] do
    let h1 : Char := hexArr[2*i]!
    let h2 : Char := hexArr[2*i + 1]!
    let nib1 := if h1.toNat ≤ '9'.toNat then h1.toNat - '0'.toNat
                else h1.toNat - 'a'.toNat + 10
    let nib2 := if h2.toNat ≤ '9'.toNat then h2.toNat - '0'.toNat
                else h2.toNat - 'a'.toNat + 10
    acc := acc.push (UInt8.ofNat (nib1 * 16 + nib2))
  return acc

/-- The `[τ]G₂` trusted-setup point, decompressed at module load. -/
def tauG2 : G2Point :=
  (decompressG2 tauG2Compressed 0).getD .infinity

/-! ## KZG verification. -/

/-- G₂ scalar multiplication. -/
def scalarMulG2 (k : Nat) (Q : G2Point) : G2Point := Id.run do
  let mut R : G2Point := .infinity
  let mut base := Q
  let mut e := k
  while e ≠ 0 do
    if e % 2 = 1 then R := G2.addPoint R base
    base := G2.addPoint base base
    e := e / 2
  return R

/-- KZG opening verification.

    Given `commitment C`, `proof π`, evaluation point `z ∈ Fr`,
    claimed value `y ∈ Fr`, check
    `e(C − [y]G₁, G₂) · e(−π, [τ]G₂ − [z]G₂) = 1`
    which is equivalent to the KZG opening identity. -/
def verifyKzg (C π : Point) (z y : Nat) : Bool :=
  let yG₁ := scalarMul y G
  let cMinusYG := addPoint C (match yG₁ with
                              | .infinity => .infinity
                              | .affine x y => .affine x (-y))
  let zG₂ := scalarMulG2 z EvmSemantics.Crypto.Bls12381.G2
  let tauMinusZG₂ := G2.addPoint tauG2 (negate zG₂)
  let negπ := match π with
              | .infinity => .infinity
              | .affine x y => .affine x (-y)
  let pairs : List (Point × G2Point) :=
    [ (cMinusYG, EvmSemantics.Crypto.Bls12381.G2),
      (negπ, tauMinusZG₂) ]
  multiPairing pairs = 1

/-- FIELD_ELEMENTS_PER_BLOB and BLS_MODULUS as EIP-4844's canonical
    success output. -/
def successOutput : ByteArray :=
  natToBytesPadded 4096 32 ++ natToBytesPadded N 32

/-- Run the `0x0A` KZG point evaluation precompile. -/
def run? (input : ByteArray) : Option ByteArray := do
  if input.size ≠ 192 then none
  else
    let versionedHash := input.extract 0 32
    let z := bytesToBigEndianNat (input.extract 32 64)
    let y := bytesToBigEndianNat (input.extract 64 96)
    let commitmentBytes := input.extract 96 144
    -- versioned_hash = 0x01 || sha256(commitment)[1:]
    let h := EvmSemantics.Crypto.Sha256.hash commitmentBytes
    if h.size ≠ 32 then none
    else
      let expected : ByteArray := Id.run do
        let mut acc : ByteArray := ByteArray.empty
        acc := acc.push 0x01
        for i in [1:32] do acc := acc.push h[i]!
        return acc
      if versionedHash ≠ expected then none
      else if z ≥ N ∨ y ≥ N then none
      else
        let C ← decompressG1 input 96
        let π ← decompressG1 input 144
        if verifyKzg C π z y then some successOutput else none

end EvmSemantics.Crypto.BlsKzg
