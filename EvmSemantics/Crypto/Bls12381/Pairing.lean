module

public import EvmSemantics.Crypto.EC
public import EvmSemantics.Crypto.Fp2
public import EvmSemantics.Crypto.Fp6
public import EvmSemantics.Crypto.Fp12
public import EvmSemantics.Crypto.G2
public import EvmSemantics.Crypto.Bls12381.Curve

/-!
`EvmSemantics.Crypto.Bls12381Pairing` — BLS12-381 optimal ate
pairing.

Structurally the same as BN254's optimal ate pairing
(`EvmSemantics.Crypto.Pairing`), with two key differences:

* **No Frobenius correction steps.** BLS12-381's Miller loop
  counter is `|u|` (not `6u+2` like BN254), and `u` is a root of
  the modulus polynomial in a way that eliminates the two
  correction adds BN254 needs after the main loop.

* **Negative `u`.** BLS12-381 uses `u = −0xd201000000010000`
  (negative). We iterate the Miller loop over `|u|` and at the end
  invert the accumulator: `f := f⁻¹`. Post final-exp this collapses
  to Fp12 conjugation on the cyclotomic subgroup, so the extra
  inversion is essentially free.

Final exponentiation is the same easy `(p⁶ − 1)(p² + 1)` split
followed by a naive `Fp12.pow` to the hard exponent
`(p⁴ − p² + 1)/N` — same shape as BN254's, different numerator.

The Miller loop bit count is 64 (bit-length of `|u|`), vs BN254's
63 for `6u+2`. Comparable overall Miller-loop cost.
-/

@[expose] public section

namespace EvmSemantics.Crypto.Bls12381Pairing

open EvmSemantics.Crypto.EC
open EvmSemantics.Crypto.G2
open EvmSemantics.Crypto.Bls12381 (p N Fp Fp2 Fp12 Point G2Point)

/-- The Miller-loop counter `|u| = 0xd201000000010000` for BLS12-381,
    where `u` is the (negative) BLS parameter. 64 bits wide, 6 non-
    zero bits (low Hamming weight — the reason BLS curves have
    fast pairings). -/
def ateLoopCount : Nat := EvmSemantics.Crypto.Bls12381.absU

----------------------------------------------------------------------------
-- Fp12 embedding + line-function evaluation.
--
-- Structure copied from `EvmSemantics.Crypto.Pairing` (the BN254
-- version) — the algebra is the same, only the field prime and
-- sextic non-residue change (which are baked into `Fp12`'s
-- typeclass instances).
----------------------------------------------------------------------------

/-- Promote a base-field element `a ∈ F_p` to `F_p¹²`. -/
@[inline] def fp12OfFp (a : Fp) : Fp12 :=
  { c0 := { c0 := { c0 := a, c1 := 0 }, c1 := 0, c2 := 0 }, c1 := 0 }

/-- Promote an `Fp2` element to `Fp12`. -/
@[inline] def fp12OfFp2 (a : Fp2) : Fp12 :=
  { c0 := { c0 := a, c1 := 0, c2 := 0 }, c1 := 0 }

/-- The `w` element of `Fp12`. -/
def w : Fp12 := { c0 := 0, c1 := 1 }

/-- Untwist a `G₂` point `(x', y') ∈ E'(F_p²)` into the isomorphic
    point on `E(F_p¹²)`. BLS12-381 uses an **M-type** twist (`b' = 4·(1+u)`),
    so with the tower `w⁶ = ξ` the untwist is `(x', y') ↦ (x'·w⁻², y'·w⁻³)` —
    the *inverse* powers of `w`. (BN254 is D-type and untwists with `w²`/`w³`;
    the twist type changes the untwist map, not only the coefficient `b'`.)
    Using the D-type map here made the Miller loop non-bilinear, so a genuine
    cross-term pairing check — KZG point-evaluation (0x0A) or a `BLS12_PAIRING`
    with independent operands — failed. -/
def untwist : G2Point → Option (Fp12 × Fp12)
  | .infinity => none
  | .affine x' y' =>
    let w2 := w^2
    let w3 := w2 * w
    some (fp12OfFp2 x' * w2⁻¹, fp12OfFp2 y' * w3⁻¹)

/-- Line function value at `P ∈ G₁` for a Miller step. Same formula
    as BN254 — the algebra doesn't know which curve it's on. -/
def lineFunc (T S : Fp12 × Fp12) (P : Fp12 × Fp12) : Fp12 :=
  let (tx, ty) := T
  let (sx, sy) := S
  let (px, py) := P
  if ¬ Fp12.eq tx sx then
    let m := (sy - ty) * (sx - tx)⁻¹
    m * (px - tx) - (py - ty)
  else if Fp12.eq ty sy then
    let m := (3 * tx^2) * (2 * ty)⁻¹
    m * (px - tx) - (py - ty)
  else
    px - tx

/-- Add two `Fp12`-embedded curve points. -/
def fp12Add (T S : Fp12 × Fp12) : Fp12 × Fp12 :=
  let (tx, ty) := T
  let (sx, sy) := S
  if ¬ Fp12.eq tx sx then
    let m := (sy - ty) * (sx - tx)⁻¹
    let x3 := m^2 - tx - sx
    let y3 := m * (tx - x3) - ty
    (x3, y3)
  else if Fp12.eq ty sy then
    let m := (3 * tx^2) * (2 * ty)⁻¹
    let x3 := m^2 - 2 * tx
    let y3 := m * (tx - x3) - ty
    (x3, y3)
  else
    T

----------------------------------------------------------------------------
-- Miller loop.
----------------------------------------------------------------------------

/-- Miller loop for BLS12-381: `f_{|u|, Q}(P)`, then inverted because
    `u < 0`. -/
def millerLoop (Q : G2Point) (P : Point) : Fp12 :=
  match untwist Q, P with
  | none, _ => 1
  | _, .infinity => 1
  | some Qf, .affine px py => Id.run do
    let Pf : Fp12 × Fp12 := (fp12OfFp px, fp12OfFp py)
    -- Bit width of ateLoopCount (= 64 for BLS12-381).
    let mut bitlen : Nat := 0
    let mut m := ateLoopCount
    while m ≠ 0 do
      bitlen := bitlen + 1
      m := m / 2
    let mut R : Fp12 × Fp12 := Qf
    let mut f : Fp12 := 1
    let mut i := bitlen - 1
    while i ≠ 0 do
      i := i - 1
      f := f^2 * lineFunc R R Pf
      R := fp12Add R R
      if (ateLoopCount >>> i) &&& 1 = 1 then
        f := f * lineFunc R Qf Pf
        R := fp12Add R Qf
    -- BLS12-381's u is negative: invert the accumulator.
    return f⁻¹

----------------------------------------------------------------------------
-- Final exponentiation.
--
-- Same split as BN254: easy `(p⁶ − 1)(p² + 1)` + hard
-- `(p⁴ − p² + 1)/N`. Hard part uses naive `Fp12.pow` (~381 Fp12
-- squarings — noticeably slower than BN254's ~256, since `p` is
-- wider, but the algorithm is identical).
----------------------------------------------------------------------------

/-- BLS12-381 Frobenius `γ` constants. -/
structure Gammas where
  /-- `γ = ξ^((p−1)/6)` — `w`-term multiplier. -/
  γw : Fp2
  /-- `γ² = ξ^((p−1)/3)` — `v`-term multiplier. -/
  γv : Fp2
  /-- `γ⁴` — `v²`-term multiplier. -/
  γv2 : Fp2

/-- Compute BLS12-381 Frobenius constants. -/
def gammas : Gammas :=
  let ξ  : Fp2 := { c0 := 1, c1 := 1 }   -- BLS12-381 ξ = 1 + u
  let γ  := _root_.Fp2.pow ξ ((p - 1) / 6)
  let γ2 := γ^2
  let γ4 := γ2^2
  { γw := γ, γv := γ2, γv2 := γ4 }

/-- Final exponentiation `f ↦ f^((p¹² − 1)/N)` for BLS12-381. -/
def finalExp (f : Fp12) : Fp12 :=
  let step1 := Fp12.conj f * f⁻¹
  let g := gammas
  let frob (x : Fp12) : Fp12 := Fp12.frobenius g.γw g.γv g.γv2 x
  let step2 := frob (frob step1) * step1
  let hardExp := ((p^4) - (p^2) + 1) / N
  step2 ^ hardExp

/-- The full BLS12-381 optimal ate pairing: `e(P, Q) ∈ μ_N ⊂ F_p¹²*`. -/
def pairing (P : Point) (Q : G2Point) : Fp12 :=
  finalExp (millerLoop Q P)

/-- Compute `∏ e(Pᵢ, Qᵢ)` with final exponentiation applied once at
    the end (bilinearity of the Miller loop). -/
def multiPairing (pairs : List (Point × G2Point)) : Fp12 :=
  let miller := pairs.foldl (fun acc (P, Q) => acc * millerLoop Q P) 1
  finalExp miller

end EvmSemantics.Crypto.Bls12381Pairing
