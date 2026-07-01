module

public import EvmSemantics.Crypto.EC
public import EvmSemantics.Crypto.Fp2
public import EvmSemantics.Crypto.Fp6
public import EvmSemantics.Crypto.Fp12
public import EvmSemantics.Crypto.G2
public import EvmSemantics.Crypto.Bn254

/-!
`EvmSemantics.Crypto.Pairing` — BN254 optimal ate pairing.

The optimal ate pairing takes `P ∈ G₁ ⊂ E(F_p)` and
`Q ∈ G₂ ⊂ E'(F_p²)` and produces an element of `μ_N ⊂ F_p¹²*`
(the `N`-th roots of unity). Bilinearity:
`e(a·P, b·Q) = e(P, Q)^(a·b)`.

The precompile (`0x08 ECPAIRING`, EIP-197) reduces the pairing
product `∏ e(Pᵢ, Qᵢ)` to a boolean: `1 iff product = 1 ∈ F_p¹²`.

Algorithm (Vercauteren 2010): the optimal ate pairing on BN254 is
`e(P, Q) = ( f_{6u+2, Q}(P) · ℓ_{[6u+2]Q, π(Q)}(P) · ℓ_{[6u+2]Q + π(Q), −π²(Q)}(P) )^((p¹² − 1)/N)`
where:
* `u = Bn254.u` is the BN254 parameter (`Bn254.p`, `Bn254.N` are
  polynomials in `u`).
* `f_{r, Q}` is the Miller function, computed by a `log₂ r`-length
  double-and-add loop that accumulates line-function values in
  `Fp12 Bn254.p`.
* `π` is the p-power Frobenius on the untwisted point.
* The final power `(p¹² − 1)/N` splits into "easy"
  `(p⁶ − 1)(p² + 1)` (Fp12 conjugation + `frobenius²`) and "hard"
  `(p⁴ − p² + 1)/N` (naive `Fp12.pow`).

Structure follows py_ecc; tower arithmetic (`Fp2 → Fp6 → Fp12`) is
our own, polymorphic in `p` — this module pins everything to
`Bn254.p`.
-/

@[expose] public section

namespace EvmSemantics.Crypto.Pairing

open EvmSemantics.Crypto.EC
open EvmSemantics.Crypto.G2
open EvmSemantics.Crypto.Bn254 (p N Fp)

/-- BN254-specific aliases for the polymorphic tower types. -/
abbrev Fp2Bn := Fp2 p
/-- BN254-specific alias. -/
abbrev Fp6Bn := Fp6 p
/-- BN254-specific alias. -/
abbrev Fp12Bn := Fp12 p

/-- The Miller-loop counter `|6u + 2|` for BN254 — 63 bits wide.
    Decimal value: `29793968203157093288`. -/
def ateLoopCount : Nat := 6*Bn254.u + 2

----------------------------------------------------------------------------
-- Fp12 embedding of G1 / G2 points and line-function evaluation.
--
-- Rather than track sparse structure, we lift everything to Fp12 and
-- run the pairing there. Slower than a sparse implementation but the
-- code is short and unambiguous, which matters more at verification
-- scope than throughput.
----------------------------------------------------------------------------

/-- Promote a base-field element `a ∈ F_p` to `F_p¹²`. -/
@[inline] def fp12OfFp (a : Fp) : Fp12Bn :=
  { c0 := { c0 := { c0 := a, c1 := 0 }, c1 := 0, c2 := 0 }, c1 := 0 }

/-- Promote an `Fp2` element to `Fp12`. -/
@[inline] def fp12OfFp2 (a : Fp2Bn) : Fp12Bn :=
  { c0 := { c0 := a, c1 := 0, c2 := 0 }, c1 := 0 }

/-- The `w` element of `Fp12`, i.e. `0 + 1·w`. -/
def w : Fp12Bn := { c0 := 0, c1 := 1 }

/-- Untwist a `G₂` point `(x', y') ∈ E'(F_p²)` into the isomorphic
    point on `E(F_p¹²)`. Uses `(x', y') ↦ (x'·w², y'·w³)`. -/
def untwist : Bn254.G2Point → Option (Fp12Bn × Fp12Bn)
  | .infinity => none
  | .affine x' y' =>
    let w2 := w^2
    let w3 := w2 * w
    some (fp12OfFp2 x' * w2, fp12OfFp2 y' * w3)

/-- Line function value at `P ∈ G₁` for a Miller step involving points
    `T`, `S` on the twist. Lifts `T`, `S`, `P` all into `Fp12` and
    evaluates the affine line formula. -/
def lineFunc (T S : Fp12Bn × Fp12Bn) (P : Fp12Bn × Fp12Bn) : Fp12Bn :=
  let (tx, ty) := T
  let (sx, sy) := S
  let (px, py) := P
  if ¬ Fp12.eq tx sx then
    let m := (sy - ty) * (sx - tx)⁻¹
    m * (px - tx) - (py - ty)
  else if Fp12.eq ty sy then
    -- Doubling: assumes ty ≠ 0 (caller ensures via T not being ∞).
    let m := (3 * tx^2) * (2 * ty)⁻¹
    m * (px - tx) - (py - ty)
  else
    -- T = -S: vertical line, value px - tx.
    px - tx

/-- Add two `Fp12`-embedded curve points, without the sparse
    optimisation. Uses the affine addition formulas over `Fp12`. -/
def fp12Add (T S : Fp12Bn × Fp12Bn) : Fp12Bn × Fp12Bn :=
  let (tx, ty) := T
  let (sx, sy) := S
  if ¬ Fp12.eq tx sx then
    let m := (sy - ty) * (sx - tx)⁻¹
    let x3 := m^2 - tx - sx
    let y3 := m * (tx - x3) - ty
    (x3, y3)
  else if Fp12.eq ty sy then
    -- Doubling.
    let m := (3 * tx^2) * (2 * ty)⁻¹
    let x3 := m^2 - 2 * tx
    let y3 := m * (tx - x3) - ty
    (x3, y3)
  else
    T

----------------------------------------------------------------------------
-- Miller loop.
----------------------------------------------------------------------------

/-- BN254 Frobenius `γ` constants for Fp12. Cached in a small record. -/
structure Gammas where
  /-- `γ = ξ^((p−1)/6)` — coefficient multiplier for the `w`-term. -/
  γw : Fp2Bn
  /-- `γ² = ξ^((p−1)/3)` — coefficient multiplier for the `v`-term. -/
  γv : Fp2Bn
  /-- `γ⁴` — coefficient multiplier for the `v²`-term. -/
  γv2 : Fp2Bn

/-- Compute BN254 Frobenius constants. -/
def gammas : Gammas :=
  let ξ  : Fp2Bn := { c0 := 9, c1 := 1 }
  let γ  := Fp2.pow ξ ((p - 1) / 6)
  let γ2 := γ^2
  let γ4 := γ2^2
  { γw := γ, γv := γ2, γv2 := γ4 }

/-- Miller loop for BN254: `f_{r, Q}(P)` where `r = 6u+2`. -/
def millerLoop (Q : Bn254.G2Point) (P : Bn254.Point) : Fp12Bn :=
  match untwist Q, P with
  | none, _ => 1
  | _, .infinity => 1
  | some Qf, .affine px py => Id.run do
    let Pf : Fp12Bn × Fp12Bn := (fp12OfFp px, fp12OfFp py)
    let g := gammas
    let frob (x : Fp12Bn) := Fp12.frobenius g.γw g.γv g.γv2 x
    -- Compute bit width of ateLoopCount.
    let mut bitlen : Nat := 0
    let mut m := ateLoopCount
    while m ≠ 0 do
      bitlen := bitlen + 1
      m := m / 2
    -- Main Miller loop, MSB-1 downto 0 (top bit is implicit).
    let mut R : Fp12Bn × Fp12Bn := Qf
    let mut f : Fp12Bn := 1
    let mut i := bitlen - 1
    while i ≠ 0 do
      i := i - 1
      f := f^2 * lineFunc R R Pf
      R := fp12Add R R
      if (ateLoopCount >>> i) &&& 1 = 1 then
        f := f * lineFunc R Qf Pf
        R := fp12Add R Qf
    -- Optimal-ate correction: add π(Q) and −π²(Q).
    let (qx, qy) := Qf
    let Qf1 : Fp12Bn × Fp12Bn := (frob qx, frob qy)
    let Qf2 : Fp12Bn × Fp12Bn := (frob (frob qx), - frob (frob qy))
    f := f * lineFunc R Qf1 Pf
    R := fp12Add R Qf1
    f := f * lineFunc R Qf2 Pf
    return f

----------------------------------------------------------------------------
-- Final exponentiation.
----------------------------------------------------------------------------

/-- Final exponentiation `f ↦ f^((p¹² − 1)/N)`. -/
def finalExp (f : Fp12Bn) : Fp12Bn :=
  -- Easy part 1: f ↦ f^(p⁶ − 1) = frob⁶(f) · f⁻¹ = conj(f) · f⁻¹.
  let step1 := Fp12.conj f * f⁻¹
  -- Easy part 2: step1 ↦ step1^(p² + 1) = frob²(step1) · step1.
  let g := gammas
  let frob (x : Fp12Bn) : Fp12Bn := Fp12.frobenius g.γw g.γv g.γv2 x
  let step2 := frob (frob step1) * step1
  -- Hard part: step2 ↦ step2^((p⁴ − p² + 1)/N).
  let hardExp := ((p^4) - (p^2) + 1) / N
  step2 ^ hardExp

/-- The full BN254 optimal ate pairing: `e(P, Q) ∈ μ_N ⊂ F_p¹²*`. -/
def pairing (P : Bn254.Point) (Q : Bn254.G2Point) : Fp12Bn :=
  finalExp (millerLoop Q P)

/-- Compute `∏ e(Pᵢ, Qᵢ)` with final exponentiation applied once at
    the end (bilinearity of the Miller loop). -/
def multiPairing (pairs : List (Bn254.Point × Bn254.G2Point)) : Fp12Bn :=
  let miller := pairs.foldl (fun acc (P, Q) => acc * millerLoop Q P) 1
  finalExp miller

end EvmSemantics.Crypto.Pairing
