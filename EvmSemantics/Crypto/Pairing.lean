module

public import EvmSemantics.Crypto.EC
public import EvmSemantics.Crypto.Fp2
public import EvmSemantics.Crypto.Fp6
public import EvmSemantics.Crypto.Fp12
public import EvmSemantics.Crypto.G2
public import EvmSemantics.Crypto.Bn254

/-!
`EvmSemantics.Crypto.Pairing` — BN254 optimal ate pairing.

The optimal ate pairing takes `P ∈ G₁ ⊂ E(F_p)` and `Q ∈ G₂ ⊂ E'(F_p²)`
and produces an element of `μ_N ⊂ F_p¹²*` (the `N`-th roots of unity).
Its defining property is bilinearity: `e(a·P, b·Q) = e(P, Q)^(a·b)`.

The precompile (`0x08 ECPAIRING`, EIP-197) reduces the pairing product
`∏ e(P_i, Q_i)` to a boolean: `1 iff product = 1 ∈ F_p¹²`.

Algorithm (Vercauteren 2010): the optimal ate pairing on BN254 is
`e(P, Q) = ( f_{6u+2, Q}(P) · ℓ_{[6u+2]Q, π(Q)}(P) · ℓ_{[6u+2]Q + π(Q), −π²(Q)}(P) )^((p¹² − 1)/N)`
where:
* `u = 4965661367192848881` is the BN254 parameter.
* `f_{r, Q}` is the Miller function, computed by a `log₂ r`-length
  double-and-add loop of doubling+addition steps that accumulate
  line-function values in `F_p¹²`.
* `π` is the "untwisted" p-power Frobenius on the twist.
* The final power `(p¹² − 1)/N` is the "final exponentiation", split
  into an "easy" part `(p⁶ − 1)(p² + 1)` and a "hard" part
  `(p⁴ − p² + 1)/N` (the cyclotomic exponent).

This module is unashamedly translated from py_ecc's reference
implementation — the tricky parts (Miller loop bit pattern,
Frobenius twist maps, cyclotomic exponent decomposition) mirror it
line for line so we can cross-check against known EIP-197 test
vectors.
-/

@[expose] public section

namespace EvmSemantics.Crypto.Pairing

open EvmSemantics.Crypto.EC
open EvmSemantics.Crypto.Fp2
open EvmSemantics.Crypto.Fp6
open EvmSemantics.Crypto.Fp12
open EvmSemantics.Crypto.G2
open EvmSemantics.Crypto.Bn254 (p N)

/-- The Miller-loop counter `|6u + 2|` for BN254 with
    `u = 4965661367192848881`. Bit-length 63. -/
def ateLoopCount : Nat := 29793968203157093288

/-- The BN254 parameter `u`. Used for the final-exponentiation hard
    part. -/
def bnParam : Nat := 4965661367192848881

----------------------------------------------------------------------------
-- Fp12 embedding of G1 / G2 points and line-function evaluation.
--
-- Rather than track sparse structure, we lift everything to Fp12 and
-- run the pairing there. This is ~10× slower than a sparse
-- implementation but the code is short and unambiguous, which
-- matters far more than throughput at verification scope.
----------------------------------------------------------------------------

/-- Promote a base-field scalar `a ∈ F_p` to `F_p¹²`. -/
@[inline] def fp12OfNat (a : Nat) : Fp12 :=
  { c0 := { c0 := { c0 := a, c1 := 0 }, c1 := Fp2.zero, c2 := Fp2.zero },
    c1 := Fp6.zero }

/-- Promote an `Fp2` element to `Fp12`. -/
@[inline] def fp12OfFp2 (a : Fp2) : Fp12 :=
  { c0 := { c0 := a, c1 := Fp2.zero, c2 := Fp2.zero }, c1 := Fp6.zero }

/-- The `w` element of `Fp12`, i.e. `0 + 1·w`. -/
def w : Fp12 :=
  { c0 := Fp6.zero, c1 := Fp6.one }

/-- Untwist a `G₂` point `(x', y') ∈ E'(F_p²)` into the isomorphic
    point on `E(F_p¹²)`. Uses the D-type twist convention
    `(x', y') ↦ (x'·w⁻², y'·w⁻³)` — but since we're keeping arithmetic
    in `Fp12` throughout, we use the *equivalent* embedding
    `(x', y') ↦ (x'·w², y'·w³)` (the pairing formula is invariant
    under this global renormalisation). -/
def untwist : G2.Point → Option (Fp12 × Fp12)
  | .infinity => none
  | .affine x' y' =>
    let w2 := Fp12.square p w
    let w3 := Fp12.mul p w2 w
    some (Fp12.mul p (fp12OfFp2 x') w2, Fp12.mul p (fp12OfFp2 y') w3)

/-- Line function value at `P ∈ G₁` for a Miller step involving points
    `T`, `S` on the twist. Follows the py_ecc formulation: lift `T`,
    `S`, `P` all into `Fp12` and evaluate the affine line formula.

    * If `T ≠ S`: slope `λ = (Sy − Ty)/(Sx − Tx)`; line value is
      `λ·(Px − Tx) − (Py − Ty)`.
    * If `T = S` but `Ty ≠ 0`: doubling slope `λ = 3·Tx² / (2·Ty)`;
      line value as above.
    * Otherwise (vertical tangent): line value is `Px − Tx`. -/
def lineFunc (T S : Fp12 × Fp12) (P : Fp12 × Fp12) : Fp12 :=
  let (tx, ty) := T
  let (sx, sy) := S
  let (px, py) := P
  if ¬ Fp12.eq tx sx then
    let m := Fp12.mul p (Fp12.sub p sy ty) (Fp12.inv p (Fp12.sub p sx tx))
    Fp12.sub p (Fp12.mul p m (Fp12.sub p px tx)) (Fp12.sub p py ty)
  else if Fp12.eq ty sy then
    -- Doubling: assumes ty ≠ 0 (caller ensures this via T not being ∞).
    let three : Fp12 := fp12OfNat 3
    let two   : Fp12 := fp12OfNat 2
    let num := Fp12.mul p three (Fp12.square p tx)
    let den := Fp12.mul p two ty
    let m := Fp12.mul p num (Fp12.inv p den)
    Fp12.sub p (Fp12.mul p m (Fp12.sub p px tx)) (Fp12.sub p py ty)
  else
    -- T = -S: vertical line, value px - tx.
    Fp12.sub p px tx

/-- Add two `Fp12`-embedded curve points, without the sparse
    optimisation. Uses the affine addition formulas over `Fp12`. -/
def fp12Add (T S : Fp12 × Fp12) : Fp12 × Fp12 :=
  let (tx, ty) := T
  let (sx, sy) := S
  if ¬ Fp12.eq tx sx then
    let m := Fp12.mul p (Fp12.sub p sy ty) (Fp12.inv p (Fp12.sub p sx tx))
    let x3 := Fp12.sub p (Fp12.sub p (Fp12.square p m) tx) sx
    let y3 := Fp12.sub p (Fp12.mul p m (Fp12.sub p tx x3)) ty
    (x3, y3)
  else if Fp12.eq ty sy then
    -- Doubling.
    let three : Fp12 := fp12OfNat 3
    let two   : Fp12 := fp12OfNat 2
    let m := Fp12.mul p (Fp12.mul p three (Fp12.square p tx))
                         (Fp12.inv p (Fp12.mul p two ty))
    let x3 := Fp12.sub p (Fp12.square p m) (Fp12.mul p two tx)
    let y3 := Fp12.sub p (Fp12.mul p m (Fp12.sub p tx x3)) ty
    (x3, y3)
  else
    -- Vertical (T + (-T)): the "point at infinity" case. Callers
    -- avoid this in the Miller loop because we're always adding
    -- points that don't produce the identity.
    T

----------------------------------------------------------------------------
-- Miller loop.
----------------------------------------------------------------------------

/-- Raise `ξ ∈ Fp2` to a `Nat` exponent via square-and-multiply. -/
def fp2Pow (a : Fp2) (e : Nat) : Fp2 := Id.run do
  let mut acc : Fp2 := Fp2.one
  let mut base : Fp2 := a
  let mut n := e
  while n ≠ 0 do
    if n % 2 = 1 then acc := Fp2.mul p acc base
    base := Fp2.square p base
    n := n / 2
  return acc

/-- BN254 Frobenius `γ` constants for Fp12. Cached in a small record. -/
structure Gammas where
  /-- `γ = ξ^((p−1)/6)` — coefficient multiplier for the `w`-term. -/
  γw : Fp2
  /-- `γ² = ξ^((p−1)/3)` — coefficient multiplier for the `v`-term. -/
  γv : Fp2
  /-- `γ⁴` — coefficient multiplier for the `v²`-term. -/
  γv2 : Fp2
  deriving Inhabited

/-- Compute BN254 Frobenius constants. -/
def gammas : Gammas :=
  let ξ : Fp2 := { c0 := 9, c1 := 1 }
  let γ := fp2Pow ξ ((p - 1) / 6)
  let γ2 := Fp2.square p γ
  let γ4 := Fp2.square p γ2
  { γw := γ, γv := γ2, γv2 := γ4 }

/-- Miller loop for BN254: `f_{r, Q}(P)` where `r = 6u+2`. Returns an
    `Fp12` element that still needs the final exponentiation to land
    in the pairing target group. Loop is MSB-to-LSB doubling+add over
    the binary expansion of `ateLoopCount`, followed by the two extra
    Frobenius correction steps unique to the optimal ate pairing. -/
def millerLoop (Q : G2.Point) (P : EC.Point) : Fp12 :=
  match untwist Q, P with
  | none, _ => Fp12.one
  | _, .infinity => Fp12.one
  | some Qf, .affine px py => Id.run do
    let Pf : Fp12 × Fp12 := (fp12OfNat px, fp12OfNat py)
    let g := gammas
    let frob (x : Fp12) := Fp12.frobenius p g.γw g.γv g.γv2 x
    -- Compute bit width of ateLoopCount.
    let mut bitlen : Nat := 0
    let mut m := ateLoopCount
    while m ≠ 0 do
      bitlen := bitlen + 1
      m := m / 2
    -- Main Miller loop, MSB-1 downto 0 (top bit is implicit).
    let mut R : Fp12 × Fp12 := Qf
    let mut f : Fp12 := Fp12.one
    let mut i := bitlen - 1
    while i ≠ 0 do
      i := i - 1
      f := Fp12.mul p (Fp12.square p f) (lineFunc R R Pf)
      R := fp12Add R R
      if (ateLoopCount >>> i) &&& 1 = 1 then
        f := Fp12.mul p f (lineFunc R Qf Pf)
        R := fp12Add R Qf
    -- Optimal-ate correction: add π(Q) and −π²(Q).
    let (qx, qy) := Qf
    let Qf1 : Fp12 × Fp12 := (frob qx, frob qy)
    let Qf2 : Fp12 × Fp12 := (frob (frob qx), Fp12.neg p (frob (frob qy)))
    f := Fp12.mul p f (lineFunc R Qf1 Pf)
    R := fp12Add R Qf1
    f := Fp12.mul p f (lineFunc R Qf2 Pf)
    return f

----------------------------------------------------------------------------
-- Final exponentiation.
--
-- Splits (p¹² − 1)/N = (p⁶ − 1)·(p² + 1)·((p⁴ − p² + 1)/N).
-- The first two ("easy" part) use conjugation + Frobenius²; the
-- third ("hard" part) is a chain of multiplications and cyclotomic
-- squarings. For simplicity we implement the hard part by raising
-- to the literal exponent `(p⁴ − p² + 1)/N` via `Fp12.pow`. This is
-- ~256 Fp12 squarings — the naive but obviously correct route.
----------------------------------------------------------------------------

/-- Final exponentiation `f ↦ f^((p¹² − 1)/N)`. -/
def finalExp (f : Fp12) : Fp12 :=
  -- Easy part 1: f ↦ f^(p⁶ − 1) = frob⁶(f) · f⁻¹.
  --   On Fp12 = Fp6[w]/(w²−v), frob⁶ acts as conjugation
  --   (c₀ + c₁w) ↦ (c₀ − c₁w).
  let step1 := Fp12.mul p (Fp12.conj p f) (Fp12.inv p f)
  -- Easy part 2: step1 ↦ step1^(p² + 1) = frob²(step1) · step1.
  let g := gammas
  let frob (x : Fp12) : Fp12 := Fp12.frobenius p g.γw g.γv g.γv2 x
  let step2 := Fp12.mul p (frob (frob step1)) step1
  -- Hard part: step2 ↦ step2^((p⁴ − p² + 1)/N). Direct
  -- square-and-multiply — ~256 Fp12 squarings.
  let hardExp := ((p^4) - (p^2) + 1) / N
  Fp12.pow p step2 hardExp

/-- The full BN254 optimal ate pairing: `e(P, Q) ∈ μ_N ⊂ F_p¹²*`. -/
def pairing (P : EC.Point) (Q : G2.Point) : Fp12 :=
  finalExp (millerLoop Q P)

/-- Compute `∏ e(P_i, Q_i)` without the final exponentiation applied
    to each term — final-exp all at once at the end (bilinearity). -/
def multiPairing (pairs : List (EC.Point × G2.Point)) : Fp12 :=
  let miller := pairs.foldl
    (fun acc (P, Q) => Fp12.mul p acc (millerLoop Q P))
    Fp12.one
  finalExp miller

end EvmSemantics.Crypto.Pairing
