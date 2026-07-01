module

public import EvmSemantics.Crypto.Fp2
public import Batteries.Tactic.Lint.Misc

/-!
`EvmSemantics.Crypto.Fp6` — the sextic tower
`F_p⁶ = F_p²[v] / (v³ − ξ)`.

Polymorphic in `p`; the curve-specific sextic non-residue `ξ` is
pulled in via the `SexticNonResidue p` typeclass (from `Fp2.lean`),
so this module is shared between BN254 (`ξ = 9 + u`) and BLS12-381
(`ξ = 1 + u`) with no per-curve edits.

An element is a triple `(c₀, c₁, c₂)` of `Fp2 p` values representing
`c₀ + c₁·v + c₂·v²`; multiplication reduces via `v³ = ξ`.
-/

@[expose] public section

/-- Element of `F_p⁶ = F_p²[v]/(v³ − ξ)`: `c₀ + c₁·v + c₂·v²`. -/
structure Fp6 (p : Nat) where
  /-- Constant-term coefficient. -/
  c0 : Fp2 p
  /-- `v`-coefficient. -/
  c1 : Fp2 p
  /-- `v²`-coefficient. -/
  c2 : Fp2 p
  deriving DecidableEq

attribute [nolint dupNamespace] Fp6 Fp6.mk Fp6.c0 Fp6.c1 Fp6.c2 Fp6.rec

instance {p : Nat} [NeZero p] : Inhabited (Fp6 p) :=
  ⟨{ c0 := 0, c1 := 0, c2 := 0 }⟩

namespace Fp6

variable {p : Nat}

/-- Additive identity. -/
@[inline] def zero [NeZero p] : Fp6 p := { c0 := 0, c1 := 0, c2 := 0 }

/-- Multiplicative identity. -/
@[inline] def one [NeZero p] : Fp6 p := { c0 := 1, c1 := 0, c2 := 0 }

/-- Boolean equality: all three coefficients must match. -/
@[inline] def eq (a b : Fp6 p) : Bool :=
  Fp2.eq a.c0 b.c0 ∧ Fp2.eq a.c1 b.c1 ∧ Fp2.eq a.c2 b.c2

/-- Componentwise addition. -/
@[inline] def add (a b : Fp6 p) : Fp6 p :=
  { c0 := a.c0 + b.c0, c1 := a.c1 + b.c1, c2 := a.c2 + b.c2 }

/-- Componentwise subtraction. -/
@[inline] def sub (a b : Fp6 p) : Fp6 p :=
  { c0 := a.c0 - b.c0, c1 := a.c1 - b.c1, c2 := a.c2 - b.c2 }

/-- Componentwise negation. -/
@[inline] def neg (a : Fp6 p) : Fp6 p :=
  { c0 := -a.c0, c1 := -a.c1, c2 := -a.c2 }

variable [NeZero p] [SexticNonResidue p]

/-- Multiplication in `F_p⁶` via Karatsuba on the three coefficients.
    `v³ = ξ` folds the schoolbook expansion of
    `(c₀ + c₁v + c₂v²)(d₀ + d₁v + d₂v²)` back to a triple:
    * `r₀ = v₀ + ξ · ((c₁+c₂)(d₁+d₂) − v₁ − v₂)`
    * `r₁ = (c₀+c₁)(d₀+d₁) − v₀ − v₁ + ξ · v₂`
    * `r₂ = (c₀+c₂)(d₀+d₂) − v₀ + v₁ − v₂`
    where `vᵢ = cᵢ · dᵢ`. Six `Fp2` muls total (plus curve-specific
    `mulByXi` from `SexticNonResidue`). -/
def mul (a b : Fp6 p) : Fp6 p :=
  let ξ : Fp2 p → Fp2 p := SexticNonResidue.mulByXi
  let v0 := a.c0 * b.c0
  let v1 := a.c1 * b.c1
  let v2 := a.c2 * b.c2
  let t0 := (a.c1 + a.c2) * (b.c1 + b.c2)
  let t1 := (a.c0 + a.c1) * (b.c0 + b.c1)
  let t2 := (a.c0 + a.c2) * (b.c0 + b.c2)
  { c0 := v0 + ξ (t0 - v1 - v2),
    c1 := (t1 - v0 - v1) + ξ v2,
    c2 := (t2 + v1) - v0 - v2 }

/-- Squaring: schoolbook expansion of `(c₀ + c₁v + c₂v²)²` reduced
    with `v³ = ξ`. -/
def square (a : Fp6 p) : Fp6 p :=
  let ξ : Fp2 p → Fp2 p := SexticNonResidue.mulByXi
  let s0 := a.c0 ^ 2
  let s1 := a.c0 * a.c1
  let s2 := a.c1 * a.c2
  let s3 := a.c1 ^ 2
  let s4 := a.c0 * a.c2
  let s5 := a.c2 ^ 2
  { c0 := s0 + ξ (s2 + s2),
    c1 := (s1 + s1) + ξ s5,
    c2 := (s4 + s4) + s3 }

/-- Multiplication by a base-field element `k ∈ F_p²`. -/
@[inline] def mulByFp2 (a : Fp6 p) (k : Fp2 p) : Fp6 p :=
  { c0 := a.c0 * k, c1 := a.c1 * k, c2 := a.c2 * k }

/-- Multiplication by `v`: `(c₀ + c₁v + c₂v²)·v = ξ·c₂ + c₀·v + c₁·v²`. -/
@[inline] def mulByV (a : Fp6 p) : Fp6 p :=
  { c0 := SexticNonResidue.mulByXi a.c2, c1 := a.c0, c2 := a.c1 }

/-- Multiplication by a sparse `(b₀ + b₁·v)` (i.e. `c₂ = 0`). Used
    for pairing line functions; saves one Fp2 mul over the general
    path. -/
def mulBy01 (a : Fp6 p) (b0 b1 : Fp2 p) : Fp6 p :=
  let ξ : Fp2 p → Fp2 p := SexticNonResidue.mulByXi
  let a_a := a.c0 * b0
  let b_b := a.c1 * b1
  let t1  := b0 + b1
  { c0 := ξ ((a.c1 + a.c2) * b1 - b_b) + a_a,
    c1 := t1 * (a.c0 + a.c1) - a_a - b_b,
    c2 := (a.c0 + a.c2) * b0 - a_a + b_b }

/-- Inverse via the adjugate formula. -/
def inv (a : Fp6 p) : Fp6 p :=
  let ξ : Fp2 p → Fp2 p := SexticNonResidue.mulByXi
  let t0 := a.c0 ^ 2
  let t1 := a.c1 ^ 2
  let t2 := a.c2 ^ 2
  let t3 := a.c0 * a.c1
  let t4 := a.c0 * a.c2
  let t5 := a.c1 * a.c2
  let c0' := t0 - ξ t5
  let c1' := ξ t2 - t3
  let c2' := t1 - t4
  let n := a.c0 * c0' + ξ (a.c2 * c1' + a.c1 * c2')
  let ninv := Fp2.inv n
  { c0 := c0' * ninv, c1 := c1' * ninv, c2 := c2' * ninv }

/-- Raise `a` to a `Nat` exponent via square-and-multiply. -/
def pow (a : Fp6 p) (e : Nat) : Fp6 p := Id.run do
  let mut acc : Fp6 p := one
  let mut base := a
  let mut n := e
  while n ≠ 0 do
    if n % 2 = 1 then acc := mul acc base
    base := square base
    n := n / 2
  return acc

end Fp6

@[inline] instance {p : Nat} : Add (Fp6 p) := ⟨Fp6.add⟩
@[inline] instance {p : Nat} : Sub (Fp6 p) := ⟨Fp6.sub⟩
@[inline] instance {p : Nat} [NeZero p] [SexticNonResidue p] :
    Mul (Fp6 p) := ⟨Fp6.mul⟩
@[inline] instance {p : Nat} : Neg (Fp6 p) := ⟨Fp6.neg⟩
@[inline] instance {p : Nat} [NeZero p] : Zero (Fp6 p) := ⟨Fp6.zero⟩
@[inline] instance {p : Nat} [NeZero p] : One (Fp6 p) := ⟨Fp6.one⟩

/-- Numeric literals lift through the constant Fp2 coefficient. -/
@[inline] instance {p n : Nat} [NeZero p] : OfNat (Fp6 p) n :=
  ⟨{ c0 := (OfNat.ofNat n : Fp2 p), c1 := 0, c2 := 0 }⟩

/-- `x ^ n` on `Fp6 p`. Fast-paths `n = 2` to the direct squaring. -/
@[inline] instance {p : Nat} [NeZero p] [SexticNonResidue p] :
    HPow (Fp6 p) Nat (Fp6 p) where
  hPow a n := if n = 2 then Fp6.square a else Fp6.pow a n
