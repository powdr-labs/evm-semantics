module

public import EvmSemantics.Crypto.Fp6
public import Batteries.Tactic.Lint.Misc

/-!
`EvmSemantics.Crypto.Fp12` — the twelfth extension
`F_p¹² = F_p⁶[w] / (w² − v)`.

Polymorphic in `p`. An `Fp12 p` element is a pair `(c₀, c₁)` of
`Fp6 p` values representing `c₀ + c₁·w`. Multiplication reduces
with `w² = v`. This is the target field of the optimal-ate pairing
for both BN254 and BLS12-381.

The sextic non-residue `ξ` only shows up transitively through
`Fp6.mulByV` (which multiplies by `ξ` on the constant slot), so
`Fp12` itself doesn't need to reference `SexticNonResidue` in its
body — the class is threaded through `Fp6`'s constraints.
-/

@[expose] public section

/-- Element of `F_p¹² = F_p⁶[w]/(w² − v)`: `c₀ + c₁·w`. -/
structure Fp12 (p : Nat) where
  /-- Constant-term Fp6 coefficient. -/
  c0 : Fp6 p
  /-- `w`-coefficient. -/
  c1 : Fp6 p
  deriving DecidableEq

attribute [nolint dupNamespace] Fp12 Fp12.mk Fp12.c0 Fp12.c1 Fp12.rec

instance {p : Nat} [NeZero p] : Inhabited (Fp12 p) :=
  ⟨{ c0 := ⟨0, 0, 0⟩, c1 := ⟨0, 0, 0⟩ }⟩

namespace Fp12

variable {p : Nat}

/-- Additive identity. -/
@[inline] def zero [NeZero p] : Fp12 p := { c0 := 0, c1 := 0 }

/-- Multiplicative identity `1 + 0·w`. -/
@[inline] def one [NeZero p] : Fp12 p := { c0 := 1, c1 := 0 }

/-- Boolean equality. -/
@[inline] def eq (a b : Fp12 p) : Bool := Fp6.eq a.c0 b.c0 ∧ Fp6.eq a.c1 b.c1

/-- Componentwise addition. -/
@[inline] def add (a b : Fp12 p) : Fp12 p :=
  { c0 := a.c0 + b.c0, c1 := a.c1 + b.c1 }

/-- Componentwise subtraction. -/
@[inline] def sub (a b : Fp12 p) : Fp12 p :=
  { c0 := a.c0 - b.c0, c1 := a.c1 - b.c1 }

/-- Componentwise negation. -/
@[inline] def neg (a : Fp12 p) : Fp12 p := { c0 := -a.c0, c1 := -a.c1 }

variable [NeZero p] [SexticNonResidue p]

/-- Multiplication via Karatsuba on the two `Fp6` coefficients.
    `(c₀ + c₁w)(d₀ + d₁w) = (c₀d₀ + v·c₁d₁) + ((c₀+c₁)(d₀+d₁) − c₀d₀ − c₁d₁)w`.
    Three `Fp6` multiplications. -/
def mul (a b : Fp12 p) : Fp12 p :=
  let v0 := a.c0 * b.c0
  let v1 := a.c1 * b.c1
  let t  := (a.c0 + a.c1) * (b.c0 + b.c1)
  { c0 := v0 + Fp6.mulByV v1,
    c1 := t - v0 - v1 }

/-- Complex squaring: `(c₀ + c₁w)² = (c₀ + c₁)(c₀ + v·c₁) − c₀·c₁ − v·c₀·c₁`.
    2 Fp6 muls. -/
def square (a : Fp12 p) : Fp12 p :=
  let ab := a.c0 * a.c1
  let c0PlusC1 := a.c0 + a.c1
  let c0PlusVC1 := a.c0 + Fp6.mulByV a.c1
  let t := c0PlusC1 * c0PlusVC1
  { c0 := t - ab - Fp6.mulByV ab,
    c1 := ab + ab }

/-- Fp12-conjugation `(c₀ + c₁w) ↦ (c₀ − c₁w)`. On the cyclotomic
    subgroup this equals the inverse — no field division needed. -/
@[inline] def conj (a : Fp12 p) : Fp12 p := { c0 := a.c0, c1 := -a.c1 }

/-- General inverse via `1/(c₀ + c₁w) = (c₀ − c₁w) / (c₀² − v·c₁²)`. -/
def inv (a : Fp12 p) : Fp12 p :=
  let t0 := a.c0 ^ 2
  let t1 := a.c1 ^ 2
  let n := t0 - Fp6.mulByV t1
  let ni := Fp6.inv n
  { c0 := a.c0 * ni, c1 := -(a.c1 * ni) }

/-- Exponentiate by a `Nat` scalar via square-and-multiply. -/
def pow (a : Fp12 p) (e : Nat) : Fp12 p := Id.run do
  let mut acc : Fp12 p := one
  let mut base := a
  let mut n := e
  while n ≠ 0 do
    if n % 2 = 1 then acc := mul acc base
    base := square base
    n := n / 2
  return acc

/-- Frobenius on `Fp12 p`. Requires the curve's γ constants (Fp2
    elements):
    * `γw = ξ^((p−1)/6)`  — `w`-term multiplier.
    * `γv = ξ^((p−1)/3) = γw²` — `v`-term (Fp6 layer).
    * `γv² = ξ^(2(p−1)/3) = γw⁴` — `v²`-term. -/
def frobenius (γw γv γv2 : Fp2 p) (a : Fp12 p) : Fp12 p :=
  let frob6 (x : Fp6 p) : Fp6 p :=
    { c0 := Fp2.conj x.c0,
      c1 := γv * Fp2.conj x.c1,
      c2 := γv2 * Fp2.conj x.c2 }
  { c0 := frob6 a.c0,
    c1 := Fp6.mulByFp2 (frob6 a.c1) γw }

/-- Sparse multiplication: `a` × a pairing-line element of shape
    `(b0, 0, 0) + (b1, b4, 0)·w`. Used inside Miller's loop. -/
def mulBy014 (a : Fp12 p) (b0 b1 b4 : Fp2 p) : Fp12 p :=
  let a0b0 : Fp6 p := Fp6.mulByFp2 a.c0 b0
  let a1b1 : Fp6 p := Fp6.mulBy01 a.c1 b1 b4
  let sum := Fp6.mulBy01 (a.c0 + a.c1) (b0 + b1) b4
  { c0 := a0b0 + Fp6.mulByV a1b1,
    c1 := sum - a0b0 - a1b1 }

end Fp12

@[inline] instance {p : Nat} : Add (Fp12 p) := ⟨Fp12.add⟩
@[inline] instance {p : Nat} : Sub (Fp12 p) := ⟨Fp12.sub⟩
@[inline] instance {p : Nat} [NeZero p] [SexticNonResidue p] :
    Mul (Fp12 p) := ⟨Fp12.mul⟩
@[inline] instance {p : Nat} : Neg (Fp12 p) := ⟨Fp12.neg⟩
@[inline] instance {p : Nat} [NeZero p] : Zero (Fp12 p) := ⟨Fp12.zero⟩
@[inline] instance {p : Nat} [NeZero p] : One (Fp12 p) := ⟨Fp12.one⟩
@[inline] instance {p : Nat} [NeZero p] [SexticNonResidue p] :
    Inv (Fp12 p) := ⟨Fp12.inv⟩

/-- Numeric literals lift through the constant Fp6 coefficient. -/
@[inline] instance {p n : Nat} [NeZero p] : OfNat (Fp12 p) n :=
  ⟨{ c0 := (OfNat.ofNat n : Fp6 p), c1 := 0 }⟩

/-- `x ^ n`. Fast-paths `n = 2` to `square` (2 Fp6 muls) vs the
    generic pow (which would do an extra wasted square). -/
@[inline] instance {p : Nat} [NeZero p] [SexticNonResidue p] :
    HPow (Fp12 p) Nat (Fp12 p) where
  hPow a n := if n = 2 then Fp12.square a else Fp12.pow a n
