module

public import EvmSemantics.Crypto.FF
public import Batteries.Tactic.Lint.Misc

/-!
`EvmSemantics.Crypto.Fp2` — the quadratic extension
`F_p² = F_p[u] / (u² + 1)`.

Polymorphic in `p`: the same code serves both BN254 (`p ≈ 2²⁵⁴`) and
BLS12-381 (`p ≈ 2³⁸¹`), because both curves choose the same
irreducible polynomial `u² + 1` (both `p ≡ 3 mod 4`, so `−1` is a
non-residue). Concrete curves supply their own `p` and its
`[NeZero p]` instance.

`Add / Sub / Mul / Neg / Zero / One / OfNat / Inv / HPow α Nat`
typeclass instances are provided so `Pairing.lean` writes
`a * b + c * d` instead of `add (mul a b) (mul c d)`.

Multiplication by the *sextic non-residue* `ξ ∈ Fp2` — the
parameter that generates the `Fp6 = Fp2[v]/(v³ − ξ)` tower above —
lives in the `SexticNonResidue p` typeclass at the bottom of this
file. Each pairing-friendly curve registers its own `ξ` (BN254:
`9 + u`; BLS12-381: `1 + u`), and `Fp6` picks it up implicitly.
-/

@[expose] public section

/-- Element of `F_p² = F_p[u]/(u² + 1)`: `c₀ + c₁·u`. Polymorphic in
    the modulus `p`. -/
structure Fp2 (p : Nat) where
  /-- Real part `c₀ ∈ F_p`. -/
  c0 : Fin p
  /-- Imaginary part `c₁ ∈ F_p` (coefficient of `u`). -/
  c1 : Fin p
  deriving DecidableEq

attribute [nolint dupNamespace] Fp2 Fp2.mk Fp2.c0 Fp2.c1 Fp2.rec

instance {p : Nat} [NeZero p] : Inhabited (Fp2 p) := ⟨{ c0 := 0, c1 := 0 }⟩

namespace Fp2

variable {p : Nat}

/-- Additive identity `0 + 0·u`. -/
@[inline] def zero [NeZero p] : Fp2 p := { c0 := 0, c1 := 0 }

/-- Multiplicative identity `1 + 0·u`. -/
@[inline] def one [NeZero p] : Fp2 p := { c0 := 1, c1 := 0 }

/-- The generator `0 + 1·u`. Useful for encoding curve-specific
    constants like the sextic non-residue `ξ`. -/
@[inline] def u [NeZero p] : Fp2 p := { c0 := 0, c1 := 1 }

/-- Boolean equality: both coefficients must match. -/
@[inline] def eq (a b : Fp2 p) : Bool := a.c0 = b.c0 ∧ a.c1 = b.c1

/-- `a + b`. -/
@[inline] def add (a b : Fp2 p) : Fp2 p :=
  { c0 := a.c0 + b.c0, c1 := a.c1 + b.c1 }

/-- `a − b`. -/
@[inline] def sub (a b : Fp2 p) : Fp2 p :=
  { c0 := a.c0 - b.c0, c1 := a.c1 - b.c1 }

/-- `−a`. -/
@[inline] def neg (a : Fp2 p) : Fp2 p := { c0 := -a.c0, c1 := -a.c1 }

/-- Multiplication in `F_p²`.
    `(a₀ + a₁u)(b₀ + b₁u) = (a₀b₀ − a₁b₁) + (a₀b₁ + a₁b₀)u`
    using `u² = −1`. Karatsuba: 3 base-field muls instead of 4. -/
def mul (a b : Fp2 p) : Fp2 p :=
  let t0 := a.c0 * b.c0
  let t1 := a.c1 * b.c1
  let c0 := t0 - t1
  let s := (a.c0 + a.c1) * (b.c0 + b.c1)
  let c1 := s - t0 - t1
  { c0 := c0, c1 := c1 }

/-- Squaring: `(a₀ + a₁u)² = (a₀² − a₁²) + 2a₀a₁·u`.
    Uses `(a₀ + a₁)(a₀ − a₁)` for the real part to save a multiply. -/
def square (a : Fp2 p) : Fp2 p :=
  let c0 := (a.c0 + a.c1) * (a.c0 - a.c1)
  let c1 := (a.c0 + a.c0) * a.c1
  { c0 := c0, c1 := c1 }

/-- Multiplication by a base-field scalar `k ∈ F_p`. -/
@[inline] def mulByFp (a : Fp2 p) (k : Fin p) : Fp2 p :=
  { c0 := a.c0 * k, c1 := a.c1 * k }

/-- Conjugation `c₀ + c₁·u ↦ c₀ − c₁·u`. Equals the `p`-th power
    (Fp2-Frobenius) because `p ≡ 3 mod 4` ⇒ `u^(p−1) = −1`. -/
@[inline] def conj (a : Fp2 p) : Fp2 p := { c0 := a.c0, c1 := -a.c1 }

/-- Frobenius on `F_p²`: `a ↦ a^p`. Equals conjugation because
    `p ≡ 3 mod 4`. -/
@[inline] def frobenius (a : Fp2 p) : Fp2 p := conj a

/-- Norm `N(a) = a · ā = a₀² + a₁²` (in `Fin p`). -/
@[inline] def norm (a : Fp2 p) : Fin p := a.c0 * a.c0 + a.c1 * a.c1

/-- Inverse via `a⁻¹ = ā / N(a)`. Returns `0` on `a = 0` (matches
    `Fin`'s `Inv` — callers must pre-check when correctness depends). -/
def inv [NeZero p] (a : Fp2 p) : Fp2 p :=
  let ninv := (norm a)⁻¹
  { c0 := a.c0 * ninv, c1 := -a.c1 * ninv }

/-- Multiplication by `u`: `(a₀ + a₁u)·u = −a₁ + a₀·u`. -/
@[inline] def mulByU (a : Fp2 p) : Fp2 p := { c0 := -a.c1, c1 := a.c0 }

/-- Raise `a` to a `Nat` exponent via square-and-multiply. -/
def pow [NeZero p] (a : Fp2 p) (e : Nat) : Fp2 p := Id.run do
  let mut acc : Fp2 p := one
  let mut base := a
  let mut n := e
  while n ≠ 0 do
    if n % 2 = 1 then acc := mul acc base
    base := square base
    n := n / 2
  return acc

end Fp2

----------------------------------------------------------------------------
-- Numeric-tower instances. `x^2` fast-paths to `square`; everything
-- else falls into the generic pow.
----------------------------------------------------------------------------

-- `Fin`'s Add/Sub/Mul/Neg from Lean core don't require `[NeZero p]`,
-- so the same is true here — pure arithmetic works vacuously on
-- `Fp2 0` (which is empty).
@[inline] instance {p : Nat} : Add (Fp2 p) := ⟨Fp2.add⟩
@[inline] instance {p : Nat} : Sub (Fp2 p) := ⟨Fp2.sub⟩
@[inline] instance {p : Nat} : Mul (Fp2 p) := ⟨Fp2.mul⟩
@[inline] instance {p : Nat} : Neg (Fp2 p) := ⟨Fp2.neg⟩
@[inline] instance {p : Nat} [NeZero p] : Zero (Fp2 p) := ⟨Fp2.zero⟩
@[inline] instance {p : Nat} [NeZero p] : One (Fp2 p) := ⟨Fp2.one⟩
@[inline] instance {p : Nat} [NeZero p] : Inv (Fp2 p) := ⟨Fp2.inv⟩

/-- Numeric literals lift into `Fp2 p` via the `c0` slot. -/
@[inline] instance {p n : Nat} [NeZero p] : OfNat (Fp2 p) n :=
  ⟨{ c0 := (OfNat.ofNat n : Fin p), c1 := 0 }⟩

/-- `x ^ n` on `Fp2 p`. Fast-paths `n = 2` to the direct
    `(a+b)(a−b)` squaring formula. -/
@[inline] instance {p : Nat} [NeZero p] : HPow (Fp2 p) Nat (Fp2 p) where
  hPow a n := if n = 2 then Fp2.square a else Fp2.pow a n

----------------------------------------------------------------------------
-- Sextic non-residue: curve-specific, hosted here so `Fp6` (the
-- sextic tower `Fp2[v]/(v³ − ξ)`) can pick it up implicitly.
----------------------------------------------------------------------------

/-- The sextic non-residue `ξ ∈ Fp2` that generates the `Fp6 =
    Fp2[v]/(v³ − ξ)` tower.

    We expose it as multiplication by `ξ` rather than a `ξ` value
    because every curve has a *specialised* formula that's faster
    than a generic `Fp2` multiplication (2 additions for BLS12-381's
    `ξ = 1 + u`; a couple of shifts + additions for BN254's
    `ξ = 9 + u`). Each pairing-friendly curve registers an instance
    with its own `mulByXi`. -/
class SexticNonResidue (p : Nat) [NeZero p] where
  /-- Specialised multiplication by the sextic non-residue `ξ`. -/
  mulByXi : Fp2 p → Fp2 p
