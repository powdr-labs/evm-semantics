module

public import EvmSemantics.Crypto.Bn254
public import Batteries.Tactic.Lint.Misc

/-!
`EvmSemantics.Crypto.Fp2` — the quadratic extension `F_p² = F_p[u]/(u² + 1)`
for BN254.

BN254's `p ≡ 3 mod 4` guarantees `u² + 1` is irreducible over `F_p`,
so this is a field. Elements are `c₀ + c₁·u` with both coefficients
in `Bn254.Fp` — the modulus is baked into the coefficient type, so
`Fp2.mul a b` doesn't need to thread a `p` at runtime.

`Add / Sub / Mul / Neg / Zero / One / OfNat / HPow α Nat` typeclass
instances are provided so `Pairing.lean` writes `a * b + c * d`
instead of `add (mul a b) (mul c d)`.

Sparse multiplications (`mulByXi`, `mulByU`) and per-op specialised
squaring stay as named functions because they're faster than the
generic `*`.
-/

@[expose] public section

namespace EvmSemantics.Crypto.Fp2

open EvmSemantics.Crypto.Bn254 (Fp)

/-- Element of `F_p² = F_p[u]/(u² + 1)`: `c₀ + c₁·u`. -/
structure Fp2 where
  /-- Real part `c₀ ∈ F_p`. -/
  c0 : Fp
  /-- Imaginary part `c₁ ∈ F_p` (coefficient of `u`). -/
  c1 : Fp
  deriving Inhabited, DecidableEq

attribute [nolint dupNamespace] Fp2 Fp2.mk Fp2.c0 Fp2.c1 Fp2.rec

/-- Additive identity `0 + 0·u`. -/
@[inline] def zero : Fp2 := { c0 := 0, c1 := 0 }

/-- Multiplicative identity `1 + 0·u`. -/
@[inline] def one : Fp2 := { c0 := 1, c1 := 0 }

/-- The generator `0 + 1·u`. Useful for encoding constants like the
    sextic-twist parameter `ξ = 9 + u`. -/
@[inline] def u : Fp2 := { c0 := 0, c1 := 1 }

/-- Boolean equality: both coefficients must match. -/
@[inline] def eq (a b : Fp2) : Bool := a.c0 = b.c0 ∧ a.c1 = b.c1

/-- `a + b`. -/
@[inline] def add (a b : Fp2) : Fp2 := { c0 := a.c0 + b.c0, c1 := a.c1 + b.c1 }

/-- `a − b`. -/
@[inline] def sub (a b : Fp2) : Fp2 := { c0 := a.c0 - b.c0, c1 := a.c1 - b.c1 }

/-- `−a`. -/
@[inline] def neg (a : Fp2) : Fp2 := { c0 := -a.c0, c1 := -a.c1 }

/-- Multiplication in `F_p²`.
    `(a₀ + a₁u)(b₀ + b₁u) = (a₀b₀ − a₁b₁) + (a₀b₁ + a₁b₀)u`
    using `u² = −1`. Karatsuba: 3 base-field muls instead of 4. -/
def mul (a b : Fp2) : Fp2 :=
  let t0 := a.c0 * b.c0
  let t1 := a.c1 * b.c1
  let c0 := t0 - t1
  let s := (a.c0 + a.c1) * (b.c0 + b.c1)
  let c1 := s - t0 - t1
  { c0 := c0, c1 := c1 }

/-- Squaring: `(a₀ + a₁u)² = (a₀² − a₁²) + 2a₀a₁·u`.
    Uses `(a₀ + a₁)(a₀ − a₁)` for the real part to save a multiply. -/
def square (a : Fp2) : Fp2 :=
  let c0 := (a.c0 + a.c1) * (a.c0 - a.c1)
  let c1 := (a.c0 + a.c0) * a.c1
  { c0 := c0, c1 := c1 }

/-- Multiplication by a base-field scalar `k ∈ F_p`. -/
@[inline] def mulByFp (a : Fp2) (k : Fp) : Fp2 :=
  { c0 := a.c0 * k, c1 := a.c1 * k }

/-- Conjugation `c₀ + c₁·u ↦ c₀ − c₁·u`. Same as raising to the `p`-th
    power (Frobenius on `F_p²`). -/
@[inline] def conj (a : Fp2) : Fp2 := { c0 := a.c0, c1 := -a.c1 }

/-- Frobenius on `F_p²`: `a ↦ a^p`. Equals conjugation because
    `p ≡ 3 mod 4` (so `u^(p−1) = −1`). -/
@[inline] def frobenius (a : Fp2) : Fp2 := conj a

/-- Norm `N(a) = a · ā = a₀² + a₁²` (in `Fp`). -/
@[inline] def norm (a : Fp2) : Fp := a.c0 * a.c0 + a.c1 * a.c1

/-- Inverse via `a⁻¹ = ā / N(a)`. Returns `0` on `a = 0` (matches
    `FF.Inv` — callers must pre-check when correctness depends on it). -/
def inv (a : Fp2) : Fp2 :=
  let ninv := (norm a)⁻¹
  { c0 := a.c0 * ninv, c1 := -a.c1 * ninv }

/-- Multiplication by the sextic-twist parameter `ξ = 9 + u`.
    `(a₀ + a₁u)(9 + u) = (9a₀ − a₁) + (a₀ + 9a₁)u`. -/
def mulByXi (a : Fp2) : Fp2 :=
  { c0 := 9 * a.c0 - a.c1,
    c1 := a.c0 + 9 * a.c1 }

/-- Multiplication by `u`: `(a₀ + a₁u)·u = −a₁ + a₀·u`. -/
@[inline] def mulByU (a : Fp2) : Fp2 := { c0 := -a.c1, c1 := a.c0 }

/-- Raise `a` to a `Nat` exponent via square-and-multiply. -/
def pow (a : Fp2) (e : Nat) : Fp2 := Id.run do
  let mut acc : Fp2 := one
  let mut base := a
  let mut n := e
  while n ≠ 0 do
    if n % 2 = 1 then acc := mul acc base
    base := square base
    n := n / 2
  return acc

----------------------------------------------------------------------------
-- Numeric-tower instances. `x^2` fast-paths to `square`; everything
-- else falls into the generic pow.
----------------------------------------------------------------------------

@[inline] instance : Add Fp2 := ⟨add⟩
@[inline] instance : Sub Fp2 := ⟨sub⟩
@[inline] instance : Mul Fp2 := ⟨mul⟩
@[inline] instance : Neg Fp2 := ⟨neg⟩
@[inline] instance : Zero Fp2 := ⟨zero⟩
@[inline] instance : One Fp2 := ⟨one⟩
@[inline] instance : Inv Fp2 := ⟨inv⟩
/-- Numeric literals lift into `Fp2` via the c0 slot (real part). -/
@[inline] instance {n : Nat} : OfNat Fp2 n :=
  ⟨{ c0 := (OfNat.ofNat n : Fp), c1 := 0 }⟩

/-- `x ^ n` on `Fp2`. Fast-paths `n = 2` to the direct `(a+b)(a−b)`
    squaring formula. -/
@[inline] instance : HPow Fp2 Nat Fp2 where
  hPow a n := if n = 2 then square a else pow a n

end EvmSemantics.Crypto.Fp2
