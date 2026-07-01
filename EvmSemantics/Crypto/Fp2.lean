module

public import EvmSemantics.Crypto.EC
public import Batteries.Tactic.Lint.Misc

/-!
`EvmSemantics.Crypto.Fp2` — the quadratic extension `F_p²` used by
BN254 pairing arithmetic.

BN254's `F_p²` is `F_p[u] / (u² + 1)`, so `u² = −1` and every element
is a pair `c₀ + c₁·u` with `c₀, c₁ ∈ F_p`. `p ≡ 3 (mod 4)` guarantees
`u² + 1` is irreducible over `F_p` (i.e. `−1` is a non-residue), so
this really is a field.

Operations in this module all take the modulus `p` explicitly rather
than closing over a global constant, so the same code could in
principle be reused for any other `F_p²` with the same irreducible
polynomial `u² + 1`. The one call site is BN254 (`Bn254.p`).

Encoding on the EIP-197 wire is `[c₁‖c₀]` (imaginary part first, then
real) — the driver handles that; internally we keep the "natural"
`(c₀, c₁)` order.
-/

@[expose] public section

namespace EvmSemantics.Crypto.Fp2

open EvmSemantics.Crypto.EC

/-- Element of `F_p² = F_p[u]/(u² + 1)`: `c₀ + c₁·u`. -/
structure Fp2 where
  /-- Real part `c₀ ∈ F_p`. -/
  c0 : Nat
  /-- Imaginary part `c₁ ∈ F_p` (coefficient of `u`). -/
  c1 : Nat
  deriving Inhabited, DecidableEq

-- The lint `dupNamespace` catches `Fp2.Fp2.*` names created by nesting the
-- struct inside a same-name namespace. We accept that here — keeping the
-- namespace name equal to the struct name is the convention in this file
-- (parallel to `Secp256k1.Point` etc.).
attribute [nolint dupNamespace] Fp2 Fp2.mk Fp2.c0 Fp2.c1 Fp2.rec

/-- Additive identity `0 + 0·u`. -/
@[inline] def zero : Fp2 := { c0 := 0, c1 := 0 }

/-- Multiplicative identity `1 + 0·u`. -/
@[inline] def one : Fp2 := { c0 := 1, c1 := 0 }

/-- The generator `0 + 1·u`. Useful for encoding constants like the
    sextic-twist parameter `ξ = 9 + u`. -/
@[inline] def u : Fp2 := { c0 := 0, c1 := 1 }

/-- Boolean equality inside the field: both coefficients must match. -/
@[inline] def eq (a b : Fp2) : Bool := a.c0 = b.c0 ∧ a.c1 = b.c1

/-- `a + b` in `F_p²`. -/
@[inline] def add (p : Nat) (a b : Fp2) : Fp2 :=
  { c0 := modAdd a.c0 b.c0 p, c1 := modAdd a.c1 b.c1 p }

/-- `a − b` in `F_p²`. -/
@[inline] def sub (p : Nat) (a b : Fp2) : Fp2 :=
  { c0 := modSub a.c0 b.c0 p, c1 := modSub a.c1 b.c1 p }

/-- `−a` in `F_p²`. -/
@[inline] def neg (p : Nat) (a : Fp2) : Fp2 :=
  { c0 := modNeg a.c0 p, c1 := modNeg a.c1 p }

/-- Multiplication in `F_p²`.
    `(a₀ + a₁u)(b₀ + b₁u) = (a₀b₀ − a₁b₁) + (a₀b₁ + a₁b₀)u`
    using `u² = −1`. -/
def mul (p : Nat) (a b : Fp2) : Fp2 :=
  let t0 := modMul a.c0 b.c0 p
  let t1 := modMul a.c1 b.c1 p
  let c0 := modSub t0 t1 p
  -- (a₀+a₁)(b₀+b₁) − t0 − t1 = a₀b₁ + a₁b₀   (Karatsuba trick, one fewer mul)
  let s := modMul (modAdd a.c0 a.c1 p) (modAdd b.c0 b.c1 p) p
  let c1 := modSub (modSub s t0 p) t1 p
  { c0 := c0, c1 := c1 }

/-- Squaring in `F_p²`: `(a₀ + a₁u)² = (a₀² − a₁²) + 2a₀a₁·u`.
    Uses `(a₀ + a₁)(a₀ − a₁)` for the real part to save a multiply. -/
def square (p : Nat) (a : Fp2) : Fp2 :=
  let c0 := modMul (modAdd a.c0 a.c1 p) (modSub a.c0 a.c1 p) p
  let c1 := modMul (modAdd a.c0 a.c0 p) a.c1 p
  { c0 := c0, c1 := c1 }

/-- Multiplication by a base-field scalar `k ∈ F_p`. -/
@[inline] def mulByFp (p : Nat) (a : Fp2) (k : Nat) : Fp2 :=
  { c0 := modMul a.c0 k p, c1 := modMul a.c1 k p }

/-- Conjugation `c₀ + c₁·u ↦ c₀ − c₁·u`. Same as raising to the `p`-th
    power (Frobenius on `F_p²`). -/
@[inline] def conj (p : Nat) (a : Fp2) : Fp2 :=
  { c0 := a.c0, c1 := modNeg a.c1 p }

/-- Frobenius on `F_p²`: `a ↦ a^p`. Since `u^p = −u` (because
    `p ≡ 3 mod 4`, so `u^(p−1) = (u²)^((p−1)/2) = (−1)^((p−1)/2) = −1`),
    this equals conjugation. -/
@[inline] def frobenius (p : Nat) (a : Fp2) : Fp2 := conj p a

/-- The norm `N(a) = a · ā = a₀² + a₁²` in `F_p`. -/
@[inline] def norm (p : Nat) (a : Fp2) : Nat :=
  modAdd (modMul a.c0 a.c0 p) (modMul a.c1 a.c1 p) p

/-- Inverse in `F_p²` via `a⁻¹ = ā / N(a)`. Returns `zero` if `a = 0`
    (matching `EC.modInv`'s convention on zero input; callers must
    pre-check). -/
def inv (p : Nat) (a : Fp2) : Fp2 :=
  let ninv := modInv (norm p a) p
  { c0 := modMul a.c0 ninv p, c1 := modMul (modNeg a.c1 p) ninv p }

/-- Multiplication by the sextic-twist parameter `ξ = 9 + u`, used
    heavily by the `F_p⁶` / `F_p¹²` tower. Direct formula avoids a
    generic `Fp2.mul`:
    `(a₀ + a₁u)(9 + u) = (9a₀ − a₁) + (a₀ + 9a₁)u`. -/
def mulByXi (p : Nat) (a : Fp2) : Fp2 :=
  let nineA0 := modMul 9 a.c0 p
  let nineA1 := modMul 9 a.c1 p
  { c0 := modSub nineA0 a.c1 p,
    c1 := modAdd a.c0 nineA1 p }

/-- Multiplication by `u`: `(a₀ + a₁u)·u = −a₁ + a₀·u`. -/
@[inline] def mulByU (p : Nat) (a : Fp2) : Fp2 :=
  { c0 := modNeg a.c1 p, c1 := a.c0 }

end EvmSemantics.Crypto.Fp2
