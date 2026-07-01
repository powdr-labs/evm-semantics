module

public import EvmSemantics.Crypto.Fp6
public import Batteries.Tactic.Lint.Misc

/-!
`EvmSemantics.Crypto.Fp12` — the twelfth extension `F_p¹² = F_p⁶[w]/(w² − v)`
where `v ∈ F_p⁶` is the generator of the sextic tower.

An `Fp12` element is a pair `(c₀, c₁)` of `F_p⁶` values representing
`c₀ + c₁·w`. Multiplication reduces with `w² = v`. This is the target
field of the BN254 optimal-ate pairing — pairing outputs live in the
order-`N` cyclotomic subgroup of `F_p¹²`.
-/

@[expose] public section

namespace EvmSemantics.Crypto.Fp12

open EvmSemantics.Crypto.Fp2
open EvmSemantics.Crypto.Fp6

/-- Element of `F_p¹² = F_p⁶[w]/(w² − v)`: `c₀ + c₁·w`. -/
structure Fp12 where
  /-- Constant-term Fp6 coefficient. -/
  c0 : Fp6
  /-- `w`-coefficient. -/
  c1 : Fp6
  deriving Inhabited, DecidableEq

attribute [nolint dupNamespace] Fp12 Fp12.mk Fp12.c0 Fp12.c1 Fp12.rec

/-- Additive identity. -/
@[inline] def zero : Fp12 := { c0 := Fp6.zero, c1 := Fp6.zero }

/-- Multiplicative identity `1 + 0·w`. -/
@[inline] def one : Fp12 := { c0 := Fp6.one, c1 := Fp6.zero }

/-- Boolean equality: both `Fp6` coefficients must match. -/
@[inline] def eq (a b : Fp12) : Bool := Fp6.eq a.c0 b.c0 ∧ Fp6.eq a.c1 b.c1

/-- Componentwise addition. -/
@[inline] def add (p : Nat) (a b : Fp12) : Fp12 :=
  { c0 := Fp6.add p a.c0 b.c0, c1 := Fp6.add p a.c1 b.c1 }

/-- Componentwise subtraction. -/
@[inline] def sub (p : Nat) (a b : Fp12) : Fp12 :=
  { c0 := Fp6.sub p a.c0 b.c0, c1 := Fp6.sub p a.c1 b.c1 }

/-- Componentwise negation. -/
@[inline] def neg (p : Nat) (a : Fp12) : Fp12 :=
  { c0 := Fp6.neg p a.c0, c1 := Fp6.neg p a.c1 }

/-- Multiplication via Karatsuba on the two `Fp6` coefficients.
    `(c₀ + c₁w)(d₀ + d₁w) = (c₀d₀ + v·c₁d₁) + ((c₀+c₁)(d₀+d₁) − c₀d₀ − c₁d₁)w`.
    Three `Fp6` multiplications. -/
def mul (p : Nat) (a b : Fp12) : Fp12 :=
  let v0 := Fp6.mul p a.c0 b.c0
  let v1 := Fp6.mul p a.c1 b.c1
  let t  := Fp6.mul p (Fp6.add p a.c0 a.c1) (Fp6.add p b.c0 b.c1)
  { c0 := Fp6.add p v0 (Fp6.mulByV p v1),
    c1 := Fp6.sub p (Fp6.sub p t v0) v1 }

/-- Complex squaring: `(c₀ + c₁w)² = (c₀ + c₁)(c₀ + v·c₁) − c₀·c₁ − v·c₀·c₁ ` — 2 Fp6 muls. -/
def square (p : Nat) (a : Fp12) : Fp12 :=
  let ab := Fp6.mul p a.c0 a.c1
  let c0PlusC1 := Fp6.add p a.c0 a.c1
  let c0PlusVC1 := Fp6.add p a.c0 (Fp6.mulByV p a.c1)
  let t := Fp6.mul p c0PlusC1 c0PlusVC1
  { c0 := Fp6.sub p (Fp6.sub p t ab) (Fp6.mulByV p ab),
    c1 := Fp6.add p ab ab }

/-- Fp12-conjugation `(c₀ + c₁w) ↦ (c₀ − c₁w)`. On the *cyclotomic*
    subgroup (norm-1 elements of `F_p¹²*`, where the pairing outputs
    live) this equals the inverse — no field division needed. -/
@[inline] def conj (p : Nat) (a : Fp12) : Fp12 :=
  { c0 := a.c0, c1 := Fp6.neg p a.c1 }

/-- General inverse via `1/(c₀ + c₁w) = (c₀ − c₁w) / (c₀² − v·c₁²)`. -/
def inv (p : Nat) (a : Fp12) : Fp12 :=
  let t0 := Fp6.square p a.c0
  let t1 := Fp6.square p a.c1
  -- norm = c0² − v·c1²
  let n  := Fp6.sub p t0 (Fp6.mulByV p t1)
  let ni := Fp6.inv p n
  { c0 := Fp6.mul p a.c0 ni,
    c1 := Fp6.neg p (Fp6.mul p a.c1 ni) }

/-- Exponentiate `a ∈ Fp12` by a `Nat` scalar via square-and-multiply. -/
def pow (p : Nat) (a : Fp12) (e : Nat) : Fp12 := Id.run do
  let mut acc : Fp12 := one
  let mut base := a
  let mut n := e
  while n ≠ 0 do
    if n % 2 = 1 then acc := mul p acc base
    base := square p base
    n := n / 2
  return acc

/-- Frobenius on `Fp12` requires precomputed constants (elements of
    `Fp2`) that depend on the field prime. Let `γ = ξ^((p−1)/6) ∈ Fp2`
    where `ξ = 9 + u` is the sextic non-residue. Then Frobenius uses
    three γ-derived constants:

    * `γ_w = γ`         — for the `w`-term in Fp12.
    * `γ_v = γ²`        — for the `v`-term in Fp6.
    * `γ_v² = γ⁴`       — for the `v²`-term in Fp6.

    (γ³ = ξ^((p−1)/2) appears in the *twist* Frobenius but not in the
    ordinary Fp12/Fp6 Frobenius.) With those three constants:
    `(c₀ + c₁w)^p = frob₆(c₀) + γ_w · frob₆(c₁) · w`
    `(a₀ + a₁v + a₂v²)^p = frob₂(a₀) + γ_v · frob₂(a₁) · v + γ_{v²} · frob₂(a₂) · v²` -/
def frobenius (p : Nat) (γw γv γv2 : Fp2) (a : Fp12) : Fp12 :=
  let frob6 (x : Fp6) : Fp6 :=
    { c0 := Fp2.conj p x.c0,
      c1 := Fp2.mul p γv (Fp2.conj p x.c1),
      c2 := Fp2.mul p γv2 (Fp2.conj p x.c2) }
  { c0 := frob6 a.c0,
    c1 := Fp6.mulByFp2 p (frob6 a.c1) γw }

/-- Sparse multiplication: `a ∈ Fp12` times a pairing-line element of
    the form `b = (b0, 0, 0) + (b1, b2, 0)·w` — i.e. only the `w⁰`
    constant term, the `w¹·v⁰`, and the `w¹·v¹` slots are nonzero.

    Used inside Miller's loop, which produces line-function values of
    exactly this shape; a specialised routine saves ~8 Fp2
    multiplications per Miller step vs. the generic `mul`. -/
def mulBy014 (p : Nat) (a : Fp12) (b0 b1 b4 : Fp2) : Fp12 :=
  -- Split as a = a₀ + a₁w with each aᵢ ∈ Fp6.
  -- b viewed the same way: b₀' = (b0,0,0) ∈ Fp6, b₁' = (b1,b4,0) ∈ Fp6.
  -- Then (a₀+a₁w)(b₀' + b₁'w) = (a₀·b₀' + v·a₁·b₁') + ((a₀+a₁)(b₀'+b₁') − a₀·b₀' − a₁·b₁')w.
  -- a₀·b₀' = a₀ * (b0 in slot 0) — this is Fp6 × Fp2 scaling of just c0.
  -- a₀·b₀' is really `(a₀.c0 * b0, a₀.c1 * b0, a₀.c2 * b0)` since (b0,0,0) is Fp2 times v⁰.
  -- Actually b₀' is more subtle: as an Fp6 element (b0, 0, 0) which is just b0 * 1.
  -- So a₀ · (b0,0,0) is just `mulByFp2 a₀ b0`.
  let a0b0 : Fp6 := Fp6.mulByFp2 p a.c0 b0
  -- b₁' as an Fp6 is (b1, b4, 0), so a₁·b₁' uses the sparse mulBy01.
  let a1b1 : Fp6 := Fp6.mulBy01 p a.c1 b1 b4
  -- Sum (a₀+a₁)·(b₀'+b₁') for the middle Karatsuba term.
  -- b₀' + b₁' = (b0+b1, b4, 0) which is again a mulBy01-compatible sparse Fp6.
  let sum := Fp6.mulBy01 p (Fp6.add p a.c0 a.c1) (Fp2.add p b0 b1) b4
  { c0 := Fp6.add p a0b0 (Fp6.mulByV p a1b1),
    c1 := Fp6.sub p (Fp6.sub p sum a0b0) a1b1 }

end EvmSemantics.Crypto.Fp12
