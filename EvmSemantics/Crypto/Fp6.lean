module

public import EvmSemantics.Crypto.Fp2
public import Batteries.Tactic.Lint.Misc

/-!
`EvmSemantics.Crypto.Fp6` — the sextic tower `F_p⁶ = F_p²[v] / (v³ − ξ)`
where `ξ = 9 + u` is the sextic-twist parameter of BN254.

An element is a triple `(c₀, c₁, c₂)` of `F_p²` elements, representing
`c₀ + c₁·v + c₂·v²`. The multiplication reduction uses `v³ = ξ`.

We implement mul via 6-Karatsuba (five schoolbook cross-terms reduce
to a couple of extra Fp2 additions for one fewer Fp2 mul in some
places). Squaring uses a direct formula. Inverse uses the classical
Fp6 formula `1/a = ā / (a · ā)` where `ā ∈ Fp6` is the adjugate.
-/

@[expose] public section

namespace EvmSemantics.Crypto.Fp6

open EvmSemantics.Crypto.Fp2

/-- Element of `F_p⁶ = F_p²[v]/(v³ − ξ)`: `c₀ + c₁·v + c₂·v²`. -/
structure Fp6 where
  /-- Constant-term coefficient. -/
  c0 : Fp2
  /-- `v`-coefficient. -/
  c1 : Fp2
  /-- `v²`-coefficient. -/
  c2 : Fp2
  deriving Inhabited, DecidableEq

attribute [nolint dupNamespace] Fp6 Fp6.mk Fp6.c0 Fp6.c1 Fp6.c2 Fp6.rec

/-- Additive identity. -/
@[inline] def zero : Fp6 := { c0 := Fp2.zero, c1 := Fp2.zero, c2 := Fp2.zero }

/-- Multiplicative identity `1 + 0·v + 0·v²`. -/
@[inline] def one : Fp6 := { c0 := Fp2.one, c1 := Fp2.zero, c2 := Fp2.zero }

/-- Boolean equality: all three coefficients must match. -/
@[inline] def eq (a b : Fp6) : Bool := Fp2.eq a.c0 b.c0 ∧ Fp2.eq a.c1 b.c1 ∧ Fp2.eq a.c2 b.c2

/-- Componentwise addition. -/
@[inline] def add (p : Nat) (a b : Fp6) : Fp6 :=
  { c0 := Fp2.add p a.c0 b.c0, c1 := Fp2.add p a.c1 b.c1, c2 := Fp2.add p a.c2 b.c2 }

/-- Componentwise subtraction. -/
@[inline] def sub (p : Nat) (a b : Fp6) : Fp6 :=
  { c0 := Fp2.sub p a.c0 b.c0, c1 := Fp2.sub p a.c1 b.c1, c2 := Fp2.sub p a.c2 b.c2 }

/-- Componentwise negation. -/
@[inline] def neg (p : Nat) (a : Fp6) : Fp6 :=
  { c0 := Fp2.neg p a.c0, c1 := Fp2.neg p a.c1, c2 := Fp2.neg p a.c2 }

/-- Multiplication in `F_p⁶` via Karatsuba on the three coefficients.
    Uses `v³ = ξ`; the schoolbook expansion of
    `(c₀ + c₁v + c₂v²)(d₀ + d₁v + d₂v²)` folds back to a triple:
    * `r₀ = v₀ + ξ · ((c₁+c₂)(d₁+d₂) − v₁ − v₂)`
    * `r₁ = (c₀+c₁)(d₀+d₁) − v₀ − v₁ + ξ · v₂`
    * `r₂ = (c₀+c₂)(d₀+d₂) − v₀ + v₁ − v₂`
    where `vᵢ = cᵢ · dᵢ`. Six `Fp2` multiplications total. -/
def mul (p : Nat) (a b : Fp6) : Fp6 :=
  let v0 := Fp2.mul p a.c0 b.c0
  let v1 := Fp2.mul p a.c1 b.c1
  let v2 := Fp2.mul p a.c2 b.c2
  let t0 := Fp2.mul p (Fp2.add p a.c1 a.c2) (Fp2.add p b.c1 b.c2)
  let t1 := Fp2.mul p (Fp2.add p a.c0 a.c1) (Fp2.add p b.c0 b.c1)
  let t2 := Fp2.mul p (Fp2.add p a.c0 a.c2) (Fp2.add p b.c0 b.c2)
  { c0 := Fp2.add p v0 (Fp2.mulByXi p (Fp2.sub p (Fp2.sub p t0 v1) v2)),
    c1 := Fp2.add p (Fp2.sub p (Fp2.sub p t1 v0) v1) (Fp2.mulByXi p v2),
    c2 := Fp2.sub p (Fp2.sub p (Fp2.add p t2 v1) v0) v2 }

/-- Squaring: schoolbook expansion of `(c₀ + c₁v + c₂v²)²` reduced
    with `v³ = ξ`.
    * `r₀ = c₀² + 2·ξ·c₁·c₂`
    * `r₁ = 2·c₀·c₁ + ξ·c₂²`
    * `r₂ = 2·c₀·c₂ + c₁²` -/
def square (p : Nat) (a : Fp6) : Fp6 :=
  let s0 := Fp2.square p a.c0
  let s1 := Fp2.mul p a.c0 a.c1
  let s2 := Fp2.mul p a.c1 a.c2
  let s3 := Fp2.square p a.c1
  let s4 := Fp2.mul p a.c0 a.c2
  let s5 := Fp2.square p a.c2
  { c0 := Fp2.add p s0 (Fp2.mulByXi p (Fp2.add p s2 s2)),
    c1 := Fp2.add p (Fp2.add p s1 s1) (Fp2.mulByXi p s5),
    c2 := Fp2.add p (Fp2.add p s4 s4) s3 }

/-- Multiplication by a base-field element `k ∈ F_p²`. -/
@[inline] def mulByFp2 (p : Nat) (a : Fp6) (k : Fp2) : Fp6 :=
  { c0 := Fp2.mul p a.c0 k, c1 := Fp2.mul p a.c1 k, c2 := Fp2.mul p a.c2 k }

/-- Multiplication by the "generator" `v`: `(c₀ + c₁v + c₂v²)·v =
    c₀·v + c₁·v² + c₂·ξ = ξ·c₂ + c₀·v + c₁·v²`. -/
@[inline] def mulByV (p : Nat) (a : Fp6) : Fp6 :=
  { c0 := Fp2.mulByXi p a.c2, c1 := a.c0, c2 := a.c1 }

/-- Multiplication by `(c₀ + c₁·v)` — a "sparse" `Fp6` element with
    `c₂ = 0`. Used by the pairing line function; saves one `Fp2` mul
    over the general path. -/
def mulBy01 (p : Nat) (a : Fp6) (b0 b1 : Fp2) : Fp6 :=
  let a_a := Fp2.mul p a.c0 b0
  let b_b := Fp2.mul p a.c1 b1
  let t1  := Fp2.add p b0 b1
  { c0 := Fp2.add p (Fp2.mulByXi p (Fp2.sub p (Fp2.mul p (Fp2.add p a.c1 a.c2) b1) b_b))
                    a_a,
    c1 := Fp2.sub p (Fp2.sub p (Fp2.mul p t1 (Fp2.add p a.c0 a.c1)) a_a) b_b,
    c2 := Fp2.add p (Fp2.sub p (Fp2.mul p (Fp2.add p a.c0 a.c2) b0) a_a) b_b }

/-- Inverse via the adjugate formula `1/a = ā / (a · ā)` where the
    "conjugate" (norm-producing companion) in Fp6 is
    `ā = (c₀² − ξ·c₁·c₂, ξ·c₂² − c₀·c₁, c₁² − c₀·c₂)`
    and its `c₀`-component times `a` gives the (scalar) norm. -/
def inv (p : Nat) (a : Fp6) : Fp6 :=
  let t0 := Fp2.square p a.c0
  let t1 := Fp2.square p a.c1
  let t2 := Fp2.square p a.c2
  let t3 := Fp2.mul p a.c0 a.c1
  let t4 := Fp2.mul p a.c0 a.c2
  let t5 := Fp2.mul p a.c1 a.c2
  let c0' := Fp2.sub p t0 (Fp2.mulByXi p t5)
  let c1' := Fp2.sub p (Fp2.mulByXi p t2) t3
  let c2' := Fp2.sub p t1 t4
  -- Norm = c₀·c₀' + ξ·c₂·c₁' + ξ·c₁·c₂'
  let n := Fp2.add p
           (Fp2.mul p a.c0 c0')
           (Fp2.mulByXi p (Fp2.add p (Fp2.mul p a.c2 c1') (Fp2.mul p a.c1 c2')))
  let ninv := Fp2.inv p n
  { c0 := Fp2.mul p c0' ninv,
    c1 := Fp2.mul p c1' ninv,
    c2 := Fp2.mul p c2' ninv }

end EvmSemantics.Crypto.Fp6
