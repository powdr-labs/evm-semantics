module

public import EvmSemantics.Crypto.EC
public import Batteries.Tactic.Lint.Misc

/-!
`EvmSemantics.Crypto.FF` — finite fields `F_p` with the modulus baked
into the type.

`FF p` is a *reducible abbreviation* for `Fin p`, i.e. a `Nat`
representative together with a `Prop`-erased proof that it lies in
`[0, p)`. The proof is enforced at the type level: constructing a
value with `.val ≥ p` is a type error. Two distinct primes yield two
distinct types (`FF Secp256k1.p ≠ FF Bn254.p`), so the compiler
catches mix-ups the raw-`Nat` code silently accepts.

The runtime representation is `val : Nat` — the `isLt` proof is
compile-time erased. So `FF p` is zero-overhead vs a bare `Nat`.

`Add / Sub / Mul / Neg / Zero / One / OfNat` come from `Fin`'s own
instances (Lean core / Mathlib) when `[NeZero p]` is in scope. Every
concrete curve (`Bn254`, `Secp256k1`) provides a `NeZero p` instance
in its own module, so BN254/secp256k1 call sites get the full
operator set automatically.

`Inv (FF p)` and `HPow (FF p) Nat (FF p)` are our own — extended
Euclidean modular inverse and square-and-multiply exponentiation
don't have counterparts in `Fin`'s core API.

This module also hosts the `Nat`-level modular arithmetic
(`modAdd`, `modMul`, `modPow`, `modInv`, `modSqrt`) that the `FF`
instances delegate to, plus the polymorphic `Curve p` value + point
operations parameterised by `p`.
-/

@[expose] public section

namespace EvmSemantics.Crypto.FF

open EvmSemantics.Crypto.EC (Point)

----------------------------------------------------------------------------
-- Nat-level modular arithmetic.
--
-- `m` is passed explicitly at every call — used both for field
-- arithmetic (`m := p`) and for scalar arithmetic mod the group
-- order (`m := N`).
----------------------------------------------------------------------------

/-- `a + b mod m`. -/
@[inline] def modAdd (a b m : Nat) : Nat := (a + b) % m

/-- `a - b mod m`; wraps via `(a + m − b) % m` so we stay in `Nat`. -/
@[inline] def modSub (a b m : Nat) : Nat := (a + (m - b % m)) % m

/-- `a * b mod m`. -/
@[inline] def modMul (a b m : Nat) : Nat := (a * b) % m

/-- `−a mod m`. -/
@[inline] def modNeg (a m : Nat) : Nat := (m - a % m) % m

/-- Inner square-and-multiply loop for `modPow`. -/
partial def modPow.go (m b acc e : Nat) : Nat :=
  if e = 0 then acc
  else
    let acc' := if e % 2 = 1 then (acc * b) % m else acc
    modPow.go m ((b * b) % m) acc' (e / 2)

/-- Square-and-multiply modular exponentiation: `base^e mod m`. -/
def modPow (base e m : Nat) : Nat := modPow.go m (base % m) 1 e

/-- Inner extended-Euclidean loop for `modInv`. -/
partial def modInv.go (m r0 r1 t0 t1 : Nat) : Nat :=
  if r1 = 0 then t0
  else
    let q := r0 / r1
    let qt1 := (q * t1) % m
    let t := if t0 ≥ qt1 then t0 - qt1 else t0 + (m - qt1)
    modInv.go m r1 (r0 - q * r1) t1 t

/-- Modular inverse via the extended Euclidean algorithm. Returns
    `0` for `a ≡ 0 mod m` (undefined behaviour for the underlying
    inverse — callers must pre-check). -/
def modInv (a m : Nat) : Nat := modInv.go m m (a % m) 0 1

/-- Modular square root when `m ≡ 3 mod 4`: `sqrt(a) = a^((m+1)/4) mod m`.
    Returns *some* square root — the other is `m − result`. -/
@[inline] def modSqrt (a m : Nat) : Nat := modPow a ((m + 1) / 4) m

end EvmSemantics.Crypto.FF

----------------------------------------------------------------------------
-- The `FF p` type.
--
-- Reducible abbreviation for `Fin p` so the compiler can see through
-- it when picking up `Add / Sub / Mul / Neg / OfNat` etc. from
-- `Fin`'s own instances (which live in Lean core and Mathlib).
----------------------------------------------------------------------------

/-- Element of `F_p` — a `Nat` in `[0, p)` with the bound enforced by
    the underlying `Fin p` proof, typed by its modulus. -/
abbrev FF (p : Nat) := Fin p

namespace FF

/-- Reduce a `Nat` into `FF p`. Idempotent on values already in
    `[0, p)`. Requires `[NeZero p]` so `Fin p` is non-empty and the
    `mod_lt` proof goes through. -/
@[inline] def ofNat {p : Nat} [NeZero p] (a : Nat) : FF p := Fin.ofNat p a

/-- Access the underlying `Nat` representative. Alias for `Fin.val`;
    exists to give byte-serialisation call sites a stable name. -/
@[inline] def toNat {p : Nat} (a : FF p) : Nat := a.val

end FF

----------------------------------------------------------------------------
-- Instances not provided by `Fin`'s core / Mathlib API.
----------------------------------------------------------------------------

/-- Inverse via extended Euclidean, wrapped back into `FF p`. Returns
    the `Fin p` element with `val = 0` for `a = 0` — mirrors the
    underlying `modInv`; callers must pre-check when correctness
    depends on non-zero input. -/
@[inline] instance {p : Nat} [NeZero p] : Inv (FF p) :=
  ⟨fun a => Fin.ofNat p (EvmSemantics.Crypto.FF.modInv a.val p)⟩

/-- `a ^ n` for `n : Nat`, via square-and-multiply on the raw
    representative. -/
@[inline] instance {p : Nat} [NeZero p] : HPow (FF p) Nat (FF p) :=
  ⟨fun a e => Fin.ofNat p (EvmSemantics.Crypto.FF.modPow a.val e p)⟩

----------------------------------------------------------------------------
-- Curve values + point operations, defined once here for any `FF p`.
----------------------------------------------------------------------------

namespace EvmSemantics.Crypto.FF

open EvmSemantics.Crypto.EC (Point)

/-- A short-Weierstrass curve `y² = x³ + b` over `F_p`. `a = 0`
    (matches both secp256k1 and BN254). -/
structure Curve (p : Nat) where
  /-- The curve equation coefficient. -/
  b : FF p

/-- `(x, y) ∈ E(F_p)` iff `y² = x³ + b`. `[NeZero p]` is required
    for the operator resolution (the linter can't see through
    typeclass instance elaboration, hence `nolint`). -/
@[nolint unusedArguments]
def onCurve {p : Nat} [NeZero p] (c : Curve p) (x y : FF p) : Bool :=
  y * y = x * (x * x) + c.b

/-- Square-root a modulus-`p` value assuming `p ≡ 3 (mod 4)`. Wraps
    the `Nat`-level `modSqrt` back into `FF p`. -/
@[inline] def sqrt {p : Nat} [NeZero p] (a : FF p) : FF p :=
  Fin.ofNat p (modSqrt a.val p)

/-- Double a curve point. Formula for `a = 0` short-Weierstrass:
    `λ = 3·x² / (2·y);  x' = λ² − 2·x;  y' = λ·(x − x') − y`.
    The `Curve` argument is unused (doubling only needs `a = 0`,
    baked in) but kept for API symmetry with `addPoint c`. -/
def doublePoint {p : Nat} [NeZero p] (c : Curve p) :
    Point (FF p) → Point (FF p)
  | .infinity => .infinity
  | .affine x y =>
    if y = 0 then .infinity
    else
      let _ := c   -- keep API symmetric with `addPoint c`; unused here
      let lam := (3 * x * x) * (2 * y)⁻¹
      let x' := lam * lam - 2 * x
      let y' := lam * (x - x') - y
      .affine x' y'

/-- Add two affine points. Handles identity / opposite / doubling
    cases explicitly so we never divide by zero. -/
def addPoint {p : Nat} [NeZero p] (c : Curve p) :
    Point (FF p) → Point (FF p) → Point (FF p)
  | .infinity, Q => Q
  | P, .infinity => P
  | .affine x1 y1, .affine x2 y2 =>
    if x1 = x2 then
      if y1 + y2 = 0 then .infinity
      else doublePoint c (.affine x1 y1)
    else
      let lam := (y2 - y1) * (x2 - x1)⁻¹
      let x3 := lam * lam - x1 - x2
      let y3 := lam * (x1 - x3) - y1
      .affine x3 y3

/-- Scalar multiplication `k · P` via right-to-left double-and-add. -/
def scalarMul {p : Nat} [NeZero p] (c : Curve p) (k : Nat)
    (P : Point (FF p)) : Point (FF p) :=
  Id.run do
  let mut R : Point (FF p) := .infinity
  let mut base : Point (FF p) := P
  let mut e := k
  while e ≠ 0 do
    if e % 2 = 1 then R := addPoint c R base
    base := doublePoint c base
    e := e / 2
  return R

/-- Simultaneous double-scalar multiplication `k₁·P₁ + k₂·P₂` via
    Shamir's trick. -/
def scalarMul2 {p : Nat} [NeZero p] (c : Curve p)
    (k1 : Nat) (P1 : Point (FF p)) (k2 : Nat) (P2 : Point (FF p)) :
    Point (FF p) :=
  Id.run do
  let P1plus2 := addPoint c P1 P2
  let mut bitlen : Nat := 0
  let mut m := Nat.max k1 k2
  while m ≠ 0 do
    bitlen := bitlen + 1
    m := m / 2
  let mut Q : Point (FF p) := .infinity
  let mut i := bitlen
  while i ≠ 0 do
    i := i - 1
    Q := doublePoint c Q
    let b1 : Bool := (k1 >>> i) &&& 1 = 1
    let b2 : Bool := (k2 >>> i) &&& 1 = 1
    match b1, b2 with
    | false, false => pure ()
    | true,  false => Q := addPoint c Q P1
    | false, true  => Q := addPoint c Q P2
    | true,  true  => Q := addPoint c Q P1plus2
  return Q

/-- Given `x` and a parity bit `yOdd`, recover the unique `(x, y)` on
    the curve with `y mod 2 = yOdd`, or `none` if `x³ + b` is not a
    quadratic residue. Requires `p ≡ 3 mod 4`. -/
def decompress {p : Nat} [NeZero p] (c : Curve p) (x : FF p) (yOdd : Bool) :
    Option (Point (FF p)) :=
  let α := x * x * x + c.b
  let β := sqrt α
  if β * β ≠ α then none
  else
    let y : FF p := if (β.val % 2 = 1) = yOdd then β else -β
    some (.affine x y)

end EvmSemantics.Crypto.FF
