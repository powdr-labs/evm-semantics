module

public import EvmSemantics.Crypto.EC
public import Batteries.Tactic.Lint.Misc

/-!
`EvmSemantics.Crypto.FF` — finite-field extensions to `Fin p` plus
the polymorphic Weierstrass curve operations that consume them.

We spell field elements `Fin p` directly rather than through an
`FF p` alias — Lean core's `Add / Sub / Mul / Neg / Zero / One /
OfNat` on `Fin p` (given `[NeZero p]`) already give us the operator
sugar, and constructing from a raw `Nat` is `Fin.ofNat p a`. This
module adds only what `Fin` doesn't:

* `Inv (Fin p)` — extended-Euclidean modular inverse.
* `HPow (Fin p) Nat (Fin p)` — square-and-multiply exponentiation.
* `sqrt` — modular square root (needs `p ≡ 3 mod 4`).
* `Curve p` + `doublePoint / addPoint / scalarMul / scalarMul2 /
  onCurve / decompress` — the polymorphic point operations, once
  per curve family, over `Point (Fin p)`.

Concrete curves (`Bn254`, `Secp256k1`) instantiate `Fp := Fin p`,
supply `NeZero p`, wrap `curve : Curve p`, and re-export the ops.
The user-facing API for those callers stays curve-namespaced
(`Bn254.doublePoint`, etc.).

Two guardrails worth noting explicitly for `Fin p` arithmetic:

* `+ / - / * / -a` are modular over `p` (Lean core's `Fin.add /
  sub / mul / neg` reduce mod n). Correct field arithmetic when
  `p` is prime.
* `x % y` and `x / y` on `Fin p` are **not** field ops — they're
  `Nat` truncated-mod and truncated-division on the raw
  representatives. We never use those.
-/

@[expose] public section

namespace EvmSemantics.Crypto.FF

open EvmSemantics.Crypto.EC (Point)

----------------------------------------------------------------------------
-- Internal Nat-level modular arithmetic.
--
-- Building blocks the `Inv` / `HPow` / `sqrt` instances on `Fin p`
-- delegate to. Not intended for direct use — external call sites
-- should get modular arithmetic via `Fin p`'s operators.
----------------------------------------------------------------------------

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
-- Instances not provided by `Fin`'s core / Mathlib API.
----------------------------------------------------------------------------

/-- Multiplicative inverse via extended Euclidean, then wrapped back
    into `Fin p`. Returns `⟨0, _⟩` for `a = 0` — mirrors the
    underlying `modInv`; callers must pre-check when correctness
    depends on non-zero input. -/
@[inline] instance instInvFin {p : Nat} [NeZero p] : Inv (Fin p) :=
  ⟨fun a => Fin.ofNat p (EvmSemantics.Crypto.FF.modInv a.val p)⟩

/-- `a ^ n` for `n : Nat`, via square-and-multiply on the raw
    representative. -/
@[inline] instance instHPowFinNat {p : Nat} [NeZero p] : HPow (Fin p) Nat (Fin p) :=
  ⟨fun a e => Fin.ofNat p (EvmSemantics.Crypto.FF.modPow a.val e p)⟩

----------------------------------------------------------------------------
-- Curve values + point operations, once here for any `Fin p`.
----------------------------------------------------------------------------

namespace EvmSemantics.Crypto.FF

open EvmSemantics.Crypto.EC (Point)

/-- A short-Weierstrass curve `y² = x³ + b` over `F_p`. `a = 0`
    (matches both secp256k1 and BN254). -/
structure Curve (p : Nat) where
  /-- The curve equation coefficient. -/
  b : Fin p

/-- `(x, y) ∈ E(F_p)` iff `y² = x³ + b`. `[NeZero p]` is required
    for the operator resolution (the linter can't see through
    typeclass instance elaboration, hence `nolint`). -/
@[nolint unusedArguments]
def onCurve {p : Nat} [NeZero p] (c : Curve p) (x y : Fin p) : Bool :=
  y * y = x * (x * x) + c.b

/-- Square-root a modulus-`p` value assuming `p ≡ 3 (mod 4)`. Wraps
    the `Nat`-level `modSqrt` back into `Fin p`. -/
@[inline] def sqrt {p : Nat} [NeZero p] (a : Fin p) : Fin p :=
  Fin.ofNat p (modSqrt a.val p)

/-- Double a curve point. Formula for `a = 0` short-Weierstrass:
    `λ = 3·x² / (2·y);  x' = λ² − 2·x;  y' = λ·(x − x') − y`.
    The `Curve` argument is unused (doubling only needs `a = 0`,
    baked in) but kept for API symmetry with `addPoint c`. -/
@[nolint unusedArguments]
def doublePoint {p : Nat} [NeZero p] (_c : Curve p) :
    Point (Fin p) → Point (Fin p)
  | .infinity => .infinity
  | .affine x y =>
    if y = 0 then .infinity
    else
      let lam := (3 * x * x) * (2 * y)⁻¹
      let x' := lam * lam - 2 * x
      let y' := lam * (x - x') - y
      .affine x' y'

/-- Add two affine points. Handles identity / opposite / doubling
    cases explicitly so we never divide by zero. -/
def addPoint {p : Nat} [NeZero p] (c : Curve p) :
    Point (Fin p) → Point (Fin p) → Point (Fin p)
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
    (P : Point (Fin p)) : Point (Fin p) :=
  Id.run do
  let mut R : Point (Fin p) := .infinity
  let mut base : Point (Fin p) := P
  let mut e := k
  while e ≠ 0 do
    if e % 2 = 1 then R := addPoint c R base
    base := doublePoint c base
    e := e / 2
  return R

/-- Simultaneous double-scalar multiplication `k₁·P₁ + k₂·P₂` via
    Shamir's trick. -/
def scalarMul2 {p : Nat} [NeZero p] (c : Curve p)
    (k1 : Nat) (P1 : Point (Fin p)) (k2 : Nat) (P2 : Point (Fin p)) :
    Point (Fin p) :=
  Id.run do
  let P1plus2 := addPoint c P1 P2
  let mut bitlen : Nat := 0
  let mut m := Nat.max k1 k2
  while m ≠ 0 do
    bitlen := bitlen + 1
    m := m / 2
  let mut Q : Point (Fin p) := .infinity
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
def decompress {p : Nat} [NeZero p] (c : Curve p) (x : Fin p) (yOdd : Bool) :
    Option (Point (Fin p)) :=
  let α := x * x * x + c.b
  let β := sqrt α
  if β * β ≠ α then none
  else
    let y : Fin p := if (β.val % 2 = 1) = yOdd then β else -β
    some (.affine x y)

end EvmSemantics.Crypto.FF
