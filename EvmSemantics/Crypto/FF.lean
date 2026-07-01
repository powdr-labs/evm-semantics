module

public import Batteries.Tactic.Lint.Misc

/-!
`EvmSemantics.Crypto.FF` — field-arithmetic extensions to `Fin p`.

Lean core's `Add / Sub / Mul / Neg / Zero / One / OfNat` on `Fin p`
(given `[NeZero p]`) already give the operator sugar, and
constructing from a raw `Nat` is `Fin.ofNat p a`. This module adds
only what `Fin` doesn't provide:

* `Inv (Fin p)` — extended-Euclidean modular inverse.
* `HPow (Fin p) Nat (Fin p)` — square-and-multiply exponentiation.
* `sqrt` — modular square root (requires `p ≡ 3 mod 4`).

Point / curve operations live in `EvmSemantics.Crypto.Weierstrass`;
the polymorphic `Point (F : Type)` container in
`EvmSemantics.Crypto.EC`.

Two guardrails worth knowing explicitly for `Fin p` arithmetic:

* `+ / - / * / -a` are modular over `p` (Lean core reduces mod n).
  Correct field arithmetic when `p` is prime.
* `x % y` and `x / y` on `Fin p` are **not** field ops — they're
  `Nat` truncated-mod and truncated-division on the raw
  representatives. We never use those.
-/

@[expose] public section

namespace EvmSemantics.Crypto.FF

----------------------------------------------------------------------------
-- Internal Nat-level modular arithmetic.
--
-- Building blocks that `Inv` / `HPow` / `sqrt` on `Fin p` delegate
-- to. Not intended for direct use — external call sites should get
-- modular arithmetic via `Fin p`'s operators.
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

/-- Square-root a modulus-`p` value assuming `p ≡ 3 (mod 4)`. Wraps
    the `Nat`-level `modSqrt` back into `Fin p`. -/
@[inline] def sqrt {p : Nat} [NeZero p] (a : Fin p) : Fin p :=
  Fin.ofNat p (modSqrt a.val p)

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
