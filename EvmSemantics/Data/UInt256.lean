module

public import Mathlib.Data.Fin.Basic

/-!
`UInt256` — 256-bit unsigned EVM words.

A faithful subset of `EvmYul.UInt256`. We model it as a `Fin (2^256)` wrapper,
provide modular arithmetic (`+`, `-`, `*`, `/`, `%`), bitwise ops, comparisons,
and a small zoo of conversions used by the relational rules.
-/

@[expose] public section

namespace EvmSemantics

/-- `2^256` — the size of the EVM word space. -/
def UInt256.size : Nat := 2^256

instance : NeZero UInt256.size where
  out := by unfold UInt256.size; decide

/-- A 256-bit EVM word, represented as `Fin (2^256)`. -/
structure UInt256 where
  /-- The underlying `Fin (2^256)` value. -/
  val : Fin UInt256.size
  deriving BEq, DecidableEq, Ord

namespace UInt256

/-- Build a `UInt256` from a `Nat`, reducing modulo `2^256`. -/
def ofNat (n : Nat) : UInt256 := ⟨Fin.ofNat _ n⟩
/-- Project a `UInt256` back to its underlying `Nat`. -/
def toNat (u : UInt256) : Nat := u.val.val

instance {n : Nat} : OfNat UInt256 n := ⟨ofNat n⟩
instance : Inhabited UInt256 := ⟨ofNat 0⟩
instance : Repr UInt256 where reprPrec u _ := repr u.toNat
instance : ToString UInt256 where toString u := toString u.toNat
instance : Hashable UInt256 where hash u := hash u.val.val
instance : LawfulBEq UInt256 where
  eq_of_beq := fun {a b} h => by
    cases a; cases b
    have := of_decide_eq_true h
    simp_all
  rfl := by intro a; cases a; exact decide_eq_true rfl
instance : LawfulHashable UInt256 where
  hash_eq a b h := by
    have : a = b := LawfulBEq.eq_of_beq h
    rw [this]

/-- Cast a byte to a 256-bit word. -/
def ofUInt8 (b : UInt8) : UInt256 := ofNat b.toNat

/-- ADD: modular `a + b`. -/
def add (a b : UInt256) : UInt256 := ⟨a.val + b.val⟩
/-- Modular successor `a + 1`. Used by every `Step` rule that advances
    the program counter by one byte, and by transaction-level
    nonce bumps — sufficiently common that we give it a name.
    Defined via `add a (ofNat 1)` (rather than `⟨a.val + 1⟩`) so it is
    *definitionally* equal to the form `replaceStackAndIncrPC`
    produces, and the flat-record post-states keep matching `stepF`
    by `rfl`. -/
@[inline] def succ (a : UInt256) : UInt256 := add a (ofNat 1)
/-- SUB: modular `a - b`. -/
def sub (a b : UInt256) : UInt256 := ⟨a.val - b.val⟩
/-- MUL: modular `a * b`. -/
def mul (a b : UInt256) : UInt256 := ⟨a.val * b.val⟩
/-- DIV: integer division, `0` when `b = 0` (EVM convention). -/
def div (a b : UInt256) : UInt256 := if b.val.val = 0 then ⟨0⟩ else ⟨a.val / b.val⟩
/-- MOD: integer modulo, `0` when `b = 0`. -/
def mod (a b : UInt256) : UInt256 := if b.val.val = 0 then ⟨0⟩ else ⟨a.val % b.val⟩

/-- ADDMOD: `(a + b) mod n`, `0` when `n = 0`. -/
def addMod (a b n : UInt256) : UInt256 :=
  if n.val.val = 0 then ⟨0⟩ else ofNat ((a.toNat + b.toNat) % n.toNat)
/-- MULMOD: `(a * b) mod n`, `0` when `n = 0`. -/
def mulMod (a b n : UInt256) : UInt256 :=
  if n.val.val = 0 then ⟨0⟩ else ofNat ((a.toNat * b.toNat) % n.toNat)
/--
`EXP` specification: `a ^ b mod 2^256`. This is the clean mathematical
definition used by the relational semantics (`Step`). It is never *evaluated*
(the relation is a `Prop`), so the full `a.toNat ^ b.toNat` is harmless here.
The executable interpreter uses `expFast` instead — see the note there.
-/
def exp (a b : UInt256) : UInt256 := ofNat (a.toNat ^ b.toNat % UInt256.size)

/--
Square-and-multiply helper for `expFast`: returns `acc * base ^ e mod 2^256`,
reducing modulo `2^256` after every multiply and square so intermediate values
never exceed `2^256`. Recurses on `e / 2`, which terminates since `e / 2 < e`
whenever `e ≠ 0`.
-/
def expAux (base acc e : Nat) : Nat :=
  if h : e = 0 then acc
  else
    let acc' := if e % 2 = 1 then (acc * base) % UInt256.size else acc
    expAux ((base * base) % UInt256.size) acc' (e / 2)
  termination_by e
  decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

/--
Fast modular exponentiation for the *interpreter* (`stepF`) using square and multiply.
-/
def expFast (a b : UInt256) : UInt256 := ofNat (expAux (a.toNat % UInt256.size) 1 b.toNat)

/-- `expAux base acc e` computes `acc * base ^ e` modulo `2^256`.

    The squared base in the recursive call is reduced mod `size` after every
    square; `Nat.pow_mod` (`n^m % k = (n%k)^m % k`) lets us pull that inner
    reduction out of the surrounding multiplication and modulo, so the
    recursive step is just routine `mul_mod` / `pow_mod` shuffling. -/
theorem expAux_modEq (base acc e : Nat) :
    expAux base acc e % size = (acc * base ^ e) % size := by
  induction e using Nat.strong_induction_on generalizing base acc with
  | _ e ih =>
    unfold expAux
    split
    · next h => subst h; simp
    · next h =>
      have hlt : e / 2 < e := Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)
      rw [ih (e/2) hlt]
      have hpow : base ^ e = (base * base) ^ (e / 2) * base ^ (e % 2) := by
        rw [← Nat.pow_two, ← Nat.pow_mul, ← Nat.pow_add]
        congr 1; omega
      rw [hpow]
      rcases Nat.mod_two_eq_zero_or_one e with hpar | hpar
      · rw [if_neg (by omega), hpar, Nat.pow_zero, Nat.mul_one,
            Nat.mul_mod, ← Nat.pow_mod, ← Nat.mul_mod]
      · rw [if_pos hpar, hpar, Nat.pow_one,
            Nat.mul_mod, Nat.mod_mod, ← Nat.pow_mod, ← Nat.mul_mod]
        rw [Nat.mul_assoc, Nat.mul_comm base ((base*base)^(e/2))]

/-- The interpreter's `expFast` agrees with the `exp` specification. -/
theorem expFast_eq_exp (a b : UInt256) : expFast a b = exp a b := by
  unfold expFast exp ofNat
  congr 1
  apply Fin.ext
  simp only [Fin.ofNat]
  rw [expAux_modEq, Nat.one_mul, Nat.mod_mod, ← Nat.pow_mod]

/-- AND: bitwise conjunction. -/
def land (a b : UInt256) : UInt256 := ⟨Fin.land a.val b.val⟩
/-- OR: bitwise disjunction. -/
def lor (a b : UInt256) : UInt256  := ⟨Fin.lor a.val b.val⟩
/-- XOR: bitwise exclusive-or. -/
def xor (a b : UInt256) : UInt256  := ⟨Fin.xor a.val b.val⟩
/-- NOT: bitwise complement (256-bit). -/
def lnot (a : UInt256) : UInt256 := ofNat (UInt256.size - 1 - a.toNat)

/-- CLZ (EIP-7939): count of leading zero bits in the 256-bit word.
    `clz 0 = 256`; otherwise `255 - ⌊log₂ a⌋` (= `256 - bit_length a`), so a
    value with the high bit set gives `0` and `1` gives `255`. -/
def clz (a : UInt256) : UInt256 :=
  if a.toNat = 0 then ofNat 256 else ofNat (255 - Nat.log2 a.toNat)

/-- SHL: left-shift by `shift` bits; result is `0` if `shift ≥ 256`. -/
def shiftLeft (a shift : UInt256) : UInt256 :=
  if shift.toNat ≥ 256 then ⟨0⟩ else ofNat ((a.toNat <<< shift.toNat) % UInt256.size)
/-- SHR: logical right-shift by `shift` bits; result is `0` if `shift ≥ 256`. -/
def shiftRight (a shift : UInt256) : UInt256 :=
  if shift.toNat ≥ 256 then ⟨0⟩ else ⟨a.val >>> shift.val⟩

instance : Add UInt256 := ⟨add⟩
instance : Sub UInt256 := ⟨sub⟩
instance : Mul UInt256 := ⟨mul⟩
instance : Div UInt256 := ⟨div⟩
instance : Mod UInt256 := ⟨mod⟩
instance : AndOp UInt256 := ⟨land⟩
instance : OrOp UInt256 := ⟨lor⟩
instance : HXor UInt256 UInt256 UInt256 := ⟨xor⟩
instance : Complement UInt256 := ⟨lnot⟩
instance : LT UInt256 := ⟨fun a b => a.val < b.val⟩
instance : LE UInt256 := ⟨fun a b => a.val ≤ b.val⟩

instance (a b : UInt256) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.val < b.val))
instance (a b : UInt256) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.val ≤ b.val))

/-- Reinterpret a 256-bit word as a signed two's-complement integer. -/
def toSignedNat (a : UInt256) : Int :=
  let half : Nat := UInt256.size / 2
  if a.toNat < half then (a.toNat : Int) else (a.toNat : Int) - UInt256.size

/-- Pack a signed integer into a 256-bit word (two's complement). -/
def ofSignedInt (z : Int) : UInt256 :=
  ofNat ((z % (UInt256.size : Int)).toNat)

/-- Signed division (EVM `SDIV`): truncate toward zero, taking the
    dividend's sign; division by zero yields `0`.  Uses `Int.tdiv`
    (truncation toward zero) rather than Lean's default `Int./`
    (Euclidean), matching the EVM convention.  The `SDIV(-2^255, -1)`
    overflow edge case is handled automatically by the two's-complement
    round-trip through `ofSignedInt`. -/
def sdiv (a b : UInt256) : UInt256 :=
  if b.toNat = 0 then ⟨0⟩
  else ofSignedInt (a.toSignedNat.tdiv b.toSignedNat)

/-- Signed modulo (EVM `SMOD`): remainder takes the dividend's sign;
    modulo by zero yields `0`.  Uses `Int.tmod` (truncation toward zero)
    rather than Lean's default `Int.%` (Euclidean), matching the EVM
    convention. -/
def smod (a b : UInt256) : UInt256 :=
  if b.toNat = 0 then ⟨0⟩
  else ofSignedInt (a.toSignedNat.tmod b.toSignedNat)

/-- SLT: signed less-than, returning `1` or `0`. -/
def slt (a b : UInt256) : UInt256 :=
  if a.toSignedNat < b.toSignedNat then ofNat 1 else ofNat 0
/-- SGT: signed greater-than. -/
def sgt (a b : UInt256) : UInt256 :=
  if a.toSignedNat > b.toSignedNat then ofNat 1 else ofNat 0
/-- LT: unsigned less-than. -/
def lt (a b : UInt256) : UInt256 :=
  if a.toNat < b.toNat then ofNat 1 else ofNat 0
/-- GT: unsigned greater-than. -/
def gt (a b : UInt256) : UInt256 :=
  if a.toNat > b.toNat then ofNat 1 else ofNat 0
/-- EQ: equality test, returning `1` or `0`. -/
def eq (a b : UInt256) : UInt256 :=
  if a.toNat = b.toNat then ofNat 1 else ofNat 0
/-- ISZERO: returns `1` if `a = 0`, else `0`. -/
def isZero (a : UInt256) : UInt256 :=
  if a.toNat = 0 then ofNat 1 else ofNat 0

/--
Arithmetic shift right: sign-extends bit 255. Required by SAR.
-/
def sar (a shift : UInt256) : UInt256 :=
  if shift.toNat ≥ 256 then
    if a.toSignedNat < 0 then ofSignedInt (-1) else ⟨0⟩
  else
    let sv := a.toSignedNat
    ofSignedInt (sv / (2 ^ shift.toNat : Int))

/--
Sign-extend the integer `x` from `b+1` bytes wide to a full 256-bit word.
EVM SIGNEXTEND.
-/
def signExtend (b x : UInt256) : UInt256 :=
  if b.toNat ≥ 31 then x else
    let bitIndex : Nat := 8 * b.toNat + 7
    let mask : Nat := (1 <<< bitIndex.succ) - 1
    let signBit : Bool := (x.toNat >>> bitIndex) &&& 1 = 1
    if signBit then
      ofNat (x.toNat ||| ((UInt256.size - 1) ^^^ mask))
    else
      ofNat (x.toNat &&& mask)

/-- The single-byte extraction opcode BYTE. -/
def byteAt (i x : UInt256) : UInt256 :=
  if i.toNat ≥ 32 then ⟨0⟩ else
    ofNat ((x.toNat >>> (8 * (31 - i.toNat))) &&& 0xff)

end UInt256

/-- Alias for `UInt256` highlighting its use as the canonical EVM word. -/
abbrev EvmWord := UInt256

end EvmSemantics
