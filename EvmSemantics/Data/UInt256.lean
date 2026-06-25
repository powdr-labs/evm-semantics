import Mathlib.Data.Fin.Basic

/-!
`UInt256` — 256-bit unsigned EVM words.

A faithful subset of `EvmYul.UInt256`. We model it as a `Fin (2^256)` wrapper,
provide modular arithmetic (`+`, `-`, `*`, `/`, `%`), bitwise ops, comparisons,
and a small zoo of conversions used by the relational rules.
-/

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

instance : OfNat UInt256 n := ⟨ofNat n⟩
instance : Inhabited UInt256 := ⟨ofNat 0⟩
instance : Repr UInt256 where reprPrec u _ := repr u.toNat
instance : ToString UInt256 where toString u := toString u.toNat

/-- Cast a byte to a 256-bit word. -/
def ofUInt8 (b : UInt8) : UInt256 := ofNat b.toNat

/-- ADD: modular `a + b`. -/
def add (a b : UInt256) : UInt256 := ⟨a.val + b.val⟩
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
/-- EXP: `a^b mod 2^256`. -/
def exp (a b : UInt256) : UInt256 := ofNat (a.toNat ^ b.toNat % UInt256.size)

/-- AND: bitwise conjunction. -/
def land (a b : UInt256) : UInt256 := ⟨Fin.land a.val b.val⟩
/-- OR: bitwise disjunction. -/
def lor (a b : UInt256) : UInt256  := ⟨Fin.lor a.val b.val⟩
/-- XOR: bitwise exclusive-or. -/
def xor (a b : UInt256) : UInt256  := ⟨Fin.xor a.val b.val⟩
/-- NOT: bitwise complement (256-bit). -/
def lnot (a : UInt256) : UInt256 := ofNat (UInt256.size - 1 - a.toNat)

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
