import EvmSemantics.Data.UInt256

/-!
`AccountAddress` and `Account`.

Storage and the world `AccountMap` are modelled as **plain functions** —
`Storage = UInt256 → UInt256`, `AccountMap = AccountAddress → Account` —
to keep the relational semantics easy to reason about. Missing keys read
as the default value (0 for storage; the empty account for accounts), so
there is no `Option`-cluttered API.

Updates are `Function.update`: `s.set k v = fun k' => if k' = k then v else s k'`.
-/

namespace EvmSemantics

/-- 2^160 — EVM addresses are 20 bytes. -/
def AccountAddress.size : Nat := 2^160

instance : NeZero AccountAddress.size where
  out := by unfold AccountAddress.size; decide

abbrev AccountAddress : Type := Fin AccountAddress.size

namespace AccountAddress

def ofNat (n : Nat) : AccountAddress := Fin.ofNat _ n
def ofUInt256 (v : UInt256) : AccountAddress := Fin.ofNat _ (v.toNat % AccountAddress.size)
def toUInt256 (a : AccountAddress) : UInt256 := UInt256.ofNat a.val
instance {n : Nat} : OfNat AccountAddress n := ⟨Fin.ofNat _ n⟩
instance : Inhabited AccountAddress := ⟨0⟩
instance : Ord AccountAddress where compare a b := compare a.val b.val

end AccountAddress

/-- Persistent storage: a total function from 256-bit keys to 256-bit
    values. The "empty" storage maps every key to `0`. -/
abbrev Storage : Type := UInt256 → UInt256

namespace Storage

/-- Storage that maps every key to `0`. -/
def empty : Storage := fun _ => ⟨0⟩

/-- Read the value bound to `k`. -/
@[reducible] def get (s : Storage) (k : UInt256) : UInt256 := s k

/-- Update the binding of `k` to `v`. -/
def set (s : Storage) (k v : UInt256) : Storage :=
  fun k' => if k' = k then v else s k'

@[simp] theorem get_empty (k : UInt256) : Storage.empty k = ⟨0⟩ := rfl

@[simp] theorem get_set_same (s : Storage) (k v : UInt256) :
    (s.set k v) k = v := by simp [Storage.set]

@[simp] theorem get_set_other (s : Storage) (k k' v : UInt256) (h : k' ≠ k) :
    (s.set k v) k' = s k' := by simp [Storage.set, h]

end Storage

instance : Inhabited Storage := ⟨Storage.empty⟩

/--
An EVM account. Matches Yellow Paper section 4.1 (minus the code-hash field,
which is computed from `code`).
-/
structure Account where
  nonce    : UInt256
  balance  : UInt256
  code     : ByteArray
  storage  : Storage
  tstorage : Storage

namespace Account

/-- The empty account (used as a default when looking up unknown addresses). -/
def empty : Account :=
  { nonce := ⟨0⟩, balance := ⟨0⟩, code := .empty
    storage := Storage.empty, tstorage := Storage.empty }

end Account

instance : Inhabited Account := ⟨Account.empty⟩

/-- World state map: address → account. Total function; addresses not
    bound read as `Account.empty`. -/
abbrev AccountMap : Type := AccountAddress → Account

namespace AccountMap

def empty : AccountMap := fun _ => Account.empty
@[reducible] def get (σ : AccountMap) (a : AccountAddress) : Account := σ a
def set (σ : AccountMap) (a : AccountAddress) (acc : Account) : AccountMap :=
  fun a' => if a' = a then acc else σ a'

@[simp] theorem get_empty (a : AccountAddress) : AccountMap.empty a = Account.empty := rfl

@[simp] theorem get_set_same (σ : AccountMap) (a : AccountAddress) (acc : Account) :
    (σ.set a acc) a = acc := by simp [AccountMap.set]

@[simp] theorem get_set_other (σ : AccountMap) (a a' : AccountAddress) (acc : Account)
    (h : a' ≠ a) : (σ.set a acc) a' = σ a' := by simp [AccountMap.set, h]

end AccountMap

instance : Inhabited AccountMap := ⟨AccountMap.empty⟩

end EvmSemantics
