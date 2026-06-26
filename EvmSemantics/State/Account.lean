module

public import EvmSemantics.Data.UInt256

/-!
`AccountAddress` and `Account`.

Storage and the world `AccountMap` are modelled as **plain functions** —
`Storage = UInt256 → UInt256`, `AccountMap = AccountAddress → Account` —
to keep the relational semantics easy to reason about. Missing keys read
as the default value (0 for storage; the empty account for accounts), so
there is no `Option`-cluttered API.

Updates are `Function.update`: `s.set k v = fun k' => if k' = k then v else s k'`.
-/

@[expose] public section

namespace EvmSemantics

/-- 2^160 — EVM addresses are 20 bytes. -/
def AccountAddress.size : Nat := 2^160

instance : NeZero AccountAddress.size where
  out := by unfold AccountAddress.size; decide

/-- 20-byte Ethereum account address, modelled as `Fin (2^160)`. -/
abbrev AccountAddress : Type := Fin AccountAddress.size

namespace AccountAddress

/-- The address represented by `n`, taken modulo `2^160`. -/
def ofNat (n : Nat) : AccountAddress := Fin.ofNat _ n
/-- Truncate a 256-bit word to a 160-bit address (drops the high 96 bits). -/
def ofUInt256 (v : UInt256) : AccountAddress := Fin.ofNat _ (v.toNat % AccountAddress.size)
/-- Zero-extend an address to a 256-bit word. -/
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
  /-- `σ[a]ₙ` — nonce (number of transactions sent / contracts created). -/
  nonce    : UInt256
  /-- `σ[a]_b` — balance in wei. -/
  balance  : UInt256
  /-- `σ[a]_c` — the contract's bytecode (empty for externally-owned accounts). -/
  code     : ByteArray
  /-- `σ[a]_s` — persistent storage (SLOAD/SSTORE). -/
  storage  : Storage
  /-- `σ[a]_t` — transient storage (TLOAD/TSTORE, EIP-1153). -/
  tstorage : Storage

namespace Account

/-- The empty account (used as a default when looking up unknown addresses). -/
def empty : Account :=
  { nonce := ⟨0⟩, balance := ⟨0⟩, code := .empty
    storage := Storage.empty, tstorage := Storage.empty }

/-- An account is *empty* (EIP-161 "dead": zero nonce, zero balance, no code).
    A CALL transferring value into an empty account pays the `G_newaccount`
    surcharge for bringing it into existence. -/
def isEmpty (a : Account) : Bool :=
  a.nonce.toNat = 0 && a.balance.toNat = 0 && a.code.size = 0

end Account

instance : Inhabited Account := ⟨Account.empty⟩

/-- World state map: address → account. Total function; addresses not
    bound read as `Account.empty`. -/
abbrev AccountMap : Type := AccountAddress → Account

namespace AccountMap

/-- The empty world: every address maps to `Account.empty`. -/
def empty : AccountMap := fun _ => Account.empty
/-- Read the account at `a`. -/
@[reducible] def get (σ : AccountMap) (a : AccountAddress) : Account := σ a
/-- Update the account at `a`. -/
def set (σ : AccountMap) (a : AccountAddress) (acc : Account) : AccountMap :=
  fun a' => if a' = a then acc else σ a'

@[simp] theorem get_empty (a : AccountAddress) : AccountMap.empty a = Account.empty := rfl

@[simp] theorem get_set_same (σ : AccountMap) (a : AccountAddress) (acc : Account) :
    (σ.set a acc) a = acc := by simp [AccountMap.set]

@[simp] theorem get_set_other (σ : AccountMap) (a a' : AccountAddress) (acc : Account)
    (h : a' ≠ a) : (σ.set a acc) a' = σ a' := by simp [AccountMap.set, h]

/-- Move `v` wei from `src` to `dst`. Sequential updates so a self-transfer
    (`src = dst`) is a no-op on the balance. Underflow is the caller's
    responsibility to rule out (a CALL checks `balance ≥ value` first). -/
def transfer (σ : AccountMap) (src dst : AccountAddress) (v : UInt256) : AccountMap :=
  let σ₁ := σ.set src { (σ src) with balance := (σ src).balance - v }
  σ₁.set dst { (σ₁ dst) with balance := (σ₁ dst).balance + v }

end AccountMap

instance : Inhabited AccountMap := ⟨AccountMap.empty⟩

end EvmSemantics
