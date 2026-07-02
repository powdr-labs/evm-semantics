module

public import EvmSemantics.Data.UInt256

/-!
`AccountAddress` and `Account`.

Storage and the world `AccountMap` are total maps from a 256-bit
(resp. 160-bit) key to a value; missing keys read as the default
(0 for storage; the empty account for accounts), so there is no
`Option`-cluttered API. Underneath both are `Std.HashMap`s — one
representation for both spec and runtime, so reasoning is direct
(no spec-vs-runtime bridge to prove). A `CoeFun` instance lets every
existing `s k` / `σ a` call site work unchanged.
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

/-- `AccountAddress` is `Fin (2^160)`, so `Hashable` reduces to hashing
    the underlying `Nat` representative. -/
instance : Hashable AccountAddress where
  hash a := hash a.val
instance : LawfulHashable AccountAddress where
  hash_eq a b h := by
    have : a = b := LawfulBEq.eq_of_beq h
    rw [this]

/-- Persistent storage: a `Std.HashMap` from 256-bit keys to 256-bit
    values, with absent keys reading as `⟨0⟩`. The "empty" storage is
    the empty hash map. -/
abbrev Storage : Type := Std.HashMap UInt256 UInt256

namespace Storage

/-- Storage that maps every key to `⟨0⟩` (the empty `HashMap`). -/
def empty : Storage := ∅

/-- Read the value bound to `k`, defaulting to `⟨0⟩`. -/
@[reducible] def get (s : Storage) (k : UInt256) : UInt256 := s.getD k ⟨0⟩

/-- Update the binding of `k` to `v`. -/
def set (s : Storage) (k v : UInt256) : Storage := s.insert k v

/-- `s k` syntax goes through `Storage.get` via this `CoeFun` instance. -/
instance : CoeFun Storage (fun _ => UInt256 → UInt256) where
  coe s := s.get

@[simp] theorem get_empty (k : UInt256) : Storage.empty k = ⟨0⟩ := by
  show (∅ : Std.HashMap UInt256 UInt256).getD k ⟨0⟩ = ⟨0⟩
  simp

@[simp] theorem get_set_same (s : Storage) (k v : UInt256) :
    (s.set k v) k = v := by
  show (s.insert k v).getD k ⟨0⟩ = v
  simp

@[simp] theorem get_set_other (s : Storage) (k k' v : UInt256) (h : k' ≠ k) :
    (s.set k v) k' = s k' := by
  show (s.insert k v).getD k' ⟨0⟩ = s.getD k' ⟨0⟩
  rw [Std.HashMap.getD_insert]
  have hbeq : (k == k') = false := by
    apply decide_eq_false
    intro hval
    apply h
    cases k; cases k'; exact congrArg UInt256.mk hval.symm
  simp [hbeq]

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

/-- CREATE/CREATE2 target collision (Yellow Paper `ζ(a, σ) = ⊥`): an
    account *exists* in the sense that creating a new contract at this
    address would overwrite a real one. Balance is **not** part of the
    check — a pre-funded address with no code, `nonce = 0`, and no
    storage is still a valid creation target (the YP explicitly allows
    this so a forwarding address can be turned into a contract).
    Storage **is** included: an address whose storage trie is already
    populated is treated as colliding (matches geth's
    `storageRoot != EmptyRootHash` check in `core/vm/evm.go`; later
    codified as EIP-7610). Defined as `Bool` (not `Prop`) so `match`
    in `stepF` yields clean branches for the Equiv proof. -/
def isContract (a : Account) : Bool :=
  a.code.size != 0 || a.nonce.toNat != 0 || !a.storage.isEmpty

/-- EIP-2681 nonce ceiling: `2^64 - 1`. The account nonce is a `u64`, so a
    sender that has reached this value can originate no further transactions
    or CREATE/CREATE2s — the required nonce increment would leave the range.
    Both are rejected before any nonce bump (a transaction is invalid; a
    CREATE/CREATE2 pushes `0` like the depth/balance failure). -/
def maxNonce : Nat := 2 ^ 64 - 1

end Account

instance : Inhabited Account := ⟨Account.empty⟩

/-- World state map: address → account, as a `Std.HashMap`. Missing
    addresses read as `Account.empty`. Same shape as [[Storage]]. -/
abbrev AccountMap : Type := Std.HashMap AccountAddress Account

namespace AccountMap

/-- The empty world: every address maps to `Account.empty`. -/
def empty : AccountMap := ∅

/-- Read the account at `a`, defaulting to `Account.empty`. -/
@[reducible] def get (σ : AccountMap) (a : AccountAddress) : Account :=
  σ.getD a Account.empty

/-- Update the account at `a`. -/
def set (σ : AccountMap) (a : AccountAddress) (acc : Account) : AccountMap :=
  σ.insert a acc

/-- `σ a` syntax goes through `AccountMap.get` via this `CoeFun` instance. -/
instance : CoeFun AccountMap (fun _ => AccountAddress → Account) where
  coe σ := σ.get

@[simp] theorem get_empty (a : AccountAddress) : AccountMap.empty a = Account.empty := by
  show (∅ : Std.HashMap AccountAddress Account).getD a Account.empty = Account.empty
  simp

@[simp] theorem get_set_same (σ : AccountMap) (a : AccountAddress) (acc : Account) :
    (σ.set a acc) a = acc := by
  show (σ.insert a acc).getD a Account.empty = acc
  simp

@[simp] theorem get_set_other (σ : AccountMap) (a a' : AccountAddress) (acc : Account)
    (h : a' ≠ a) : (σ.set a acc) a' = σ a' := by
  show (σ.insert a acc).getD a' Account.empty = σ.getD a' Account.empty
  rw [Std.HashMap.getD_insert]
  have hbeq : (a == a') = false := by
    apply decide_eq_false
    intro hval; exact h hval.symm
  simp [hbeq]

/-- Move `v` wei from `src` to `dst`. Sequential updates so a self-transfer
    (`src = dst`) is a no-op on the balance. Underflow is the caller's
    responsibility to rule out (a CALL checks `balance ≥ value` first). -/
def transfer (σ : AccountMap) (src dst : AccountAddress) (v : UInt256) : AccountMap :=
  let σ₁ := σ.set src { (σ src) with balance := (σ src).balance - v }
  σ₁.set dst { (σ₁ dst) with balance := (σ₁ dst).balance + v }

end AccountMap

instance : Inhabited AccountMap := ⟨AccountMap.empty⟩

end EvmSemantics
