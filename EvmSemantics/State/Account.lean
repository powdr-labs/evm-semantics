module

public import EvmSemantics.Data.UInt256

/-!
`AccountAddress` and `Account`.

Storage and the world `AccountMap` are total maps with missing keys
reading as the default value (0 for storage; the empty account for
accounts), so there is no `Option`-cluttered API.

Both are split into a *spec view* (`toFun : Key → Val`, a
function-update chain — `s.set k v = fun k' => if k' = k then v else
s k'`) used exclusively by proofs, and a *runtime cache* (`cache :
Std.HashMap Key Val`) maintained by `@[implemented_by]` impls so the
compiled code reads/writes in O(1) average instead of walking the
closure chain. `CoeFun` makes `s k` desugar to `s.get k` so every
existing call site works unchanged.
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

/-- Persistent storage: a total map from 256-bit keys to 256-bit values.
    The "empty" storage maps every key to `0`.

    Same `toFun` / `cache` split as [[AccountMap]]: `toFun` is the spec
    view proofs reason about, `cache` is the runtime `Std.HashMap`-backed
    acceleration the `@[implemented_by]` impls maintain. A `CoeFun`
    instance lets every existing `s k` call site work unchanged. -/
structure Storage where
  /-- Spec view (function-update chain) — used only by proofs. -/
  toFun : UInt256 → UInt256
  /-- Runtime-only acceleration; ignored by proofs. -/
  cache : Std.HashMap UInt256 UInt256 := {}

namespace Storage

/-- Runtime impl of `.empty`. -/
@[inline] def emptyImpl : Storage where
  toFun := fun _ => ⟨0⟩
  cache := {}

/-- Runtime impl of `.get`: read from the cache, defaulting to `0`. -/
@[inline] def getImpl (s : Storage) (k : UInt256) : UInt256 :=
  s.cache.getD k ⟨0⟩

/-- Runtime impl of `.set`: insert into the cache; `toFun` preserved. -/
@[inline] def setImpl (s : Storage) (k v : UInt256) : Storage where
  toFun := s.toFun
  cache := s.cache.insert k v

/-- Storage that maps every key to `0`. -/
@[implemented_by emptyImpl]
def empty : Storage where
  toFun := fun _ => ⟨0⟩
  cache := {}

/-- Read the value bound to `k`. Spec view: `s.toFun k`. -/
@[implemented_by getImpl]
def get (s : Storage) (k : UInt256) : UInt256 := s.toFun k

/-- Update the binding of `k` to `v`. Spec view: wrap an `if`-chain. -/
@[implemented_by setImpl]
def set (s : Storage) (k v : UInt256) : Storage where
  toFun := fun k' => if k' = k then v else s.toFun k'
  cache := s.cache

/-- `s k` syntax goes through `Storage.get` via this `CoeFun` instance. -/
instance : CoeFun Storage (fun _ => UInt256 → UInt256) where
  coe s := s.get

@[simp] theorem get_empty (k : UInt256) : Storage.empty k = ⟨0⟩ := rfl

@[simp] theorem get_set_same (s : Storage) (k v : UInt256) :
    (s.set k v) k = v := by simp [Storage.set, Storage.get]

@[simp] theorem get_set_other (s : Storage) (k k' v : UInt256) (h : k' ≠ k) :
    (s.set k v) k' = s k' := by simp [Storage.set, Storage.get, h]

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
    address would overwrite a real one. Stricter than `isEmpty` because
    balance is **not** part of the check — a pre-funded address with no
    code and `nonce = 0` is still a valid creation target (the YP
    explicitly allows this so a forwarding address can be turned into a
    contract). Defined as `Bool` (not `Prop`) so `match` in `stepF`
    yields clean branches for the Equiv proof. -/
def isContract (a : Account) : Bool :=
  a.code.size != 0 || a.nonce.toNat != 0

end Account

instance : Inhabited Account := ⟨Account.empty⟩

/-- `AccountAddress` is `Fin (2^160)`, so `Hashable` reduces to hashing
    the underlying `Nat` representative. Required for the runtime
    `Std.HashMap`-backed `AccountMap` implementation. -/
instance : Hashable AccountAddress where
  hash a := hash a.val

/-- World state map: address → account. Total: addresses not bound read
    as `Account.empty`.

    The `toFun` field is the **spec view** the proofs reason about
    (a function-update chain). The `cache` field is the
    **runtime acceleration** — a `Std.HashMap` the `@[implemented_by]`
    impls maintain to give O(1)-average lookup. The spec is oblivious
    to `cache`; proofs only ever read `toFun`. A `CoeFun` instance
    lets every existing `σ a` call site work unchanged. -/
structure AccountMap where
  /-- The function-update view used by every proof. -/
  toFun : AccountAddress → Account
  /-- Runtime-only acceleration. The spec never reads this field;
      proofs ignore it. Maintained by the `@[implemented_by]` impls
      (`setImpl`) so `getImpl` can answer in O(1) average rather than
      walking a closure chain. Starts empty. -/
  cache : Std.HashMap AccountAddress Account := {}

namespace AccountMap

/-- Runtime impl of `.empty`. -/
@[inline] def emptyImpl : AccountMap where
  toFun := fun _ => Account.empty
  cache := {}

/-- Runtime impl of `.get`. -/
@[inline] def getImpl (σ : AccountMap) (a : AccountAddress) : Account :=
  σ.cache.getD a Account.empty

/-- Runtime impl of `.set`. -/
@[inline] def setImpl
    (σ : AccountMap) (a : AccountAddress) (acc : Account) : AccountMap where
  toFun := σ.toFun
  cache := σ.cache.insert a acc

/-- The empty world: every address maps to `Account.empty`. -/
@[implemented_by emptyImpl]
def empty : AccountMap where
  toFun := fun _ => Account.empty
  cache := {}

/-- Read the account at `a`. Spec view: just `σ.toFun a`. The runtime
    impl (see `getImpl`) reads from `σ.cache` instead. -/
@[implemented_by getImpl]
def get (σ : AccountMap) (a : AccountAddress) : Account := σ.toFun a

/-- Update the account at `a`. Spec view: wrap an `if`-chain on top of `σ.toFun`. -/
@[implemented_by setImpl]
def set (σ : AccountMap) (a : AccountAddress) (acc : Account) : AccountMap where
  toFun := fun a' => if a' = a then acc else σ.toFun a'
  cache := σ.cache

/-- `σ a` (the syntax every existing call site uses) goes through
    `AccountMap.get` via this `CoeFun` instance. Lean's elaborator sees
    `σ a` as `(coe σ) a = σ.get a`. -/
instance : CoeFun AccountMap (fun _ => AccountAddress → Account) where
  coe σ := σ.get

@[simp] theorem get_empty (a : AccountAddress) : AccountMap.empty a = Account.empty := rfl

@[simp] theorem get_set_same (σ : AccountMap) (a : AccountAddress) (acc : Account) :
    (σ.set a acc) a = acc := by simp [AccountMap.set, AccountMap.get]

@[simp] theorem get_set_other (σ : AccountMap) (a a' : AccountAddress) (acc : Account)
    (h : a' ≠ a) : (σ.set a acc) a' = σ a' := by simp [AccountMap.set, AccountMap.get, h]

/-- Move `v` wei from `src` to `dst`. Sequential updates so a self-transfer
    (`src = dst`) is a no-op on the balance. Underflow is the caller's
    responsibility to rule out (a CALL checks `balance ≥ value` first). -/
def transfer (σ : AccountMap) (src dst : AccountAddress) (v : UInt256) : AccountMap :=
  let σ₁ := σ.set src { (σ src) with balance := (σ src).balance - v }
  σ₁.set dst { (σ₁ dst) with balance := (σ₁ dst).balance + v }

end AccountMap

instance : Inhabited AccountMap := ⟨AccountMap.empty⟩

end EvmSemantics
