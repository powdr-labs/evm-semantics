module

public import EvmSemantics.Data.UInt256
public import EvmSemantics.State.Account

/-!
`Substate` `A` — the accrued transaction-level "extra" state that EVM
execution updates: log entries, accessed accounts/keys for EIP-2929 warm
pricing, the self-destruct set, and the refund counter.

Address / (address × key) sets are `Std.HashSet` for decidable
membership at runtime — that's what EIP-2929 needs for warm-vs-cold
gas pricing, and it also lets `SELFDESTRUCT` refund idempotency
(YP §7 "each address contributes at most once") be expressed directly.
The previous `Prop`-valued predicate representation forced a parallel
`Array` mirror; that redundancy is gone.

The `logSeries` stays an `Array` since we genuinely need to inspect it
in order (and append at the end).
-/

@[expose] public section

namespace EvmSemantics

/-- A single LOG record: the contract address that emitted it, the
    indexed topics, and the unindexed data bytes. -/
structure LogEntry where
  /-- Address of the contract that emitted the log (`Iₐ` at emit time). -/
  address : AccountAddress
  /-- The indexed topics (`#topics ∈ [0, 4]`, enforced by `StepRunning.log`). -/
  topics  : Array UInt256
  /-- The unindexed data bytes — a copy of `memory[offset..offset+size]`. -/
  data    : ByteArray
  deriving Inhabited

/-- The ordered list of LOG records emitted during execution. -/
abbrev LogSeries := Array LogEntry

/-- A decidable-membership set of addresses. -/
abbrev AddressSet : Type := Std.HashSet AccountAddress

/-- A decidable-membership set of `(address, storage-key)` pairs. -/
abbrev StorageKeySet : Type := Std.HashSet (AccountAddress × UInt256)

namespace AddressSet
/-- The empty address set. -/
def empty : AddressSet := ∅
end AddressSet

namespace StorageKeySet
/-- The empty storage-key set. -/
def empty : StorageKeySet := ∅
end StorageKeySet

-- `insert` and `contains` on both sets go straight through the underlying
-- `Std.HashSet` methods — no wrapping needed since `AddressSet` and
-- `StorageKeySet` are `abbrev`s. Consumers write `S.insert a`, `S.contains a`
-- verbatim.

/-- The accrued substate `A` (Yellow Paper §6.1) tracked across an
    execution: addresses self-destructed, addresses touched, refund
    counter, accessed-account / accessed-storage-key sets (EIP-2929),
    in-order log series, and a snapshot of the storage at frame start
    used by SSTORE to look up the "original" value (EIP-1283 / EIP-2200). -/
structure Substate where
  /-- `Aₛ` — addresses scheduled to be deleted at the end of the transaction. -/
  selfDestructSet     : AddressSet
  /-- Iterable parallel to `selfDestructSet`: the list of addresses that
      `SELFDESTRUCT`ed in this transaction, in insertion order. Used by
      `Tx.execute`'s end-of-tx cleanup pass (YP §6.1). The set gives
      idempotent-refund membership; the list gives ordered iteration
      that the set can't (HashSet has no defined iteration order). -/
  selfDestructList    : Array AccountAddress
  /-- `Aₜ` — addresses that have been "touched" (read or written). -/
  touchedAccounts     : AddressSet
  /-- `Aᵣ` — refund counter accumulated from `SSTORE` clears. -/
  refundBalance       : UInt256
  /-- `Aₐ` — accounts already accessed in this transaction (warm — EIP-2929). -/
  accessedAccounts    : AddressSet
  /-- `Aₖ` — storage slots already accessed in this transaction (EIP-2929). -/
  accessedStorageKeys : StorageKeySet
  /-- `Aₗ` — ordered list of LOG records emitted so far. -/
  logSeries           : LogSeries
  /-- Snapshot of the storage at frame start, used by SSTORE to find the
      `original` value of a slot (EIP-1283 / EIP-2200). For VMTests this
      is initialised from the pre-state's `accountMap`. -/
  originalAccountMap  : AccountMap

namespace Substate

/-- The empty substate: nothing self-destructed, nothing touched, no
    refunds, no accesses, no logs, all slots originally 0. -/
def empty : Substate :=
  { selfDestructSet     := AddressSet.empty
    selfDestructList    := #[]
    touchedAccounts     := AddressSet.empty
    refundBalance       := ⟨0⟩
    accessedAccounts    := AddressSet.empty
    accessedStorageKeys := StorageKeySet.empty
    logSeries           := #[]
    originalAccountMap  := AccountMap.empty }

/-- Look up the `original` value of `(addr, key)` (its value at frame
    start). Used by SSTORE for EIP-1283 net-metered gas. -/
def originalStorage (A : Substate) (addr : AccountAddress) (key : UInt256) : UInt256 :=
  (A.originalAccountMap addr).storage key

/-- Mark `a` as a warm account in `A.accessedAccounts`. -/
def addAccessedAccount (A : Substate) (a : AccountAddress) : Substate :=
  { A with accessedAccounts := A.accessedAccounts.insert a }

/-- `true` iff `a` is already warm — EIP-2929 gas-pricing predicate. -/
def isWarmAccount (A : Substate) (a : AccountAddress) : Bool :=
  A.accessedAccounts.contains a

/-- Mark `(addr, key)` as a warm storage slot in `A.accessedStorageKeys`. -/
def addAccessedStorageKey (A : Substate) (sk : AccountAddress × UInt256) : Substate :=
  { A with accessedStorageKeys := A.accessedStorageKeys.insert sk }

/-- `true` iff `(addr, key)` is already warm — EIP-2929 gas-pricing predicate. -/
def isWarmStorageKey (A : Substate) (sk : AccountAddress × UInt256) : Bool :=
  A.accessedStorageKeys.contains sk

/-- Append a LOG record to the substate's `logSeries`. -/
def appendLog (A : Substate) (entry : LogEntry) : Substate :=
  { A with logSeries := A.logSeries.push entry }

end Substate

instance : Inhabited Substate := ⟨Substate.empty⟩

end EvmSemantics
