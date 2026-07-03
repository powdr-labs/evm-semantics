module

public import EvmSemantics.Data.UInt256
public import EvmSemantics.State.Account

/-!
`Substate` `A` — the accrued transaction-level "extra" state that EVM
execution updates: log entries, accessed accounts/keys for EIP-2929 warm
pricing, the self-destruct set, and the refund counter.

Address/key *sets* are modelled as predicates `α → Prop`. Membership is
`s a` (read: "`a` is in `s`"); union adds an alternative; the empty set
is `fun _ => False`. We're optimising for reasoning, not enumeration.

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

/-- A set of addresses, as a predicate. Used for the reasoning-oriented
    `selfDestructSet` / `touchedAccounts` fields (membership `s a`). The
    EIP-2929 warm sets below instead use computable `List`s, since `stepF`
    must *decide* warmth to pick the cold-vs-warm gas price. -/
abbrev AddressSet : Type := AccountAddress → Prop

namespace AddressSet

/-- The empty address set — nothing is in it. -/
def empty : AddressSet := fun _ => False

/-- Add `a` to `S`. Membership in `S.insert a` is "either equals `a` or
    was already in `S`". -/
def insert (S : AddressSet) (a : AccountAddress) : AddressSet :=
  fun a' => a' = a ∨ S a'

@[simp] theorem empty_def (a : AccountAddress) : (empty : AddressSet) a ↔ False :=
  Iff.rfl

@[simp] theorem mem_insert (S : AddressSet) (a a' : AccountAddress) :
    S.insert a a' ↔ a' = a ∨ S a' := Iff.rfl
end AddressSet

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
      `Tx.execute`'s end-of-tx cleanup pass (the YP §6.1 deletion of
      accounts in `Aₛ` from the world state), which can't iterate the
      `Prop`-valued `selfDestructSet` directly. May contain duplicates
      if `selfDestructTo` fires twice on the same account; the cleanup
      is idempotent (set-to-empty), so duplicates are harmless. -/
  selfDestructList    : Array AccountAddress
  /-- `Aₜ` — addresses that have been "touched" (read or written). -/
  touchedAccounts     : AddressSet
  /-- `Aᵣ` — refund counter accumulated from `SSTORE` clears. -/
  refundBalance       : UInt256
  /-- `Aₐ` — accounts already accessed in this transaction (EIP-2929 warm
      set). A computable `List` (not a `Prop` predicate) so `stepF` can
      decide warmth to choose the cold-vs-warm gas price; may contain
      duplicates (membership is all that matters). -/
  accessedAccounts    : List AccountAddress
  /-- `Aₖ` — storage slots already accessed in this transaction (EIP-2929
      warm set), keyed by `(owning address, slot)`. Computable `List`, as
      for `accessedAccounts`. -/
  accessedStorageKeys : List (AccountAddress × UInt256)
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
    accessedAccounts    := []
    accessedStorageKeys := []
    logSeries           := #[]
    originalAccountMap  := AccountMap.empty }

/-- Look up the `original` value of `(addr, key)` (its value at frame
    start). Used by SSTORE for EIP-1283 net-metered gas. -/
def originalStorage (A : Substate) (addr : AccountAddress) (key : UInt256) : UInt256 :=
  (A.originalAccountMap addr).storage key

/-- Is account `a` warm (already accessed this tx)? EIP-2929. -/
def isWarmAccount (A : Substate) (a : AccountAddress) : Bool :=
  decide (a ∈ A.accessedAccounts)

/-- Is storage slot `sk = (address, key)` warm (already accessed)? EIP-2929. -/
def isWarmStorageKey (A : Substate) (sk : AccountAddress × UInt256) : Bool :=
  decide (sk ∈ A.accessedStorageKeys)

/-- Mark `a` as a warm account in `A.accessedAccounts`. -/
def addAccessedAccount (A : Substate) (a : AccountAddress) : Substate :=
  { A with accessedAccounts := a :: A.accessedAccounts }

/-- Mark an *optional* account warm: warm `a` when `some a`, no-op on `none`.
    Used to warm an EIP-7702 delegate address (present only when the call
    target carries a delegation designator). -/
def addAccessedAccountOpt (A : Substate) : Option AccountAddress → Substate
  | some a => A.addAccessedAccount a
  | none   => A

/-- Mark `(addr, key)` as a warm storage slot in `A.accessedStorageKeys`. -/
def addAccessedStorageKey (A : Substate) (sk : AccountAddress × UInt256) : Substate :=
  { A with accessedStorageKeys := sk :: A.accessedStorageKeys }

/-- Append a LOG record to the substate's `logSeries`. -/
def appendLog (A : Substate) (entry : LogEntry) : Substate :=
  { A with logSeries := A.logSeries.push entry }

end Substate

instance : Inhabited Substate := ⟨Substate.empty⟩

end EvmSemantics
