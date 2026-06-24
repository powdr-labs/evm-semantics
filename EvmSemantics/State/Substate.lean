import EvmSemantics.Data.UInt256
import EvmSemantics.State.Account

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

namespace EvmSemantics

structure LogEntry where
  address : AccountAddress
  topics  : Array UInt256
  data    : ByteArray
  deriving Inhabited

abbrev LogSeries := Array LogEntry

/-- A set of addresses, as a predicate. -/
abbrev AddressSet : Type := AccountAddress → Prop

/-- A set of (address, storage-key) pairs. -/
abbrev StorageKeySet : Type := AccountAddress × UInt256 → Prop

namespace AddressSet
def empty : AddressSet := fun _ => False
def insert (S : AddressSet) (a : AccountAddress) : AddressSet :=
  fun a' => a' = a ∨ S a'

@[simp] theorem empty_def (a : AccountAddress) : (empty : AddressSet) a ↔ False :=
  Iff.rfl

@[simp] theorem mem_insert (S : AddressSet) (a a' : AccountAddress) :
    S.insert a a' ↔ a' = a ∨ S a' := Iff.rfl
end AddressSet

namespace StorageKeySet
def empty : StorageKeySet := fun _ => False
def insert (S : StorageKeySet) (sk : AccountAddress × UInt256) : StorageKeySet :=
  fun sk' => sk' = sk ∨ S sk'

@[simp] theorem mem_insert (S : StorageKeySet) (sk sk' : AccountAddress × UInt256) :
    S.insert sk sk' ↔ sk' = sk ∨ S sk' := Iff.rfl
end StorageKeySet

structure Substate where
  selfDestructSet     : AddressSet
  touchedAccounts     : AddressSet
  refundBalance       : UInt256
  accessedAccounts    : AddressSet
  accessedStorageKeys : StorageKeySet
  logSeries           : LogSeries

namespace Substate

def empty : Substate :=
  { selfDestructSet     := AddressSet.empty
    touchedAccounts     := AddressSet.empty
    refundBalance       := ⟨0⟩
    accessedAccounts    := AddressSet.empty
    accessedStorageKeys := StorageKeySet.empty
    logSeries           := #[] }

def addAccessedAccount (A : Substate) (a : AccountAddress) : Substate :=
  { A with accessedAccounts := A.accessedAccounts.insert a }

def addAccessedStorageKey (A : Substate) (sk : AccountAddress × UInt256) : Substate :=
  { A with accessedStorageKeys := A.accessedStorageKeys.insert sk }

def appendLog (A : Substate) (entry : LogEntry) : Substate :=
  { A with logSeries := A.logSeries.push entry }

end Substate

instance : Inhabited Substate := ⟨Substate.empty⟩

end EvmSemantics
