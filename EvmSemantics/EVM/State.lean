import EvmSemantics.Data.UInt256
import EvmSemantics.Data.Stack
import EvmSemantics.Machine.SharedState
import EvmSemantics.EVM.Exception

/-!
`EVM.State` — the per-execution-frame state that the small-step relation
acts on. Extends `SharedState` with EVM-specific fields: program counter,
stack, exec-length counter, and a `halt` flag indicating that execution
has terminated (along with how — success, revert, or exception).
-/

namespace EvmSemantics

/-- How a frame terminates. `Running` means "still going". -/
inductive HaltKind where
  | Running
  | Success    -- STOP
  | Returned   -- RETURN (output stashed in `H_return`)
  | Reverted   -- REVERT (output stashed in `H_return`)
  | Exception (e : ExecutionException)
  deriving BEq, Repr, Inhabited

namespace EVM

structure State extends EvmSemantics.SharedState where
  pc         : UInt256
  stack      : Stack UInt256
  execLength : Nat
  halt       : HaltKind
  deriving Inhabited

namespace State

def isRunning (s : State) : Bool :=
  match s.halt with | .Running => true | _ => false

def isHalted (s : State) : Bool := ! s.isRunning

/-- Push a new stack and advance the pc by `pcΔ` (default 1). -/
def replaceStackAndIncrPC (s : State) (stk : Stack UInt256) (pcΔ : Nat := 1) : State :=
  { s with stack := stk, pc := s.pc + UInt256.ofNat pcΔ }

def incrPC (s : State) (pcΔ : Nat := 1) : State :=
  { s with pc := s.pc + UInt256.ofNat pcΔ }

def haltWith (s : State) (e : ExecutionException) : State :=
  { s with halt := .Exception e }

end State

end EVM
end EvmSemantics
