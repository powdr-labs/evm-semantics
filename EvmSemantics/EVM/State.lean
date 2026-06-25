module

public import EvmSemantics.Data.UInt256
public import EvmSemantics.Data.Stack
public import EvmSemantics.Machine.SharedState
public import EvmSemantics.EVM.Exception

/-!
`EVM.State` — the per-execution-frame state that the small-step relation
acts on. Extends `SharedState` with EVM-specific fields: program counter,
stack, exec-length counter, and a `halt` flag indicating that execution
has terminated (along with how — success, revert, or exception).
-/

@[expose] public section

namespace EvmSemantics

/-- How a frame terminates. `Running` means "still going". -/
inductive HaltKind where
  | Running
  | Success    -- STOP
  | Returned   -- RETURN (output stashed in `hReturn`)
  | Reverted   -- REVERT (output stashed in `hReturn`)
  | Exception (e : ExecutionException)
  deriving BEq, Repr, Inhabited

namespace EVM

/-- Per-execution-frame state — extends `SharedState` with EVM-specific
    fields (PC, stack, exec counter, halt flag). -/
structure State extends EvmSemantics.SharedState where
  /-- Program counter into the executing bytecode. -/
  pc         : UInt256
  /-- Operand stack (top of stack is `stack.head`). -/
  stack      : Stack UInt256
  /-- Number of instructions executed so far in this frame. -/
  execLength : Nat
  /-- Termination status (`.Running` while still executing). -/
  halt       : HaltKind
  deriving Inhabited

namespace State

/-- True iff the frame has not yet halted. -/
def isRunning (s : State) : Bool :=
  match s.halt with | .Running => true | _ => false

/-- Negation of `isRunning`. -/
def isHalted (s : State) : Bool := ! s.isRunning

/-- Push a new stack and advance the pc by `pcΔ` (default 1). -/
def replaceStackAndIncrPC (s : State) (stk : Stack UInt256) (pcΔ : Nat := 1) : State :=
  { s with stack := stk, pc := s.pc + UInt256.ofNat pcΔ }

/-- Advance the pc by `pcΔ` (default 1) without touching the stack. -/
def incrPC (s : State) (pcΔ : Nat := 1) : State :=
  { s with pc := s.pc + UInt256.ofNat pcΔ }

/-- Transition into the exception-halt state for `e`. -/
def haltWith (s : State) (e : ExecutionException) : State :=
  { s with halt := .Exception e }

end State

end EVM
end EvmSemantics
