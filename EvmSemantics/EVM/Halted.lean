import EvmSemantics.EVM.State

/-!
`ExecutionResult` and halt-related lemmas.

The small-step relation `Step` produces a sequence of `EVM.State`s where
the `halt` field eventually leaves `.Running`. The big-step relation
`Eval` summarises a complete execution as an `ExecutionResult`, projecting
the final state's `halt` + output buffer down to a flat sum.
-/

namespace EvmSemantics
namespace EVM

/-- The summarised outcome of running a frame to completion. -/
inductive ExecutionResult where
  /-- STOP: ordinary termination, no return data. -/
  | success
  /-- RETURN: ordinary termination, with return data. -/
  | returned (output : ByteArray)
  /-- REVERT: state changes are rolled back, output buffer is returned. -/
  | reverted (output : ByteArray)
  /-- Halt due to an `ExecutionException` (out-of-gas, bad jump, …). -/
  | exception (e : ExecutionException)
  deriving Inhabited

namespace State

/-- Project a halted `State`'s `halt` field to an `ExecutionResult`,
    pulling the output buffer from `hReturn` when appropriate. -/
def toResult (s : State) : ExecutionResult :=
  match s.halt with
  | .Running     => .exception .InvalidInstruction  -- defensive default
  | .Success     => .success
  | .Returned    => .returned s.hReturn
  | .Reverted    => .reverted s.hReturn
  | .Exception e => .exception e

@[simp] theorem toResult_success (s : State) (h : s.halt = .Success) :
    s.toResult = .success := by simp [toResult, h]

@[simp] theorem toResult_returned (s : State) (h : s.halt = .Returned) :
    s.toResult = .returned s.hReturn := by simp [toResult, h]

@[simp] theorem toResult_reverted (s : State) (h : s.halt = .Reverted) :
    s.toResult = .reverted s.hReturn := by simp [toResult, h]

@[simp] theorem toResult_exception (s : State) (e : ExecutionException)
    (h : s.halt = .Exception e) : s.toResult = .exception e := by
  simp [toResult, h]

end State

end EVM
end EvmSemantics
