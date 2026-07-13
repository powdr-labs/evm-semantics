module

public import EvmSemantics.EVM.StepComplete.Dispatch

/-!
`StepComplete.Exceptions` — completeness cases for the Exceptions constructors of
`StepRunning`: each constructor's premises force `stepF` to compute
exactly that constructor's successor. Assembled into
`stepRunning_complete` in `StepDeterminism.lean`.
-/

@[expose] public section

namespace EvmSemantics
namespace EVM
namespace StepComplete

/-- Completeness for `StepRunning.decodeFailure`. -/
theorem complete_decodeFailure (s : State)
        (h_none    : s.decoded = none)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s = ({ s with halt := .Exception .InvalidInstruction })
    := by
  exact stepF_eq_error (stepFE_decodeNone h_run h_np h_none)

/-- Completeness for `StepRunning.invalidOpcode`. -/
theorem complete_invalidOpcode (s : State)
        (h_op      : s.decodedOp = some .INVALID)
        (h_cap     : s.stack.length + Operation.pushArity .INVALID
                       ≤ 1024 + Operation.popArity .INVALID)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s = ({ s with halt := .Exception .InvalidInstruction })
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  refine stepF_eq_error ?_
  rw [stepFE_dispatch h_run h_np h_dec h_cap (Nat.zero_le _)]
  simp only [stepF.system]


/-- Completeness for `StepRunning.initCodeSizeOog`. -/
theorem complete_initCodeSizeOog (s : State) (op : Operation)
        (value offset size : UInt256) (rest : List UInt256)
        (h_op       : s.decodedOp = some op)
        (h_create   : op = .System .CREATE ∨ op = .System .CREATE2)
        (h_cap      : s.stack.length + op.pushArity ≤ 1024 + op.popArity)
        (h_gas      : Gas.baseCost s.fork op ≤ s.gasAvailable)
        (h_stack    : s.stack = value :: offset :: size :: rest)
        (h_perm     : s.executionEnv.permitStateMutation = true)
        (h_large    : Gas.initCodeTooLarge s.fork size.toNat = true)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s = ({ s with halt := .Exception .OutOfGas })
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  refine stepF_eq_error ?_
  rcases h_create with rfl | rfl
  · rw [stepFE_dispatch h_run h_np h_dec h_cap h_gas]
    simp only [stepF.system, h_stack]
    rw [if_neg (by simp [h_perm]), if_pos h_large]
  · rw [stepFE_dispatch h_run h_np h_dec h_cap h_gas]
    simp only [stepF.system, h_stack]
    -- UNPROVABLE AS STATED (design-level gap, not to be fixed here).
    -- For CREATE2, `stepF.system` matches four stack items
    -- (`value :: offset :: size :: salt :: rest`) *before* the
    -- `initCodeTooLarge` OutOfGas check, but the premises only pin three
    -- items (`h_stack : s.stack = value :: offset :: size :: rest`) with
    -- `rest` unconstrained. When `rest = []` the executable takes the
    -- underflow arm and returns `.error .StackUnderflow`, not
    -- `.error .OutOfGas`, so the goal is false. The rule
    -- `StepRunning.initCodeSizeOog` (Step.lean) would need an extra
    -- `4 ≤ s.stack.length` premise (or a `salt` in `h_stack`) for the
    -- CREATE2 disjunct; changing it is a design decision outside this task.
    sorry


/-- Completeness for `StepRunning.stackOverflow`. -/
theorem complete_stackOverflow (s : State) (op : Operation)
        (h_op      : s.decodedOp = some op)
        (h_pop_ok  : op.popArity ≤ s.stack.length)
        (h_over    : s.stack.length - op.popArity + op.pushArity > 1024)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s = ({ s with halt := .Exception .StackOverflow })
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  refine stepF_eq_error ?_
  exact stepFE_overflow h_run h_np h_dec (by omega)

/-- Completeness for `StepRunning.staticModeViolation`. -/
theorem complete_staticModeViolation (s : State) (op : Operation)
        (h_op      : s.decodedOp = some op)
        (h_mut     : op.isStateMutating = true)
        (h_cap     : s.stack.length + op.pushArity ≤ 1024 + op.popArity)
        (h_gas     : Gas.baseCost s.fork op ≤ s.gasAvailable)
        (h_reach   : s.staticReach op)
        (h_perm    : s.executionEnv.permitStateMutation = false)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s = ({ s with halt := .Exception .StaticModeViolation })
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  refine stepF_eq_error ?_
  rw [stepFE_dispatch h_run h_np h_dec h_cap h_gas]
  cases op with
  | StopArith o => simp [Operation.isStateMutating] at h_mut
  | CompBit o => simp [Operation.isStateMutating] at h_mut
  | Keccak o => simp [Operation.isStateMutating] at h_mut
  | Env o => simp [Operation.isStateMutating] at h_mut
  | Block o => simp [Operation.isStateMutating] at h_mut
  | Push o => simp [Operation.isStateMutating] at h_mut
  | Dup o => simp [Operation.isStateMutating] at h_mut
  | Swap o => simp [Operation.isStateMutating] at h_mut
  | DupN o => simp [Operation.isStateMutating] at h_mut
  | SwapN o => simp [Operation.isStateMutating] at h_mut
  | Exchange o => simp [Operation.isStateMutating] at h_mut
  | Log o => simp [stepF.log, h_perm, static]
  | StackMemFlow o =>
    cases o <;>
      simp_all [Operation.isStateMutating, stepF.stackMemFlow, static]
  | System o =>
    cases o with
    | CALL => simp [Operation.isStateMutating] at h_mut
    | CALLCODE => simp [Operation.isStateMutating] at h_mut
    | RETURN => simp [Operation.isStateMutating] at h_mut
    | REVERT => simp [Operation.isStateMutating] at h_mut
    | DELEGATECALL => simp [Operation.isStateMutating] at h_mut
    | STATICCALL => simp [Operation.isStateMutating] at h_mut
    | INVALID => simp [Operation.isStateMutating] at h_mut
    | CREATE =>
      simp only [State.staticReach] at h_reach
      simp only [stepF.system]
      match hs : s.stack, h_reach with
      | a :: b :: c :: rest, _ => simp [h_perm, static]
      | [], h => simp at h
      | [_], h => simp at h
      | [_, _], h => simp at h
    | CREATE2 =>
      simp only [State.staticReach] at h_reach
      simp only [stepF.system]
      match hs : s.stack, h_reach with
      | a :: b :: c :: d :: rest, _ => simp [h_perm, static]
      | [], h => simp at h
      | [_], h => simp at h
      | [_, _], h => simp at h
      | [_, _, _], h => simp at h
    | SELFDESTRUCT =>
      simp only [State.staticReach] at h_reach
      simp only [stepF.system]
      match hs : s.stack, h_reach with
      | a :: rest, _ => simp [h_perm, static]
      | [], h => simp at h

/-- Completeness for `StepRunning.jumpBadDest`. -/
theorem complete_jumpBadDest (s : State) (dest : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .JUMP)
        (h_cap     : s.stack.length + Operation.pushArity .JUMP
                       ≤ 1024 + Operation.popArity .JUMP)
        (h_gas     : Gas.baseCost s.fork .JUMP ≤ s.gasAvailable)
        (h_stack   : s.stack = dest :: rest)
        (h_bad     : Decode.isValidJumpDest s.executionEnv.code dest.toNat = false)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s = ({ s with halt := .Exception .BadJumpDestination })
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  refine stepF_eq_error ?_
  rw [stepFE_dispatch h_run h_np h_dec h_cap h_gas]
  simp only [stepF.stackMemFlow, h_stack]
  rw [if_neg (by simp [h_bad])]

/-- Completeness for `StepRunning.jumpiBadDest`. -/
theorem complete_jumpiBadDest (s : State) (dest cond : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .JUMPI)
        (h_cap     : s.stack.length + Operation.pushArity .JUMPI
                       ≤ 1024 + Operation.popArity .JUMPI)
        (h_gas     : Gas.baseCost s.fork .JUMPI ≤ s.gasAvailable)
        (h_stack   : s.stack = dest :: cond :: rest)
        (h_cond    : UInt256.isTrue cond)
        (h_bad     : Decode.isValidJumpDest s.executionEnv.code dest.toNat = false)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s = ({ s with halt := .Exception .BadJumpDestination })
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  refine stepF_eq_error ?_
  rw [stepFE_dispatch h_run h_np h_dec h_cap h_gas]
  simp only [stepF.stackMemFlow, h_stack]
  rw [if_neg h_cond, if_neg (by simp [h_bad])]

/-- Completeness for `StepRunning.returndatacopyOob`. -/
theorem complete_returndatacopyOob (s : State) (destOff srcOff sz : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .RETURNDATACOPY)
        (h_cap     : s.stack.length + Operation.pushArity .RETURNDATACOPY
                       ≤ 1024 + Operation.popArity .RETURNDATACOPY)
        (h_gas     : Gas.baseCost s.fork .RETURNDATACOPY ≤ s.gasAvailable)
        (h_stack   : s.stack = destOff :: srcOff :: sz :: rest)
        (h_oob     : srcOff.toNat + sz.toNat > s.returnData.size)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s = ({ s with halt := .Exception .InvalidMemoryAccess })
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  refine stepF_eq_error ?_
  rw [stepFE_dispatch h_run h_np h_dec h_cap h_gas]
  simp only [stepF.env, h_stack]
  rw [if_pos h_oob]

end StepComplete
end EVM
end EvmSemantics
