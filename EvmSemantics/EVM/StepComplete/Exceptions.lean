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
  sorry


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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

end StepComplete
end EVM
end EvmSemantics
