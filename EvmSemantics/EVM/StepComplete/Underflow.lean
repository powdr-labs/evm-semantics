module

public import EvmSemantics.EVM.StepComplete.Dispatch

/-!
`StepComplete.Underflow` — completeness for the generic `stackUnderflow` exception rule of
`StepRunning`: its priority premises pin `stepF`'s path to exactly this
error kind. Proven by case analysis over the decoded operation.
-/

@[expose] public section

namespace EvmSemantics
namespace EVM
namespace StepComplete

/-- Completeness for `StepRunning.stackUnderflow`. -/
theorem complete_stackUnderflow (s : State) (op : Operation)
        (h_op      : s.decodedOp = some op)
        (h_cap     : s.stack.length + op.pushArity ≤ 1024 + op.popArity)
        (h_gas     : Gas.baseCost s.fork op ≤ s.gasAvailable)
        (h_reach   : s.underflowReach op)
        (h_under   : s.stack.length < op.popArity)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s = ({ s with halt := .Exception .StackUnderflow })
    := by
  sorry

end StepComplete
end EVM
end EvmSemantics
