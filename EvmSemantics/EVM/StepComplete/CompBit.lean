module

public import EvmSemantics.EVM.StepComplete.Dispatch

/-!
`StepComplete.CompBit` — completeness cases for the CompBit constructors of
`StepRunning`: each constructor's premises force `stepF` to compute
exactly that constructor's successor. Assembled into
`stepRunning_complete` in `StepDeterminism.lean`.
-/

@[expose] public section

namespace EvmSemantics
namespace EVM
namespace StepComplete

/-- Completeness for `StepRunning.lt`. -/
theorem complete_lt (s : State) (a b : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .LT)
        (h_gas     : Gas.baseCost s.fork .LT ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: b :: rest)
        (h_cap   : s.stack.length + Operation.pushArity .LT
                     ≤ 1024 + Operation.popArity .LT)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := UInt256.lt a b :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .LT }
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  refine stepF_eq_ok ?_
  rw [stepFE_dispatch h_run h_np h_dec h_cap h_gas]
  simp only [stepF.compBit, h_stack]
  rfl

/-- Completeness for `StepRunning.gt`. -/
theorem complete_gt (s : State) (a b : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .GT)
        (h_gas     : Gas.baseCost s.fork .GT ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: b :: rest)
        (h_cap   : s.stack.length + Operation.pushArity .GT
                     ≤ 1024 + Operation.popArity .GT)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := UInt256.gt a b :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .GT }
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  refine stepF_eq_ok ?_
  rw [stepFE_dispatch h_run h_np h_dec h_cap h_gas]
  simp only [stepF.compBit, h_stack]
  rfl

/-- Completeness for `StepRunning.slt`. -/
theorem complete_slt (s : State) (a b : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .SLT)
        (h_gas     : Gas.baseCost s.fork .SLT ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: b :: rest)
        (h_cap   : s.stack.length + Operation.pushArity .SLT
                     ≤ 1024 + Operation.popArity .SLT)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := UInt256.slt a b :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .SLT }
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  refine stepF_eq_ok ?_
  rw [stepFE_dispatch h_run h_np h_dec h_cap h_gas]
  simp only [stepF.compBit, h_stack]
  rfl

/-- Completeness for `StepRunning.sgt`. -/
theorem complete_sgt (s : State) (a b : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .SGT)
        (h_gas     : Gas.baseCost s.fork .SGT ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: b :: rest)
        (h_cap   : s.stack.length + Operation.pushArity .SGT
                     ≤ 1024 + Operation.popArity .SGT)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := UInt256.sgt a b :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .SGT }
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  refine stepF_eq_ok ?_
  rw [stepFE_dispatch h_run h_np h_dec h_cap h_gas]
  simp only [stepF.compBit, h_stack]
  rfl

/-- Completeness for `StepRunning.eq`. -/
theorem complete_eq (s : State) (a b : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .EQ)
        (h_gas     : Gas.baseCost s.fork .EQ ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: b :: rest)
        (h_cap   : s.stack.length + Operation.pushArity .EQ
                     ≤ 1024 + Operation.popArity .EQ)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := UInt256.eq a b :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .EQ }
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  refine stepF_eq_ok ?_
  rw [stepFE_dispatch h_run h_np h_dec h_cap h_gas]
  simp only [stepF.compBit, h_stack]
  rfl

/-- Completeness for `StepRunning.iszero`. -/
theorem complete_iszero (s : State) (a : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .ISZERO)
        (h_gas     : Gas.baseCost s.fork .ISZERO ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: rest)
        (h_cap   : s.stack.length + Operation.pushArity .ISZERO
                     ≤ 1024 + Operation.popArity .ISZERO)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := UInt256.isZero a :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .ISZERO }
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  refine stepF_eq_ok ?_
  rw [stepFE_dispatch h_run h_np h_dec h_cap h_gas]
  simp only [stepF.compBit, h_stack]
  rfl

/-- Completeness for `StepRunning.and`. -/
theorem complete_and (s : State) (a b : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .AND)
        (h_gas     : Gas.baseCost s.fork .AND ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: b :: rest)
        (h_cap   : s.stack.length + Operation.pushArity .AND
                     ≤ 1024 + Operation.popArity .AND)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := UInt256.land a b :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .AND }
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  refine stepF_eq_ok ?_
  rw [stepFE_dispatch h_run h_np h_dec h_cap h_gas]
  simp only [stepF.compBit, h_stack]
  rfl

/-- Completeness for `StepRunning.or`. -/
theorem complete_or (s : State) (a b : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .OR)
        (h_gas     : Gas.baseCost s.fork .OR ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: b :: rest)
        (h_cap   : s.stack.length + Operation.pushArity .OR
                     ≤ 1024 + Operation.popArity .OR)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := UInt256.lor a b :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .OR }
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  refine stepF_eq_ok ?_
  rw [stepFE_dispatch h_run h_np h_dec h_cap h_gas]
  simp only [stepF.compBit, h_stack]
  rfl

/-- Completeness for `StepRunning.xor_`. -/
theorem complete_xor_ (s : State) (a b : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .XOR)
        (h_gas     : Gas.baseCost s.fork .XOR ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: b :: rest)
        (h_cap   : s.stack.length + Operation.pushArity .XOR
                     ≤ 1024 + Operation.popArity .XOR)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := UInt256.xor a b :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .XOR }
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  refine stepF_eq_ok ?_
  rw [stepFE_dispatch h_run h_np h_dec h_cap h_gas]
  simp only [stepF.compBit, h_stack]
  rfl

/-- Completeness for `StepRunning.not`. -/
theorem complete_not (s : State) (a : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .NOT)
        (h_gas     : Gas.baseCost s.fork .NOT ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: rest)
        (h_cap   : s.stack.length + Operation.pushArity .NOT
                     ≤ 1024 + Operation.popArity .NOT)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := UInt256.lnot a :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .NOT }
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  refine stepF_eq_ok ?_
  rw [stepFE_dispatch h_run h_np h_dec h_cap h_gas]
  simp only [stepF.compBit, h_stack]
  rfl

/-- Completeness for `StepRunning.clz`. -/
theorem complete_clz (s : State) (a : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .CLZ)
        (h_gas     : Gas.baseCost s.fork .CLZ ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: rest)
        (h_cap   : s.stack.length + Operation.pushArity .CLZ
                     ≤ 1024 + Operation.popArity .CLZ)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := UInt256.clz a :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .CLZ }
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  refine stepF_eq_ok ?_
  rw [stepFE_dispatch h_run h_np h_dec h_cap h_gas]
  simp only [stepF.compBit, h_stack]
  rfl

/-- Completeness for `StepRunning.byte_`. -/
theorem complete_byte_ (s : State) (i x : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .BYTE)
        (h_gas     : Gas.baseCost s.fork .BYTE ≤ s.gasAvailable)
        (h_stack   : s.stack = i :: x :: rest)
        (h_cap   : s.stack.length + Operation.pushArity .BYTE
                     ≤ 1024 + Operation.popArity .BYTE)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := UInt256.byteAt i x :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .BYTE }
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  refine stepF_eq_ok ?_
  rw [stepFE_dispatch h_run h_np h_dec h_cap h_gas]
  simp only [stepF.compBit, h_stack]
  rfl

/-- Completeness for `StepRunning.shl`. -/
theorem complete_shl (s : State) (shift v : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .SHL)
        (h_gas     : Gas.baseCost s.fork .SHL ≤ s.gasAvailable)
        (h_stack   : s.stack = shift :: v :: rest)
        (h_cap   : s.stack.length + Operation.pushArity .SHL
                     ≤ 1024 + Operation.popArity .SHL)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := UInt256.shiftLeft v shift :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .SHL }
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  refine stepF_eq_ok ?_
  rw [stepFE_dispatch h_run h_np h_dec h_cap h_gas]
  simp only [stepF.compBit, h_stack]
  rfl

/-- Completeness for `StepRunning.shr`. -/
theorem complete_shr (s : State) (shift v : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .SHR)
        (h_gas     : Gas.baseCost s.fork .SHR ≤ s.gasAvailable)
        (h_stack   : s.stack = shift :: v :: rest)
        (h_cap   : s.stack.length + Operation.pushArity .SHR
                     ≤ 1024 + Operation.popArity .SHR)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := UInt256.shiftRight v shift :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .SHR }
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  refine stepF_eq_ok ?_
  rw [stepFE_dispatch h_run h_np h_dec h_cap h_gas]
  simp only [stepF.compBit, h_stack]
  rfl

/-- Completeness for `StepRunning.sar`. -/
theorem complete_sar (s : State) (shift v : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .SAR)
        (h_gas     : Gas.baseCost s.fork .SAR ≤ s.gasAvailable)
        (h_stack   : s.stack = shift :: v :: rest)
        (h_cap   : s.stack.length + Operation.pushArity .SAR
                     ≤ 1024 + Operation.popArity .SAR)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := UInt256.sar v shift :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .SAR }
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  refine stepF_eq_ok ?_
  rw [stepFE_dispatch h_run h_np h_dec h_cap h_gas]
  simp only [stepF.compBit, h_stack]
  rfl

end StepComplete
end EVM
end EvmSemantics
