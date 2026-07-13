module

public import EvmSemantics.EVM.StepComplete.Dispatch

/-!
`StepComplete.Arith` — completeness cases for the Arith constructors of
`StepRunning`: each constructor's premises force `stepF` to compute
exactly that constructor's successor. Assembled into
`stepRunning_complete` in `StepDeterminism.lean`.
-/

@[expose] public section

namespace EvmSemantics
namespace EVM
namespace StepComplete

/-- Completeness for `StepRunning.add`. -/
theorem complete_add (s : State) (a b : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .ADD)
        (h_gas     : Gas.baseCost s.fork .ADD ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: b :: rest)
        (h_cap   : s.stack.length + Operation.pushArity .ADD
                     ≤ 1024 + Operation.popArity .ADD)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := (a + b) :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .ADD }
    := by
  sorry

/-- Completeness for `StepRunning.mul`. -/
theorem complete_mul (s : State) (a b : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .MUL)
        (h_gas     : Gas.baseCost s.fork .MUL ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: b :: rest)
        (h_cap   : s.stack.length + Operation.pushArity .MUL
                     ≤ 1024 + Operation.popArity .MUL)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := (a * b) :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .MUL }
    := by
  sorry

/-- Completeness for `StepRunning.sub`. -/
theorem complete_sub (s : State) (a b : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .SUB)
        (h_gas     : Gas.baseCost s.fork .SUB ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: b :: rest)
        (h_cap   : s.stack.length + Operation.pushArity .SUB
                     ≤ 1024 + Operation.popArity .SUB)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := (a - b) :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .SUB }
    := by
  sorry

/-- Completeness for `StepRunning.div`. -/
theorem complete_div (s : State) (a b : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .DIV)
        (h_gas     : Gas.baseCost s.fork .DIV ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: b :: rest)
        (h_cap   : s.stack.length + Operation.pushArity .DIV
                     ≤ 1024 + Operation.popArity .DIV)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := (a / b) :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .DIV }
    := by
  sorry

/-- Completeness for `StepRunning.sdiv`. -/
theorem complete_sdiv (s : State) (a b : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .SDIV)
        (h_gas     : Gas.baseCost s.fork .SDIV ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: b :: rest)
        (h_cap   : s.stack.length + Operation.pushArity .SDIV
                     ≤ 1024 + Operation.popArity .SDIV)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := UInt256.sdiv a b :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .SDIV }
    := by
  sorry

/-- Completeness for `StepRunning.mod`. -/
theorem complete_mod (s : State) (a b : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .MOD)
        (h_gas     : Gas.baseCost s.fork .MOD ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: b :: rest)
        (h_cap   : s.stack.length + Operation.pushArity .MOD
                     ≤ 1024 + Operation.popArity .MOD)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := (a % b) :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .MOD }
    := by
  sorry

/-- Completeness for `StepRunning.smod`. -/
theorem complete_smod (s : State) (a b : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .SMOD)
        (h_gas     : Gas.baseCost s.fork .SMOD ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: b :: rest)
        (h_cap   : s.stack.length + Operation.pushArity .SMOD
                     ≤ 1024 + Operation.popArity .SMOD)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := UInt256.smod a b :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .SMOD }
    := by
  sorry

/-- Completeness for `StepRunning.addmod`. -/
theorem complete_addmod (s : State) (a b n : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .ADDMOD)
        (h_gas     : Gas.baseCost s.fork .ADDMOD ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: b :: n :: rest)
        (h_cap   : s.stack.length + Operation.pushArity .ADDMOD
                     ≤ 1024 + Operation.popArity .ADDMOD)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := UInt256.addMod a b n :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .ADDMOD }
    := by
  sorry

/-- Completeness for `StepRunning.mulmod`. -/
theorem complete_mulmod (s : State) (a b n : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .MULMOD)
        (h_gas     : Gas.baseCost s.fork .MULMOD ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: b :: n :: rest)
        (h_cap   : s.stack.length + Operation.pushArity .MULMOD
                     ≤ 1024 + Operation.popArity .MULMOD)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := UInt256.mulMod a b n :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .MULMOD }
    := by
  sorry

/-- Completeness for `StepRunning.exp`. -/
theorem complete_exp (s : State) (a b : UInt256) (rest : List UInt256)
        (h_op    : s.decodedOp = some .EXP)
        (h_gas   : Gas.baseCost s.fork .EXP + Gas.expByteCost s.fork b ≤ s.gasAvailable)
        (h_stack : s.stack = a :: b :: rest)
        (h_cap   : s.stack.length + Operation.pushArity .EXP
                     ≤ 1024 + Operation.popArity .EXP)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := UInt256.exp a b :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .EXP
                              - Gas.expByteCost s.fork b }
    := by
  sorry

/-- Completeness for `StepRunning.signextend`. -/
theorem complete_signextend (s : State) (b x : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .SIGNEXTEND)
        (h_gas     : Gas.baseCost s.fork .SIGNEXTEND ≤ s.gasAvailable)
        (h_stack   : s.stack = b :: x :: rest)
        (h_cap   : s.stack.length + Operation.pushArity .SIGNEXTEND
                     ≤ 1024 + Operation.popArity .SIGNEXTEND)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := UInt256.signExtend b x :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .SIGNEXTEND }
    := by
  sorry

/-- Completeness for `StepRunning.stop`. -/
theorem complete_stop (s : State)
        (h_op      : s.decodedOp = some .STOP)
        (h_cap   : s.stack.length + Operation.pushArity .STOP
                     ≤ 1024 + Operation.popArity .STOP)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s = { s with halt := .Success, hReturn := .empty }
    := by
  sorry

end StepComplete
end EVM
end EvmSemantics
