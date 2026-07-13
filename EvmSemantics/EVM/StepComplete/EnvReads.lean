module

public import EvmSemantics.EVM.StepComplete.Dispatch

/-!
`StepComplete.EnvReads` — completeness cases for the EnvReads constructors of
`StepRunning`: each constructor's premises force `stepF` to compute
exactly that constructor's successor. Assembled into
`stepRunning_complete` in `StepDeterminism.lean`.
-/

@[expose] public section

namespace EvmSemantics
namespace EVM
namespace StepComplete

/-- Completeness for `StepRunning.address`. -/
theorem complete_address (s : State)
        (h_op      : s.decodedOp = some .ADDRESS)
        (h_gas     : Gas.baseCost s.fork .ADDRESS ≤ s.gasAvailable)
        (h_cap     : s.stack.length < 1024)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := s.executionEnv.address.toUInt256 :: s.stack
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .ADDRESS }
    := by
  sorry

/-- Completeness for `StepRunning.balance`. -/
theorem complete_balance (s : State) (addr : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .BALANCE)
        (h_gas     : Gas.balanceTotal s addr ≤ s.gasAvailable)
        (h_stack   : s.stack = addr :: rest)
        (h_cap   : s.stack.length + Operation.pushArity .BALANCE
                     ≤ 1024 + Operation.popArity .BALANCE)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := (s.accountMap (AccountAddress.ofUInt256 addr)).balance :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.balanceTotal s addr
              substate     := s.substate.addAccessedAccount
                                (AccountAddress.ofUInt256 addr) }
    := by
  sorry

/-- Completeness for `StepRunning.origin`. -/
theorem complete_origin (s : State)
        (h_op      : s.decodedOp = some .ORIGIN)
        (h_gas     : Gas.baseCost s.fork .ORIGIN ≤ s.gasAvailable)
        (h_cap     : s.stack.length < 1024)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := s.executionEnv.origin.toUInt256 :: s.stack
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .ORIGIN }
    := by
  sorry

/-- Completeness for `StepRunning.caller`. -/
theorem complete_caller (s : State)
        (h_op      : s.decodedOp = some .CALLER)
        (h_gas     : Gas.baseCost s.fork .CALLER ≤ s.gasAvailable)
        (h_cap     : s.stack.length < 1024)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := s.executionEnv.caller.toUInt256 :: s.stack
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .CALLER }
    := by
  sorry

/-- Completeness for `StepRunning.callvalue`. -/
theorem complete_callvalue (s : State)
        (h_op      : s.decodedOp = some .CALLVALUE)
        (h_gas     : Gas.baseCost s.fork .CALLVALUE ≤ s.gasAvailable)
        (h_cap     : s.stack.length < 1024)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := s.executionEnv.weiValue :: s.stack
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .CALLVALUE }
    := by
  sorry

/-- Completeness for `StepRunning.calldataload`. -/
theorem complete_calldataload (s : State) (i : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .CALLDATALOAD)
        (h_gas     : Gas.baseCost s.fork .CALLDATALOAD ≤ s.gasAvailable)
        (h_stack   : s.stack = i :: rest)
        (h_cap   : s.stack.length + Operation.pushArity .CALLDATALOAD
                     ≤ 1024 + Operation.popArity .CALLDATALOAD)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := MachineState.readWord s.executionEnv.calldata i.toNat :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .CALLDATALOAD }
    := by
  sorry

/-- Completeness for `StepRunning.calldatasize`. -/
theorem complete_calldatasize (s : State)
        (h_op      : s.decodedOp = some .CALLDATASIZE)
        (h_gas     : Gas.baseCost s.fork .CALLDATASIZE ≤ s.gasAvailable)
        (h_cap     : s.stack.length < 1024)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := UInt256.ofNat s.executionEnv.calldata.size :: s.stack
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .CALLDATASIZE }
    := by
  sorry

/-- Completeness for `StepRunning.codesize`. -/
theorem complete_codesize (s : State)
        (h_op      : s.decodedOp = some .CODESIZE)
        (h_gas     : Gas.baseCost s.fork .CODESIZE ≤ s.gasAvailable)
        (h_cap     : s.stack.length < 1024)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := UInt256.ofNat s.executionEnv.code.size :: s.stack
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .CODESIZE }
    := by
  sorry

/-- Completeness for `StepRunning.gasprice`. -/
theorem complete_gasprice (s : State)
        (h_op      : s.decodedOp = some .GASPRICE)
        (h_gas     : Gas.baseCost s.fork .GASPRICE ≤ s.gasAvailable)
        (h_cap     : s.stack.length < 1024)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := s.executionEnv.gasPrice :: s.stack
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .GASPRICE }
    := by
  sorry

/-- Completeness for `StepRunning.extcodesize`. -/
theorem complete_extcodesize (s : State) (addr : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .EXTCODESIZE)
        (h_gas     : Gas.extcodesizeTotal s addr ≤ s.gasAvailable)
        (h_stack   : s.stack = addr :: rest)
        (h_cap   : s.stack.length + Operation.pushArity .EXTCODESIZE
                     ≤ 1024 + Operation.popArity .EXTCODESIZE)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := UInt256.ofNat
                                (s.accountMap (AccountAddress.ofUInt256 addr)).code.size
                              :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.extcodesizeTotal s addr
              substate     := s.substate.addAccessedAccount
                                (AccountAddress.ofUInt256 addr) }
    := by
  sorry

/-- Completeness for `StepRunning.returndatasize`. -/
theorem complete_returndatasize (s : State)
        (h_op      : s.decodedOp = some .RETURNDATASIZE)
        (h_gas     : Gas.baseCost s.fork .RETURNDATASIZE ≤ s.gasAvailable)
        (h_cap     : s.stack.length < 1024)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := UInt256.ofNat s.returnData.size :: s.stack
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .RETURNDATASIZE }
    := by
  sorry

/-- Completeness for `StepRunning.extcodehash`. -/
theorem complete_extcodehash (s : State) (addr : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .EXTCODEHASH)
        (h_gas     : Gas.extcodehashTotal s addr ≤ s.gasAvailable)
        (h_stack   : s.stack = addr :: rest)
        (h_cap   : s.stack.length + Operation.pushArity .EXTCODEHASH
                     ≤ 1024 + Operation.popArity .EXTCODEHASH)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := (s.accountMap (AccountAddress.ofUInt256 addr)).codeHash :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.extcodehashTotal s addr
              substate     := s.substate.addAccessedAccount
                                (AccountAddress.ofUInt256 addr) }
    := by
  sorry

end StepComplete
end EVM
end EvmSemantics
