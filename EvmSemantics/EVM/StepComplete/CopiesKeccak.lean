module

public import EvmSemantics.EVM.StepComplete.Dispatch

/-!
`StepComplete.CopiesKeccak` — completeness cases for the CopiesKeccak constructors of
`StepRunning`: each constructor's premises force `stepF` to compute
exactly that constructor's successor. Assembled into
`stepRunning_complete` in `StepDeterminism.lean`.
-/

@[expose] public section

namespace EvmSemantics
namespace EVM
namespace StepComplete

/-- Completeness for `StepRunning.keccak256`. -/
theorem complete_keccak256 (s : State) (offset size : UInt256) (rest : List UInt256)
        (h_op    : s.decodedOp = some .KECCAK256)
        (h_stack : s.stack = offset :: size :: rest)
        (h_gas   : Gas.keccakTotal s offset size ≤ s.gasAvailable)
        (h_cap   : s.stack.length + Operation.pushArity .KECCAK256
                     ≤ 1024 + Operation.popArity .KECCAK256)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := EvmSemantics.keccak256
                                (MachineState.readPadded s.memory
                                  offset.toNat size.toNat) :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.keccakTotal s offset size
              activeWords  := s.activeWordsAfterUInt256 offset.toNat size.toNat }
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  have hg : Gas.baseCost s.fork (.Keccak .KECCAK256)
      + MachineState.memExpansionDelta s.activeWords.toNat offset.toNat size.toNat
      + Gas.keccakWordCost size ≤ s.gasAvailable := h_gas
  have h_base : Gas.baseCost s.fork (.Keccak .KECCAK256) ≤ s.gasAvailable := by omega
  have h_mem : (s.consumeGas (Gas.baseCost s.fork (.Keccak .KECCAK256))
      h_base).canExpandMemory offset.toNat size.toNat := by
    simp only [State.canExpandMemory, State.consumeGas]
    omega
  have h_dyn : Gas.keccakWordCost size ≤
      ((s.consumeGas (Gas.baseCost s.fork (.Keccak .KECCAK256)) h_base).consumeMemExp
        offset.toNat size.toNat h_mem).gasAvailable := by
    simp only [MachineState.memExpansionDelta] at hg
    simp only [State.consumeMemExp, State.consumeGas]
    omega
  refine stepF_eq_ok ?_
  rw [stepFE_dispatch h_run h_np h_dec h_cap h_base]
  simp only [stepF.keccak, h_stack]
  unfold chargeMem
  simp only [dif_pos h_mem, dif_pos h_dyn]
  simp [State.consumeGas, State.consumeMemExp, State.replaceStackAndIncrPC,
        State.activeWordsAfterUInt256, Gas.keccakTotal, UInt256.succ,
        MachineState.memExpansionDelta,
        show ∀ (a b : UInt256), a + b = a.add b from fun _ _ => rfl]
  grind

/-- Completeness for `StepRunning.calldatacopy`. -/
theorem complete_calldatacopy (s : State) (destOff srcOff sz : UInt256) (rest : List UInt256)
        (h_op    : s.decodedOp = some .CALLDATACOPY)
        (h_stack : s.stack = destOff :: srcOff :: sz :: rest)
        (h_gas   : Gas.calldatacopyTotal s destOff sz ≤ s.gasAvailable)
        (h_cap   : s.stack.length + Operation.pushArity .CALLDATACOPY
                     ≤ 1024 + Operation.popArity .CALLDATACOPY)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.calldatacopyTotal s destOff sz
              activeWords  := s.activeWordsAfterUInt256 destOff.toNat sz.toNat
              memory       := MachineState.writeBytes s.memory
                                (MachineState.readPadded s.executionEnv.calldata
                                  srcOff.toNat sz.toNat)
                                destOff.toNat }
    := by
  sorry

/-- Completeness for `StepRunning.codecopy`. -/
theorem complete_codecopy (s : State) (destOff srcOff sz : UInt256) (rest : List UInt256)
        (h_op    : s.decodedOp = some .CODECOPY)
        (h_stack : s.stack = destOff :: srcOff :: sz :: rest)
        (h_gas   : Gas.codecopyTotal s destOff sz ≤ s.gasAvailable)
        (h_cap   : s.stack.length + Operation.pushArity .CODECOPY
                     ≤ 1024 + Operation.popArity .CODECOPY)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.codecopyTotal s destOff sz
              activeWords  := s.activeWordsAfterUInt256 destOff.toNat sz.toNat
              memory       := MachineState.writeBytes s.memory
                                (MachineState.readPadded s.executionEnv.code
                                  srcOff.toNat sz.toNat)
                                destOff.toNat }
    := by
  sorry

/-- Completeness for `StepRunning.extcodecopy`. -/
theorem complete_extcodecopy (s : State) (addr destOff srcOff sz : UInt256) (rest : List UInt256)
        (h_op    : s.decodedOp = some .EXTCODECOPY)
        (h_stack : s.stack = addr :: destOff :: srcOff :: sz :: rest)
        (h_gas   : Gas.extcodecopyTotal s addr destOff sz ≤ s.gasAvailable)
        (h_cap   : s.stack.length + Operation.pushArity .EXTCODECOPY
                     ≤ 1024 + Operation.popArity .EXTCODECOPY)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.extcodecopyTotal s addr destOff sz
              activeWords  := s.activeWordsAfterUInt256 destOff.toNat sz.toNat
              memory       := MachineState.writeBytes s.memory
                                (MachineState.readPadded
                                  (s.accountMap (AccountAddress.ofUInt256 addr)).code
                                  srcOff.toNat sz.toNat)
                                destOff.toNat
              substate     := s.substate.addAccessedAccount
                                (AccountAddress.ofUInt256 addr) }
    := by
  sorry

/-- Completeness for `StepRunning.returndatacopy`. -/
theorem complete_returndatacopy (s : State) (destOff srcOff sz : UInt256) (rest : List UInt256)
        (h_op       : s.decodedOp = some .RETURNDATACOPY)
        (h_stack    : s.stack = destOff :: srcOff :: sz :: rest)
        (h_inbounds : srcOff.toNat + sz.toNat ≤ s.returnData.size)
        (h_gas      : Gas.returndatacopyTotal s destOff sz ≤ s.gasAvailable)
        (h_cap   : s.stack.length + Operation.pushArity .RETURNDATACOPY
                     ≤ 1024 + Operation.popArity .RETURNDATACOPY)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.returndatacopyTotal s destOff sz
              activeWords  := s.activeWordsAfterUInt256 destOff.toNat sz.toNat
              memory       := MachineState.writeBytes s.memory
                                (MachineState.readPadded s.returnData
                                  srcOff.toNat sz.toNat)
                                destOff.toNat }
    := by
  sorry

end StepComplete
end EVM
end EvmSemantics
