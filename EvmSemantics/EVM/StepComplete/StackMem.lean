module

public import EvmSemantics.EVM.StepComplete.Dispatch

/-!
`StepComplete.StackMem` — completeness cases for the StackMem constructors of
`StepRunning`: each constructor's premises force `stepF` to compute
exactly that constructor's successor. Assembled into
`stepRunning_complete` in `StepDeterminism.lean`.
-/

@[expose] public section

namespace EvmSemantics
namespace EVM
namespace StepComplete

/-- Completeness for `StepRunning.pop`. -/
theorem complete_pop (s : State) (a : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .POP)
        (h_gas     : Gas.baseCost s.fork .POP ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: rest)
        (h_cap   : s.stack.length + Operation.pushArity .POP
                     ≤ 1024 + Operation.popArity .POP)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .POP }
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  refine stepF_eq_ok ?_
  rw [stepFE_dispatch h_run h_np h_dec h_cap h_gas]
  simp only [stepF.stackMemFlow, h_stack]
  rfl

/-- Completeness for `StepRunning.mload`. -/
theorem complete_mload (s : State) (offset : UInt256) (rest : List UInt256)
        (h_op    : s.decodedOp = some .MLOAD)
        (h_stack : s.stack = offset :: rest)
        (h_gas   : Gas.mloadTotal s offset ≤ s.gasAvailable)
        (h_cap   : s.stack.length + Operation.pushArity .MLOAD
                     ≤ 1024 + Operation.popArity .MLOAD)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := MachineState.readWord s.memory offset.toNat :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.mloadTotal s offset
              activeWords  := s.activeWordsAfterUInt256 offset.toNat 32 }
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  have hL : Gas.mloadTotal s offset
      = Gas.baseCost s.fork .MLOAD
        + MachineState.memExpansionDelta s.activeWords.toNat offset.toNat 32 := rfl
  have h_base : Gas.baseCost s.fork .MLOAD ≤ s.gasAvailable := by rw [hL] at h_gas; omega
  refine stepF_eq_ok ?_
  rw [stepFE_dispatch h_run h_np h_dec h_cap h_base]
  simp only [stepF.stackMemFlow, h_stack]
  have h_mem : (s.consumeGas (Gas.baseCost s.fork .MLOAD) h_base).canExpandMemory
                 offset.toNat 32 := by
    simp only [State.canExpandMemory, State.consumeGas]; rw [hL] at h_gas; omega
  simp only [chargeMem, dif_pos h_mem]
  simp only [State.consumeGas, State.consumeMemExp, State.replaceStackAndIncrPC,
    State.activeWordsAfterUInt256, Gas.mloadTotal, UInt256.succ,
    MachineState.memExpansionDelta, MachineState.mload,
    show ∀ (a b : UInt256), a + b = a.add b from fun _ _ => rfl]
  grind

/-- Completeness for `StepRunning.mstore`. -/
theorem complete_mstore (s : State) (offset value : UInt256) (rest : List UInt256)
        (h_op    : s.decodedOp = some .MSTORE)
        (h_stack : s.stack = offset :: value :: rest)
        (h_gas   : Gas.mstoreTotal s offset ≤ s.gasAvailable)
        (h_cap   : s.stack.length + Operation.pushArity .MSTORE
                     ≤ 1024 + Operation.popArity .MSTORE)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.mstoreTotal s offset
              memory       := MachineState.writeBytes s.memory
                                (Data.Bytes.natToBytesPadded value.toNat 32) offset.toNat
              activeWords  := s.activeWordsAfterUInt256 offset.toNat 32 }
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  have hL : Gas.mstoreTotal s offset
      = Gas.baseCost s.fork .MSTORE
        + MachineState.memExpansionDelta s.activeWords.toNat offset.toNat 32 := rfl
  have h_base : Gas.baseCost s.fork .MSTORE ≤ s.gasAvailable := by rw [hL] at h_gas; omega
  refine stepF_eq_ok ?_
  rw [stepFE_dispatch h_run h_np h_dec h_cap h_base]
  simp only [stepF.stackMemFlow, h_stack]
  have h_mem : (s.consumeGas (Gas.baseCost s.fork .MSTORE) h_base).canExpandMemory
                 offset.toNat 32 := by
    simp only [State.canExpandMemory, State.consumeGas]; rw [hL] at h_gas; omega
  simp only [chargeMem, dif_pos h_mem]
  simp only [State.consumeGas, State.consumeMemExp, State.replaceStackAndIncrPC,
    State.activeWordsAfterUInt256, Gas.mstoreTotal, UInt256.succ,
    MachineState.memExpansionDelta, MachineState.mstore,
    show ∀ (a b : UInt256), a + b = a.add b from fun _ _ => rfl]
  grind

/-- Completeness for `StepRunning.mstore8`. -/
theorem complete_mstore8 (s : State) (offset value : UInt256) (rest : List UInt256)
        (h_op    : s.decodedOp = some .MSTORE8)
        (h_stack : s.stack = offset :: value :: rest)
        (h_gas   : Gas.mstore8Total s offset ≤ s.gasAvailable)
        (h_cap   : s.stack.length + Operation.pushArity .MSTORE8
                     ≤ 1024 + Operation.popArity .MSTORE8)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.mstore8Total s offset
              memory       := MachineState.writeBytes s.memory
                                (ByteArray.mk #[UInt8.ofNat (value.toNat % 256)])
                                offset.toNat
              activeWords  := s.activeWordsAfterUInt256 offset.toNat 1 }
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  have hL : Gas.mstore8Total s offset
      = Gas.baseCost s.fork .MSTORE8
        + MachineState.memExpansionDelta s.activeWords.toNat offset.toNat 1 := rfl
  have h_base : Gas.baseCost s.fork .MSTORE8 ≤ s.gasAvailable := by rw [hL] at h_gas; omega
  refine stepF_eq_ok ?_
  rw [stepFE_dispatch h_run h_np h_dec h_cap h_base]
  simp only [stepF.stackMemFlow, h_stack]
  have h_mem : (s.consumeGas (Gas.baseCost s.fork .MSTORE8) h_base).canExpandMemory
                 offset.toNat 1 := by
    simp only [State.canExpandMemory, State.consumeGas]; rw [hL] at h_gas; omega
  simp only [chargeMem, dif_pos h_mem]
  simp only [State.consumeGas, State.consumeMemExp, State.replaceStackAndIncrPC,
    State.activeWordsAfterUInt256, Gas.mstore8Total, UInt256.succ,
    MachineState.memExpansionDelta, MachineState.mstore8,
    show ∀ (a b : UInt256), a + b = a.add b from fun _ _ => rfl]
  grind

/-- Completeness for `StepRunning.msize`. -/
theorem complete_msize (s : State)
        (h_op      : s.decodedOp = some .MSIZE)
        (h_gas     : Gas.baseCost s.fork .MSIZE ≤ s.gasAvailable)
        (h_cap     : s.stack.length < 1024)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := MachineState.msize s.toMachineState :: s.stack
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .MSIZE }
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  refine stepF_eq_ok ?_
  rw [stepFE_dispatch h_run h_np h_dec
        (by simp only [Operation.pushArity, Operation.popArity]; omega) h_gas]
  simp only [stepF.stackMemFlow]
  rfl

/-- Completeness for `StepRunning.mcopy`. -/
theorem complete_mcopy (s : State) (destOff srcOff sz : UInt256) (rest : List UInt256)
        (h_op    : s.decodedOp = some .MCOPY)
        (h_stack : s.stack = destOff :: srcOff :: sz :: rest)
        (h_gas   : Gas.mcopyTotal s destOff srcOff sz ≤ s.gasAvailable)
        (h_cap   : s.stack.length + Operation.pushArity .MCOPY
                     ≤ 1024 + Operation.popArity .MCOPY)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.mcopyTotal s destOff srcOff sz
              memory       := MachineState.writeBytes s.memory
                                (MachineState.readPadded s.memory
                                  srcOff.toNat sz.toNat)
                                destOff.toNat
              activeWords  := s.activeWordsAfterUInt256_2
                                destOff.toNat sz.toNat srcOff.toNat sz.toNat }
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  have hL : Gas.mcopyTotal s destOff srcOff sz
      = Gas.baseCost s.fork .MCOPY
        + MachineState.memExpansionDelta2 s.activeWords.toNat
            destOff.toNat sz.toNat srcOff.toNat sz.toNat
        + Gas.copyWordCost sz := rfl
  have h_base : Gas.baseCost s.fork .MCOPY ≤ s.gasAvailable := by rw [hL] at h_gas; omega
  refine stepF_eq_ok ?_
  rw [stepFE_dispatch h_run h_np h_dec h_cap h_base]
  simp only [stepF.stackMemFlow, h_stack]
  have h_mem : (s.consumeGas (Gas.baseCost s.fork .MCOPY) h_base).canExpandMemory2
                 destOff.toNat sz.toNat srcOff.toNat sz.toNat := by
    simp only [State.canExpandMemory2, State.consumeGas]; rw [hL] at h_gas; omega
  simp only [chargeMem2, dif_pos h_mem]
  have h_dyn : Gas.copyWordCost sz ≤
      ((s.consumeGas (Gas.baseCost s.fork .MCOPY) h_base).consumeMemExp2
        destOff.toNat sz.toNat srcOff.toNat sz.toNat h_mem).gasAvailable := by
    simp only [State.consumeMemExp2, State.consumeGas]
    rw [hL] at h_gas
    simp only [MachineState.memExpansionDelta2] at h_gas h_mem ⊢
    omega
  simp only [dif_pos h_dyn]
  simp only [State.consumeGas, State.consumeMemExp2, State.replaceStackAndIncrPC,
    State.activeWordsAfterUInt256_2, Gas.mcopyTotal, UInt256.succ,
    MachineState.memExpansionDelta2, MachineState.mcopy,
    show ∀ (a b : UInt256), a + b = a.add b from fun _ _ => rfl]
  grind

/-- Completeness for `StepRunning.sload`. -/
theorem complete_sload (s : State) (key : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .SLOAD)
        (h_gas     : Gas.sloadTotal s key ≤ s.gasAvailable)
        (h_stack   : s.stack = key :: rest)
        (h_cap   : s.stack.length + Operation.pushArity .SLOAD
                     ≤ 1024 + Operation.popArity .SLOAD)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := ((s.accountMap s.executionEnv.address).storage key) :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.sloadTotal s key
              substate     := s.substate.addAccessedStorageKey
                                (s.executionEnv.address, key) }
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  have h_base : Gas.baseCost s.fork .SLOAD ≤ s.gasAvailable := by
    have hL : Gas.sloadTotal s key
        = Gas.baseCost s.fork .SLOAD + Gas.sloadColdSurcharge s key := rfl
    rw [hL] at h_gas; omega
  refine stepF_eq_ok ?_
  rw [stepFE_dispatch h_run h_np h_dec h_cap h_base]
  simp only [stepF.stackMemFlow, h_stack]
  rw [dif_pos h_gas]
  rfl

/-- Completeness for `StepRunning.sstore`. -/
theorem complete_sstore (s : State) (key value : UInt256) (rest : List UInt256)
        (h_op     : s.decodedOp = some .SSTORE)
        (h_perm   : s.executionEnv.permitStateMutation = true)
        (h_stack  : s.stack = key :: value :: rest)
        (h_sentry : Gas.sstoreSentry s.fork
                      (s.gasAvailable - Gas.baseCost s.fork .SSTORE) = false)
        (h_gas    : Gas.sstoreTotal s key value ≤ s.gasAvailable)
        (h_cap   : s.stack.length + Operation.pushArity .SSTORE
                     ≤ 1024 + Operation.popArity .SSTORE)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.sstoreTotal s key value
              accountMap   := s.accountMap.set s.executionEnv.address
                                { s.accountMap s.executionEnv.address with
                                    storage := (s.accountMap s.executionEnv.address).storage.set
                                                 key value }
              substate     :=
                { s.substate.addAccessedStorageKey (s.executionEnv.address, key) with
                    refundBalance :=
                      let δ := Gas.sstoreRefund s.fork
                                 (s.substate.originalStorage s.executionEnv.address key)
                                 ((s.accountMap s.executionEnv.address).storage key) value
                      let rb : Int := (s.substate.refundBalance.toNat : Int) + δ
                      UInt256.ofNat (if rb < 0 then 0 else rb.toNat) } }
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  have hL : Gas.sstoreTotal s key value
      = Gas.baseCost s.fork .SSTORE
        + (Gas.sstoreCost s.fork
              (s.substate.originalStorage s.executionEnv.address key)
              ((s.accountMap s.executionEnv.address).storage key) value
            + Gas.sstoreColdSurcharge s key) := rfl
  have h_base : Gas.baseCost s.fork .SSTORE ≤ s.gasAvailable := by rw [hL] at h_gas; omega
  refine stepF_eq_ok ?_
  rw [stepFE_dispatch h_run h_np h_dec h_cap h_base]
  simp only [stepF.stackMemFlow]
  rw [if_neg (by simp [h_perm])]
  rw [if_neg (by simp [State.consumeGas, h_sentry])]
  simp only [h_stack]
  have h_cost :
      Gas.sstoreCost s.fork (s.substate.originalStorage s.executionEnv.address key)
          ((s.accountMap s.executionEnv.address).storage key) value
        + Gas.sstoreColdSurcharge s key
      ≤ (s.consumeGas (Gas.baseCost s.fork .SSTORE) h_base).gasAvailable := by
    simp only [State.consumeGas]; rw [hL] at h_gas; omega
  rw [dif_pos h_cost]
  simp only [State.consumeGas, State.replaceStackAndIncrPC, Gas.sstoreTotal, UInt256.succ,
    show ∀ (a b : UInt256), a + b = a.add b from fun _ _ => rfl]
  grind

/-- Completeness for `StepRunning.tload`. -/
theorem complete_tload (s : State) (key : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .TLOAD)
        (h_gas     : Gas.baseCost s.fork .TLOAD ≤ s.gasAvailable)
        (h_stack   : s.stack = key :: rest)
        (h_cap   : s.stack.length + Operation.pushArity .TLOAD
                     ≤ 1024 + Operation.popArity .TLOAD)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := ((s.accountMap s.executionEnv.address).tstorage key) :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .TLOAD }
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  refine stepF_eq_ok ?_
  rw [stepFE_dispatch h_run h_np h_dec h_cap h_gas]
  simp only [stepF.stackMemFlow, h_stack]
  rfl

/-- Completeness for `StepRunning.tstore`. -/
theorem complete_tstore (s : State) (key value : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .TSTORE)
        (h_perm    : s.executionEnv.permitStateMutation = true)
        (h_gas     : Gas.baseCost s.fork .TSTORE ≤ s.gasAvailable)
        (h_stack   : s.stack = key :: value :: rest)
        (h_cap   : s.stack.length + Operation.pushArity .TSTORE
                     ≤ 1024 + Operation.popArity .TSTORE)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .TSTORE
              accountMap   := s.accountMap.set s.executionEnv.address
                                { s.accountMap s.executionEnv.address with
                                    tstorage :=
                                      (s.accountMap s.executionEnv.address).tstorage.set
                                        key value } }
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  refine stepF_eq_ok ?_
  rw [stepFE_dispatch h_run h_np h_dec h_cap h_gas]
  simp only [stepF.stackMemFlow]
  rw [if_neg (by simp [h_perm])]
  simp only [h_stack]
  rfl

end StepComplete
end EVM
end EvmSemantics
