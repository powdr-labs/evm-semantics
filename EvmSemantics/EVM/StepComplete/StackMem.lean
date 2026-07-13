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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

end StepComplete
end EVM
end EvmSemantics
