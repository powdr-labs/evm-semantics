module

public import EvmSemantics.EVM.StepComplete.Dispatch

/-!
`StepComplete.Creates` — completeness cases for the Creates constructors of
`StepRunning`: each constructor's premises force `stepF` to compute
exactly that constructor's successor. Assembled into
`stepRunning_complete` in `StepDeterminism.lean`.
-/

@[expose] public section

namespace EvmSemantics
namespace EVM
namespace StepComplete

/-- Completeness for `StepRunning.return_`. -/
theorem complete_return_ (s : State) (offset size : UInt256) (rest : List UInt256)
        (h_op    : s.decodedOp = some .RETURN)
        (h_stack : s.stack = offset :: size :: rest)
        (h_gas   : Gas.returnTotal s offset size ≤ s.gasAvailable)
        (h_cap   : s.stack.length + Operation.pushArity .RETURN
                     ≤ 1024 + Operation.popArity .RETURN)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              halt         := .Returned
              hReturn      := MachineState.readPadded s.memory offset.toNat size.toNat
              stack        := rest
              gasAvailable := s.gasAvailable - Gas.returnTotal s offset size
              activeWords  := s.activeWordsAfterUInt256 offset.toNat size.toNat }
    := by
  sorry

/-- Completeness for `StepRunning.revert`. -/
theorem complete_revert (s : State) (offset size : UInt256) (rest : List UInt256)
        (h_op    : s.decodedOp = some .REVERT)
        (h_stack : s.stack = offset :: size :: rest)
        (h_gas   : Gas.revertTotal s offset size ≤ s.gasAvailable)
        (h_cap   : s.stack.length + Operation.pushArity .REVERT
                     ≤ 1024 + Operation.popArity .REVERT)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              halt         := .Reverted
              hReturn      := MachineState.readPadded s.memory offset.toNat size.toNat
              stack        := rest
              gasAvailable := s.gasAvailable - Gas.revertTotal s offset size
              activeWords  := s.activeWordsAfterUInt256 offset.toNat size.toNat }
    := by
  sorry

/-- Completeness for `StepRunning.createStatic`. -/
theorem complete_createStatic (s : State)
        (value offset size : UInt256) (rest : List UInt256)
        (h_op    : s.decodedOp = some .CREATE)
        (h_stack : s.stack = value :: offset :: size :: rest)
        (h_perm  : s.executionEnv.permitStateMutation = false)
        (h_gas   : Gas.baseCost s.fork .CREATE ≤ s.gasAvailable)
        (h_cap   : s.stack.length + Operation.pushArity .CREATE
                     ≤ 1024 + Operation.popArity .CREATE)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s = ({ s with halt := .Exception .StaticModeViolation })
    := by
  sorry

/-- Completeness for `StepRunning.createFail`. -/
theorem complete_createFail (s : State)
        (value offset size : UInt256) (rest : List UInt256)
        (h_op    : s.decodedOp = some .CREATE)
        (h_stack : s.stack = value :: offset :: size :: rest)
        (h_perm  : s.executionEnv.permitStateMutation = true)
        (h_gas   : Gas.createCommitted s offset size ≤ s.gasAvailable)
        (h_fail  : s.executionEnv.depth ≥ 1024 ∨
                     (s.accountMap s.executionEnv.address).balance < value ∨
                     Account.maxNonce ≤ (s.accountMap s.executionEnv.address).nonce.toNat)
        (h_size  : Gas.initCodeTooLarge s.fork size.toNat = false)
        (h_cap   : s.stack.length + Operation.pushArity .CREATE
                     ≤ 1024 + Operation.popArity .CREATE)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              gasAvailable := s.gasAvailable - Gas.createCommitted s offset size
              activeWords  := s.activeWordsAfterUInt256 offset.toNat size.toNat
              returnData   := .empty
              stack        := UInt256.ofNat 0 :: rest
              pc           := s.pc.succ }
    := by
  sorry

/-- Completeness for `StepRunning.createCollision`. -/
theorem complete_createCollision (s : State)
        (value offset size : UInt256) (rest : List UInt256)
        (forwarded : Nat)
        (h_op    : s.decodedOp = some .CREATE)
        (h_stack : s.stack = value :: offset :: size :: rest)
        (h_perm  : s.executionEnv.permitStateMutation = true)
        (h_gas   : Gas.createCommitted s offset size ≤ s.gasAvailable)
        (h_take  : ¬ (s.executionEnv.depth ≥ 1024 ∨
                        (s.accountMap s.executionEnv.address).balance < value ∨
                        Account.maxNonce ≤ (s.accountMap s.executionEnv.address).nonce.toNat))
        (h_fwd   : forwarded = Gas.allButOneSixtyFourth s.executionEnv.fork
                     (s.gasAvailable - Gas.createCommitted s offset size))
        (h_coll  : (s.accountMap (EvmSemantics.createAddress s.executionEnv.address
                     (s.accountMap s.executionEnv.address).nonce)).isContract = true)
        (h_size  : Gas.initCodeTooLarge s.fork size.toNat = false)
        (h_cap   : s.stack.length + Operation.pushArity .CREATE
                     ≤ 1024 + Operation.popArity .CREATE)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              gasAvailable := s.gasAvailable - Gas.createCommitted s offset size - forwarded
              activeWords  := s.activeWordsAfterUInt256 offset.toNat size.toNat
              accountMap   := s.accountMap.set s.executionEnv.address
                                { s.accountMap s.executionEnv.address with
                                    nonce := (s.accountMap s.executionEnv.address).nonce + ⟨1⟩ }
              returnData   := .empty
              stack        := UInt256.ofNat 0 :: rest
              pc           := s.pc.succ }
    := by
  sorry

/-- Completeness for `StepRunning.create`. -/
theorem complete_create (s : State)
        (value offset size : UInt256) (rest : List UInt256)
        (forwarded : Nat)
        (h_op     : s.decodedOp = some .CREATE)
        (h_stack  : s.stack = value :: offset :: size :: rest)
        (h_perm   : s.executionEnv.permitStateMutation = true)
        (h_gas    : Gas.createCommitted s offset size ≤ s.gasAvailable)
        (h_take   : ¬ (s.executionEnv.depth ≥ 1024 ∨
                         (s.accountMap s.executionEnv.address).balance < value ∨
                         Account.maxNonce ≤ (s.accountMap s.executionEnv.address).nonce.toNat))
        (h_fwd    : forwarded = Gas.allButOneSixtyFourth s.executionEnv.fork
                      (s.gasAvailable - Gas.createCommitted s offset size))
        (h_nocoll : (s.accountMap (EvmSemantics.createAddress s.executionEnv.address
                      (s.accountMap s.executionEnv.address).nonce)).isContract = false)
        (h_size  : Gas.initCodeTooLarge s.fork size.toNat = false)
        (h_cap   : s.stack.length + Operation.pushArity .CREATE
                     ≤ 1024 + Operation.popArity .CREATE)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          (({ s with
                gasAvailable := s.gasAvailable - Gas.createCommitted s offset size - forwarded
                activeWords  := s.activeWordsAfterUInt256 offset.toNat size.toNat }
           ).enterCreate rest (EvmSemantics.createAddress s.executionEnv.address
                                  (s.accountMap s.executionEnv.address).nonce) value
             (MachineState.readPadded s.memory offset.toNat size.toNat)
             forwarded)
    := by
  sorry

/-- Completeness for `StepRunning.create2Static`. -/
theorem complete_create2Static (s : State)
        (value offset size salt : UInt256) (rest : List UInt256)
        (h_op    : s.decodedOp = some .CREATE2)
        (h_stack : s.stack = value :: offset :: size :: salt :: rest)
        (h_perm  : s.executionEnv.permitStateMutation = false)
        (h_gas   : Gas.baseCost s.fork .CREATE2 ≤ s.gasAvailable)
        (h_cap   : s.stack.length + Operation.pushArity .CREATE2
                     ≤ 1024 + Operation.popArity .CREATE2)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s = ({ s with halt := .Exception .StaticModeViolation })
    := by
  sorry

/-- Completeness for `StepRunning.create2Fail`. -/
theorem complete_create2Fail (s : State)
        (value offset size salt : UInt256) (rest : List UInt256)
        (h_op    : s.decodedOp = some .CREATE2)
        (h_stack : s.stack = value :: offset :: size :: salt :: rest)
        (h_perm  : s.executionEnv.permitStateMutation = true)
        (h_gas   : Gas.create2Committed s offset size ≤ s.gasAvailable)
        (h_fail  : s.executionEnv.depth ≥ 1024 ∨
                     (s.accountMap s.executionEnv.address).balance < value ∨
                     Account.maxNonce ≤ (s.accountMap s.executionEnv.address).nonce.toNat)
        (h_size  : Gas.initCodeTooLarge s.fork size.toNat = false)
        (h_cap   : s.stack.length + Operation.pushArity .CREATE2
                     ≤ 1024 + Operation.popArity .CREATE2)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              gasAvailable := s.gasAvailable - Gas.create2Committed s offset size
              activeWords  := s.activeWordsAfterUInt256 offset.toNat size.toNat
              returnData   := .empty
              stack        := UInt256.ofNat 0 :: rest
              pc           := s.pc.succ }
    := by
  sorry

/-- Completeness for `StepRunning.create2Collision`. -/
theorem complete_create2Collision (s : State)
        (value offset size salt : UInt256) (rest : List UInt256) (forwarded : Nat)
        (h_op    : s.decodedOp = some .CREATE2)
        (h_stack : s.stack = value :: offset :: size :: salt :: rest)
        (h_perm  : s.executionEnv.permitStateMutation = true)
        (h_gas   : Gas.create2Committed s offset size ≤ s.gasAvailable)
        (h_take  : ¬ (s.executionEnv.depth ≥ 1024 ∨
                        (s.accountMap s.executionEnv.address).balance < value ∨
                        Account.maxNonce ≤ (s.accountMap s.executionEnv.address).nonce.toNat))
        (h_fwd   : forwarded = Gas.allButOneSixtyFourth s.executionEnv.fork
                     (s.gasAvailable - Gas.create2Committed s offset size))
        (h_coll  : (s.accountMap
                     (EvmSemantics.create2Address s.executionEnv.address salt
                       (MachineState.readPadded s.memory
                          offset.toNat size.toNat))).isContract = true)
        (h_size  : Gas.initCodeTooLarge s.fork size.toNat = false)
        (h_cap   : s.stack.length + Operation.pushArity .CREATE2
                     ≤ 1024 + Operation.popArity .CREATE2)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              gasAvailable := s.gasAvailable - Gas.create2Committed s offset size - forwarded
              activeWords  := s.activeWordsAfterUInt256 offset.toNat size.toNat
              accountMap   := s.accountMap.set s.executionEnv.address
                                { s.accountMap s.executionEnv.address with
                                    nonce := (s.accountMap s.executionEnv.address).nonce + ⟨1⟩ }
              returnData   := .empty
              stack        := UInt256.ofNat 0 :: rest
              pc           := s.pc.succ }
    := by
  sorry

/-- Completeness for `StepRunning.create2`. -/
theorem complete_create2 (s : State)
        (value offset size salt : UInt256) (rest : List UInt256) (forwarded : Nat)
        (h_op     : s.decodedOp = some .CREATE2)
        (h_stack  : s.stack = value :: offset :: size :: salt :: rest)
        (h_perm   : s.executionEnv.permitStateMutation = true)
        (h_gas    : Gas.create2Committed s offset size ≤ s.gasAvailable)
        (h_take   : ¬ (s.executionEnv.depth ≥ 1024 ∨
                         (s.accountMap s.executionEnv.address).balance < value ∨
                         Account.maxNonce ≤ (s.accountMap s.executionEnv.address).nonce.toNat))
        (h_fwd    : forwarded = Gas.allButOneSixtyFourth s.executionEnv.fork
                      (s.gasAvailable - Gas.create2Committed s offset size))
        (h_nocoll : (s.accountMap
                      (EvmSemantics.create2Address s.executionEnv.address salt
                        (MachineState.readPadded s.memory
                           offset.toNat size.toNat))).isContract = false)
        (h_size  : Gas.initCodeTooLarge s.fork size.toNat = false)
        (h_cap   : s.stack.length + Operation.pushArity .CREATE2
                     ≤ 1024 + Operation.popArity .CREATE2)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          (({ s with
                gasAvailable := s.gasAvailable - Gas.create2Committed s offset size - forwarded
                activeWords  := s.activeWordsAfterUInt256 offset.toNat size.toNat }
           ).enterCreate rest
             (EvmSemantics.create2Address s.executionEnv.address salt
               (MachineState.readPadded s.memory offset.toNat size.toNat))
             value
             (MachineState.readPadded s.memory offset.toNat size.toNat)
             forwarded)
    := by
  sorry

/-- Completeness for `StepRunning.selfDestructStatic`. -/
theorem complete_selfDestructStatic (s : State)
        (beneficiary : UInt256) (rest : List UInt256)
        (h_op    : s.decodedOp = some .SELFDESTRUCT)
        (h_stack : s.stack = beneficiary :: rest)
        (h_perm  : s.executionEnv.permitStateMutation = false)
        (h_gas   : Gas.baseCost s.fork .SELFDESTRUCT ≤ s.gasAvailable)
        (h_cap   : s.stack.length + Operation.pushArity .SELFDESTRUCT
                     ≤ 1024 + Operation.popArity .SELFDESTRUCT)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s = ({ s with halt := .Exception .StaticModeViolation })
    := by
  sorry

/-- Completeness for `StepRunning.selfDestruct`. -/
theorem complete_selfDestruct (s : State)
        (beneficiary : UInt256) (rest : List UInt256)
        (h_op    : s.decodedOp = some .SELFDESTRUCT)
        (h_stack : s.stack = beneficiary :: rest)
        (h_perm  : s.executionEnv.permitStateMutation = true)
        (h_gas   : Gas.selfDestructTotal s beneficiary ≤ s.gasAvailable)
        (h_cap   : s.stack.length + Operation.pushArity .SELFDESTRUCT
                     ≤ 1024 + Operation.popArity .SELFDESTRUCT)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          (({ s with gasAvailable := s.gasAvailable - Gas.selfDestructTotal s beneficiary
            }).selfDestructTo (AccountAddress.ofUInt256 beneficiary))
    := by
  sorry

end StepComplete
end EVM
end EvmSemantics
