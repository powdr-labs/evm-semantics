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
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  have h_gas' : Gas.baseCost s.fork (.System .RETURN)
      + MachineState.memExpansionDelta s.activeWords.toNat offset.toNat size.toNat
      ≤ s.gasAvailable := h_gas
  have h_base : Gas.baseCost s.fork (.System .RETURN) ≤ s.gasAvailable :=
    le_trans (Nat.le_add_right _ _) h_gas'
  have h_mem : (s.consumeGas (Gas.baseCost s.fork (.System .RETURN))
      h_base).canExpandMemory offset.toNat size.toNat := by
    show MachineState.memExpansionDelta s.activeWords.toNat offset.toNat size.toNat
      ≤ s.gasAvailable - Gas.baseCost s.fork (.System .RETURN)
    omega
  refine stepF_eq_ok ?_
  rw [stepFE_dispatch h_run h_np h_dec h_cap h_base]
  simp only [stepF.system, h_stack]
  unfold chargeMem
  rw [dif_pos h_mem]
  simp only [Except.ok.injEq]
  simp [State.consumeGas, State.consumeMemExp, State.activeWordsAfterUInt256,
        Gas.returnTotal, MachineState.memExpansionDelta, State.fork]
  grind

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
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  have h_gas' : Gas.baseCost s.fork (.System .REVERT)
      + MachineState.memExpansionDelta s.activeWords.toNat offset.toNat size.toNat
      ≤ s.gasAvailable := h_gas
  have h_base : Gas.baseCost s.fork (.System .REVERT) ≤ s.gasAvailable :=
    le_trans (Nat.le_add_right _ _) h_gas'
  have h_mem : (s.consumeGas (Gas.baseCost s.fork (.System .REVERT))
      h_base).canExpandMemory offset.toNat size.toNat := by
    show MachineState.memExpansionDelta s.activeWords.toNat offset.toNat size.toNat
      ≤ s.gasAvailable - Gas.baseCost s.fork (.System .REVERT)
    omega
  refine stepF_eq_ok ?_
  rw [stepFE_dispatch h_run h_np h_dec h_cap h_base]
  simp only [stepF.system, h_stack]
  unfold chargeMem
  rw [dif_pos h_mem]
  simp only [Except.ok.injEq]
  simp [State.consumeGas, State.consumeMemExp, State.activeWordsAfterUInt256,
        Gas.revertTotal, MachineState.memExpansionDelta, State.fork]
  grind

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
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  refine stepF_eq_error ?_
  rw [stepFE_dispatch h_run h_np h_dec h_cap h_gas]
  simp only [stepF.system, h_stack]
  rw [if_pos (by simp [h_perm])]
  rfl

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
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  have hC : Gas.createCommitted s offset size
      = Gas.baseCost s.fork .CREATE
        + MachineState.memExpansionDelta s.activeWords.toNat offset.toNat size.toNat
        + Gas.initCodeWordCost s.fork size.toNat := rfl
  have h_base : Gas.baseCost s.fork .CREATE ≤ s.gasAvailable := by rw [hC] at h_gas; omega
  refine stepF_eq_ok ?_
  rw [stepFE_dispatch h_run h_np h_dec h_cap h_base]
  simp only [stepF.system, h_stack]
  rw [if_neg (by simp [h_perm]), if_neg (by simp [h_size])]
  have h_mem : (s.consumeGas (Gas.baseCost s.fork .CREATE) h_base).canExpandMemory
      offset.toNat size.toNat := by
    simp only [State.canExpandMemory, State.consumeGas]; rw [hC] at h_gas; omega
  simp only [chargeMem, dif_pos h_mem]
  rw [dif_pos (by
        simp only [State.consumeMemExp, State.consumeGas]
        rw [hC] at h_gas
        simp only [MachineState.memExpansionDelta, Operation.CREATE] at h_gas ⊢
        omega)]
  rw [if_pos (by
        simpa only [State.consumeGas, State.consumeMemExp] using h_fail)]
  simp [State.consumeGas, State.consumeMemExp, State.replaceStackAndIncrPC,
    State.activeWordsAfterUInt256, Gas.createCommitted, MachineState.memExpansionDelta,
    State.fork, UInt256.succ, show ∀ (a b : UInt256), a + b = a.add b from fun _ _ => rfl]
  grind

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
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  have h_base : Gas.baseCost s.fork .CREATE ≤ s.gasAvailable := by
    exact le_trans ( Nat.le_add_right _ _ ) ( le_trans ( Nat.le_add_right _ _ ) h_gas )
  rw [stepF_eq_ok]
  rw [stepFE_dispatch h_run h_np h_dec h_cap h_base]
  simp +decide [ stepF.system, h_stack, h_perm, h_size ]
  rw [ chargeMem ]
  split_ifs <;> simp_all +decide [ State.canExpandMemory, State.consumeGas, State.consumeMemExp ]
  · rw [ if_pos, if_neg ]
    · rw [ if_pos ]
      · simp +decide [Gas.createCommitted, MachineState.memExpansionDelta,
          State.activeWordsAfterUInt256, State.replaceStackAndIncrPC, State.fork, UInt256.succ]
        grind
      · unfold Gas.allButOneSixtyFourth
        split_ifs <;> omega
    · grind
    · unfold Gas.createCommitted at h_gas; simp_all +decide [ Gas.baseCost ]
      unfold MachineState.memExpansionDelta at h_gas; simp_all +decide [ Nat.sub_sub ]
      simp only [State.fork]; omega
  · unfold Gas.createCommitted at h_gas
    grind

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
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op;
  have h_base : Gas.baseCost s.fork .CREATE ≤ s.gasAvailable := by
    exact le_trans ( Nat.le_add_right _ _ ) ( le_trans ( Nat.le_add_right _ _ ) h_gas );
  rw [stepF_eq_ok];
  rw [stepFE_dispatch h_run h_np h_dec h_cap h_base];
  simp +decide [ stepF.system, h_stack, h_perm, h_size ];
  rw [ chargeMem ];
  split_ifs <;> simp_all +decide [ State.canExpandMemory, State.consumeGas, State.consumeMemExp ];
  · rw [ if_pos, if_neg ];
    · rw [ if_pos ];
      · simp +decide [ Gas.createCommitted, MachineState.memExpansionDelta,
            createAddress, State.activeWordsAfterUInt256 ];
        grind;
      · unfold Gas.allButOneSixtyFourth;
        split_ifs <;> omega;
    · grind;
    · unfold Gas.createCommitted at h_gas; simp_all +decide [ Gas.baseCost ] ;
      unfold MachineState.memExpansionDelta at h_gas; simp_all +decide [ Nat.sub_sub ] ;
      simp only [State.fork]; omega;
  · unfold Gas.createCommitted at h_gas;
    grind

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