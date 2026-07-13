module

public import EvmSemantics.EVM.StepComplete.Dispatch

/-!
`StepComplete.Calls` — completeness cases for the Calls constructors of
`StepRunning`: each constructor's premises force `stepF` to compute
exactly that constructor's successor. Assembled into
`stepRunning_complete` in `StepDeterminism.lean`.
-/

@[expose] public section

namespace EvmSemantics
namespace EVM
namespace StepComplete

/-- Completeness for `StepRunning.callStatic`. -/
theorem complete_callStatic (s : State)
        (gasArg toArg value argsOff argsLen retOff retLen : UInt256)
        (rest : List UInt256)
        (h_op       : s.decodedOp = some .CALL)
        (h_stack    : s.stack =
                        gasArg :: toArg :: value :: argsOff :: argsLen :: retOff :: retLen :: rest)
        (h_perm     : s.executionEnv.permitStateMutation = false)
        (h_value    : value.toNat ≠ 0)
        (h_gas   : Gas.baseCost s.fork .CALL ≤ s.gasAvailable)
        (h_cap   : s.stack.length + Operation.pushArity .CALL
                     ≤ 1024 + Operation.popArity .CALL)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s = ({ s with halt := .Exception .StaticModeViolation })
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  refine stepF_eq_error ?_
  rw [stepFE_dispatch h_run h_np h_dec h_cap h_gas]
  simp only [stepF.system, h_stack]
  rw [if_pos ⟨by simp [h_perm], h_value⟩]
  rfl

/-- Completeness for `StepRunning.call`. -/
theorem complete_call (s : State)
        (gasArg toArg value argsOff argsLen retOff retLen : UInt256)
        (rest : List UInt256) (forwarded : Nat)
        (h_op       : s.decodedOp = some .CALL)
        (h_stack    : s.stack =
                        gasArg :: toArg :: value :: argsOff :: argsLen :: retOff :: retLen :: rest)
        -- Complement of `callStatic`: a value-transferring CALL in a static
        -- frame is rejected *before* any gas is charged, so neither the
        -- taken nor the silent-fail path may fire in that case.
        (h_static   : s.executionEnv.permitStateMutation = true ∨ value.toNat = 0)
        (h_gas      : Gas.callCommitted s value argsOff argsLen retOff retLen toArg
                        ≤ s.gasAvailable)
        (h_take     : ¬ (s.executionEnv.depth ≥ 1024 ∨
                         (s.accountMap s.executionEnv.address).balance < value))
        (h_fwd      : forwarded = Gas.forwardGas s.executionEnv.fork
                        (s.gasAvailable
                          - Gas.callCommitted s value argsOff argsLen retOff retLen toArg)
                        gasArg.toNat)
        -- Pre-EIP-150 `forwardGas` returns `gasArg` verbatim, so a too-
        -- large `gasArg` must OOG rather than enter the callee. This
        -- premise rules out that case; post-EIP-150 it is implied by
        -- the `g - g/64` cap.
        (h_afford   : forwarded ≤ s.gasAvailable
                        - Gas.callCommitted s value argsOff argsLen retOff retLen toArg)
        (h_cap   : s.stack.length + Operation.pushArity .CALL
                     ≤ 1024 + Operation.popArity .CALL)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          (({ s with
                gasAvailable := s.gasAvailable
                                - Gas.callCommitted s value argsOff argsLen retOff retLen toArg
                                - forwarded
                activeWords  := s.activeWordsAfterUInt256_2
                                  argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat }
           ).enterCall rest (AccountAddress.ofUInt256 toArg)
             (AccountAddress.ofUInt256 toArg) value
             (MachineState.readPadded s.memory argsOff.toNat argsLen.toNat)
             (State.callTargetCode s (AccountAddress.ofUInt256 toArg))
             (forwarded + (bif (value.toNat != 0) then Gas.callStipend else 0))
             retOff.toNat retLen.toNat)
    := by
  apply Eq.symm; exact (by
    have h_base : Gas.baseCost s.fork .CALL ≤ s.gasAvailable := by
      have h := h_gas; unfold Gas.callCommitted at h; simp only [State.fork] at h ⊢; omega
    obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
    rw [stepF_eq_ok]
    rw [stepFE_dispatch h_run h_np h_dec h_cap h_base]
    simp +decide [h_stack] ;
    rw [ stepF.system ] ; simp +decide [ h_stack ] ;
    rw [ chargeMem2 ];
    split_ifs <;> simp_all +decide [ State.canExpandMemory2, State.consumeGas ];
    · rw [ if_pos ];
      · rw [ if_pos ];
        · rw [ if_neg ];
          · simp +decide [ State.consumeGas, State.consumeMemExp2,
              State.activeWordsAfterUInt256_2, Gas.callCommitted,
              MachineState.memExpansionDelta2, State.callTargetCode, State.delegateOf ];
            congr! 1; all_goals grind;
          · simp +decide [ State.consumeMemExp2, State.consumeGas ] at * ; omega;
        · simp +decide [ State.consumeMemExp2, State.consumeGas ] at *;
          unfold Gas.callCommitted at *; simp_all +decide [ Nat.sub_sub ] ;
          simp only [State.fork, MachineState.memExpansionDelta2] at h_afford ⊢
          exact h_afford;
      · simp +decide [ State.consumeMemExp2, State.consumeGas ] at *;
        simp +decide [ Gas.callCommitted ] at *;
        simp +decide [ MachineState.memExpansionDelta2 ] at *;
        grind;
    · rw [ if_pos ];
      · rw [ if_pos ];
        · rw [ if_neg ];
          · simp +decide [ State.consumeGas, State.consumeMemExp2,
              State.activeWordsAfterUInt256_2, Gas.callCommitted,
              MachineState.memExpansionDelta2, State.callTargetCode, State.delegateOf ];
            congr! 1;
            · grind;
            · grind;
          · simp +decide [ State.consumeMemExp2, State.consumeGas ] at * ; omega;
        · convert h_afford using 1;
          · unfold Gas.callCommitted; simp +decide [ State.consumeGas, State.consumeMemExp2 ] ;
            unfold MachineState.memExpansionDelta2; simp +decide [ Nat.sub_sub ] ;
          · simp +decide [ State.consumeMemExp2, Gas.callCommitted ];
            simp +decide [ State.consumeGas, MachineState.memExpansionDelta2 ];
            grind +splitImp;
      · simp +decide [ State.consumeMemExp2, State.consumeGas ] at *;
        simp +decide [ Gas.callCommitted ] at *;
        simp +decide [ MachineState.memExpansionDelta2 ] at *;
        grind;
    · unfold Gas.callCommitted at *;
      grind +splitImp
  )

/-- Completeness for `StepRunning.callFail`. -/
theorem complete_callFail (s : State)
        (gasArg toArg value argsOff argsLen retOff retLen : UInt256)
        (rest : List UInt256)
        (h_op    : s.decodedOp = some .CALL)
        (h_stack : s.stack =
                     gasArg :: toArg :: value :: argsOff :: argsLen :: retOff :: retLen :: rest)
        -- Same static-mode exclusion as `call`: the `callStatic` rejection
        -- fires before the depth/balance check, so the silent-fail exit is
        -- unreachable for a value-transferring CALL in a static frame.
        (h_static : s.executionEnv.permitStateMutation = true ∨ value.toNat = 0)
        (h_gas   : Gas.callCommitted s value argsOff argsLen retOff retLen toArg
                     ≤ s.gasAvailable)
        -- Same `h_afford` as `call`: pre-EIP-150 `forwardGas gasArg =
        -- gasArg`, so `gasArg > gasAvailable - commit` must OOG rather
        -- than take the silent-fail exit; post-EIP-150 the `g - g/64`
        -- cap makes this premise trivial. Ruling this case out here
        -- keeps `Step.callFail` from admitting transitions the YP would
        -- reject.
        (h_afford : Gas.forwardGas s.executionEnv.fork
                      (s.gasAvailable
                        - Gas.callCommitted s value argsOff argsLen retOff retLen toArg)
                      gasArg.toNat
                    ≤ s.gasAvailable
                      - Gas.callCommitted s value argsOff argsLen retOff retLen toArg)
        (h_fail  : s.executionEnv.depth ≥ 1024 ∨
                     (s.accountMap s.executionEnv.address).balance < value)
        (h_cap   : s.stack.length + Operation.pushArity .CALL
                     ≤ 1024 + Operation.popArity .CALL)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          ({ s with
              gasAvailable := s.gasAvailable
                              - Gas.callCommitted s value argsOff argsLen retOff retLen toArg
                              + (bif (value.toNat != 0) then Gas.callStipend else 0)
              activeWords  := s.activeWordsAfterUInt256_2
                                argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat
              returnData   := .empty
              -- EIP-2929: target warmed during gas-charging, before the
              -- depth/balance check (matches the taken `call` via enterCall).
              substate     := State.warmCallTarget s s.substate (AccountAddress.ofUInt256 toArg)
              stack        := UInt256.ofNat 0 :: rest
              pc           := s.pc.succ })
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  have hC : Gas.callCommitted s value argsOff argsLen retOff retLen toArg
      = Gas.baseCost s.fork .CALL
        + MachineState.memExpansionDelta2 s.activeWords.toNat
            argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat
        + (Gas.callSurcharge s.fork (value.toNat != 0)
              (Gas.callTargetIsNew s.fork s.accountMap (AccountAddress.ofUInt256 toArg))
            + Gas.accountColdSurcharge s (AccountAddress.ofUInt256 toArg)
            + Gas.delegationAccessCost s (AccountAddress.ofUInt256 toArg)) := rfl
  have h_base : Gas.baseCost s.fork .CALL ≤ s.gasAvailable := by rw [hC] at h_gas; omega
  refine stepF_eq_ok ?_
  rw [stepFE_dispatch h_run h_np h_dec h_cap h_base]
  simp only [stepF.system, h_stack]
  rw [if_neg (by rintro ⟨hp, hv⟩; rcases h_static with h | h; exacts [hp h, hv h])]
  have h_mem : (s.consumeGas (Gas.baseCost s.fork .CALL) h_base).canExpandMemory2
      argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat := by
    simp only [State.canExpandMemory2, State.consumeGas]; rw [hC] at h_gas; omega
  simp only [chargeMem2, dif_pos h_mem]
  rw [dif_pos (by
        simp only [State.consumeMemExp2, State.consumeGas]
        rw [hC] at h_gas
        simp only [MachineState.memExpansionDelta2, Operation.CALL] at h_gas ⊢
        omega)]
  rw [dif_pos (by
        simp only [State.consumeMemExp2, State.consumeGas, Operation.CALL] at *
        unfold Gas.callCommitted at *
        simp_all only [Nat.sub_sub]
        simp only [State.fork, MachineState.memExpansionDelta2, Operation.CALL] at h_afford ⊢
        exact h_afford)]
  rw [if_pos (by
        simpa only [State.consumeGas, State.consumeMemExp2] using h_fail)]
  by_cases h_vnz : value.toNat != 0 <;>
    simp [h_vnz, State.consumeGas, State.consumeMemExp2, State.replaceStackAndIncrPC,
      State.activeWordsAfterUInt256_2, Gas.callCommitted, MachineState.memExpansionDelta2,
      State.warmCallTarget, Substate.addAccessedAccount, Substate.addAccessedAccountOpt,
      State.fork, UInt256.succ,
      show ∀ (a b : UInt256), a + b = a.add b from fun _ _ => rfl] <;>
    grind

/-- Completeness for `StepRunning.callcode`. -/
theorem complete_callcode (s : State)
        (gasArg toArg value argsOff argsLen retOff retLen : UInt256)
        (rest : List UInt256) (forwarded : Nat)
        (h_op    : s.decodedOp = some .CALLCODE)
        (h_stack : s.stack =
                     gasArg :: toArg :: value :: argsOff :: argsLen :: retOff :: retLen :: rest)
        (h_gas   : Gas.callcodeCommitted s value argsOff argsLen retOff retLen toArg
                     ≤ s.gasAvailable)
        (h_take  : ¬ (s.executionEnv.depth ≥ 1024 ∨
                      (s.accountMap s.executionEnv.address).balance < value))
        (h_fwd   : forwarded = Gas.forwardGas s.executionEnv.fork
                     (s.gasAvailable
                       - Gas.callcodeCommitted s value argsOff argsLen retOff retLen toArg)
                     gasArg.toNat)
        (h_afford : forwarded ≤ s.gasAvailable
                      - Gas.callcodeCommitted s value argsOff argsLen retOff retLen toArg)
        (h_cap   : s.stack.length + Operation.pushArity .CALLCODE
                     ≤ 1024 + Operation.popArity .CALLCODE)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          (({ s with
                gasAvailable := s.gasAvailable
                                - Gas.callcodeCommitted s value argsOff argsLen retOff retLen toArg
                                - forwarded
                activeWords  := s.activeWordsAfterUInt256_2
                                  argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat }
           ).enterCall rest s.executionEnv.address
             (AccountAddress.ofUInt256 toArg) value
             (MachineState.readPadded s.memory argsOff.toNat argsLen.toNat)
             (State.callTargetCode s (AccountAddress.ofUInt256 toArg))
             (forwarded + (bif (value.toNat != 0) then Gas.callStipend else 0))
             retOff.toNat retLen.toNat)
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  have hC : Gas.callcodeCommitted s value argsOff argsLen retOff retLen toArg
      = Gas.baseCost s.fork .CALLCODE
        + MachineState.memExpansionDelta2 s.activeWords.toNat
            argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat
        + (Gas.callSurcharge s.fork (value.toNat != 0) false
            + Gas.accountColdSurcharge s (AccountAddress.ofUInt256 toArg)
            + Gas.delegationAccessCost s (AccountAddress.ofUInt256 toArg)) := rfl
  have h_base : Gas.baseCost s.fork .CALLCODE ≤ s.gasAvailable := by
    rw [hC] at h_gas; omega
  refine stepF_eq_ok ?_
  rw [stepFE_dispatch h_run h_np h_dec h_cap h_base]
  simp only [stepF.system, h_stack]
  have h_mem : (s.consumeGas (Gas.baseCost s.fork .CALLCODE) h_base).canExpandMemory2
      argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat := by
    simp only [State.canExpandMemory2, State.consumeGas]; rw [hC] at h_gas; omega
  simp only [chargeMem2, dif_pos h_mem]
  rw [dif_pos (by
        simp only [State.consumeMemExp2, State.consumeGas]
        rw [hC] at h_gas
        simp only [MachineState.memExpansionDelta2, Operation.CALLCODE] at h_gas ⊢
        omega)]
  rw [dif_pos (by
        simp only [State.consumeMemExp2, State.consumeGas, Operation.CALLCODE] at *
        unfold Gas.callcodeCommitted at *
        simp_all only [Nat.sub_sub]
        simp only [State.fork, MachineState.memExpansionDelta2, Operation.CALLCODE]
          at h_afford ⊢
        exact h_afford)]
  rw [if_neg (by
        simpa only [State.consumeGas, State.consumeMemExp2] using h_take)]
  simp only [State.consumeGas, State.consumeMemExp2,
    State.enterCall, State.activeWordsAfterUInt256_2, State.callTargetCode,
    State.delegateOf, MachineState.memExpansionDelta2, hC, State.fork, h_fwd]
  grind

/-- Completeness for `StepRunning.callcodeFail`. -/
theorem complete_callcodeFail (s : State)
        (gasArg toArg value argsOff argsLen retOff retLen : UInt256)
        (rest : List UInt256)
        (h_op    : s.decodedOp = some .CALLCODE)
        (h_stack : s.stack =
                     gasArg :: toArg :: value :: argsOff :: argsLen :: retOff :: retLen :: rest)
        (h_gas   : Gas.callcodeCommitted s value argsOff argsLen retOff retLen toArg
                     ≤ s.gasAvailable)
        -- Mirrors `callFail`'s `h_afford` premise: pre-EIP-150, silent
        -- fail is only legal when `gasArg` also fits — otherwise the
        -- transition is OOG rather than a `0`-push.
        (h_afford : Gas.forwardGas s.executionEnv.fork
                      (s.gasAvailable
                        - Gas.callcodeCommitted s value argsOff argsLen retOff retLen toArg)
                      gasArg.toNat
                    ≤ s.gasAvailable
                      - Gas.callcodeCommitted s value argsOff argsLen retOff retLen toArg)
        (h_fail  : s.executionEnv.depth ≥ 1024 ∨
                     (s.accountMap s.executionEnv.address).balance < value)
        (h_cap   : s.stack.length + Operation.pushArity .CALLCODE
                     ≤ 1024 + Operation.popArity .CALLCODE)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          ({ s with
              gasAvailable := s.gasAvailable
                              - Gas.callcodeCommitted s value argsOff argsLen retOff retLen toArg
                              + (bif (value.toNat != 0) then Gas.callStipend else 0)
              activeWords  := s.activeWordsAfterUInt256_2
                                argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat
              returnData   := .empty
              -- EIP-2929: warm the code source even on the silent-fail path.
              substate     := State.warmCallTarget s s.substate (AccountAddress.ofUInt256 toArg)
              stack        := UInt256.ofNat 0 :: rest
              pc           := s.pc.succ })
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  have hC : Gas.callcodeCommitted s value argsOff argsLen retOff retLen toArg
      = Gas.baseCost s.fork .CALLCODE
        + MachineState.memExpansionDelta2 s.activeWords.toNat
            argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat
        + (Gas.callSurcharge s.fork (value.toNat != 0) false
            + Gas.accountColdSurcharge s (AccountAddress.ofUInt256 toArg)
            + Gas.delegationAccessCost s (AccountAddress.ofUInt256 toArg)) := rfl
  have h_base : Gas.baseCost s.fork .CALLCODE ≤ s.gasAvailable := by rw [hC] at h_gas; omega
  refine stepF_eq_ok ?_
  rw [stepFE_dispatch h_run h_np h_dec h_cap h_base]
  simp only [stepF.system, h_stack]
  have h_mem : (s.consumeGas (Gas.baseCost s.fork .CALLCODE) h_base).canExpandMemory2
      argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat := by
    simp only [State.canExpandMemory2, State.consumeGas]; rw [hC] at h_gas; omega
  simp only [chargeMem2, dif_pos h_mem]
  rw [dif_pos (by
        simp only [State.consumeMemExp2, State.consumeGas]
        rw [hC] at h_gas
        simp only [MachineState.memExpansionDelta2, Operation.CALLCODE] at h_gas ⊢
        omega)]
  rw [dif_pos (by
        simp only [State.consumeMemExp2, State.consumeGas, Operation.CALLCODE] at *
        unfold Gas.callcodeCommitted at *
        simp_all only [Nat.sub_sub]
        simp only [State.fork, MachineState.memExpansionDelta2, Operation.CALLCODE]
          at h_afford ⊢
        exact h_afford)]
  rw [if_pos (by
        simpa only [State.consumeGas, State.consumeMemExp2] using h_fail)]
  by_cases h_vnz : value.toNat != 0 <;>
    simp [h_vnz, State.consumeGas, State.consumeMemExp2, State.replaceStackAndIncrPC,
      State.activeWordsAfterUInt256_2, Gas.callcodeCommitted, MachineState.memExpansionDelta2,
      State.warmCallTarget, Substate.addAccessedAccount, Substate.addAccessedAccountOpt,
      State.fork, UInt256.succ,
      show ∀ (a b : UInt256), a + b = a.add b from fun _ _ => rfl] <;>
    grind

/-- Completeness for `StepRunning.delegatecall`. -/
theorem complete_delegatecall (s : State)
        (gasArg toArg argsOff argsLen retOff retLen : UInt256)
        (rest : List UInt256) (forwarded : Nat)
        (h_op    : s.decodedOp = some .DELEGATECALL)
        (h_stack : s.stack =
                     gasArg :: toArg :: argsOff :: argsLen :: retOff :: retLen :: rest)
        (h_gas   : Gas.delegatecallCommitted s argsOff argsLen retOff retLen toArg
                     ≤ s.gasAvailable)
        (h_take  : ¬ s.executionEnv.depth ≥ 1024)
        (h_fwd   : forwarded = Gas.forwardGas s.executionEnv.fork
                     (s.gasAvailable
                       - Gas.delegatecallCommitted s argsOff argsLen retOff retLen toArg)
                     gasArg.toNat)
        (h_afford : forwarded ≤ s.gasAvailable
                      - Gas.delegatecallCommitted s argsOff argsLen retOff retLen toArg)
        (h_cap   : s.stack.length + Operation.pushArity .DELEGATECALL
                     ≤ 1024 + Operation.popArity .DELEGATECALL)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          (({ s with
                gasAvailable := s.gasAvailable
                                - Gas.delegatecallCommitted s argsOff argsLen retOff retLen toArg
                                - forwarded
                activeWords  := s.activeWordsAfterUInt256_2
                                  argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat }
           ).enterCallFor .DelegateCall rest (AccountAddress.ofUInt256 toArg)
             ⟨0⟩  -- value is irrelevant: weiValue is inherited
             (MachineState.readPadded s.memory argsOff.toNat argsLen.toNat)
             (State.callTargetCode s (AccountAddress.ofUInt256 toArg))
             forwarded retOff.toNat retLen.toNat)
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  have hC : Gas.delegatecallCommitted s argsOff argsLen retOff retLen toArg
      = Gas.baseCost s.fork .DELEGATECALL
        + MachineState.memExpansionDelta2 s.activeWords.toNat
            argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat
        + (Gas.accountColdSurcharge s (AccountAddress.ofUInt256 toArg)
            + Gas.delegationAccessCost s (AccountAddress.ofUInt256 toArg)) := rfl
  have h_base : Gas.baseCost s.fork .DELEGATECALL ≤ s.gasAvailable := by
    rw [hC] at h_gas; omega
  refine stepF_eq_ok ?_
  rw [stepFE_dispatch h_run h_np h_dec h_cap h_base]
  simp only [stepF.system, h_stack]
  have h_mem : (s.consumeGas (Gas.baseCost s.fork .DELEGATECALL) h_base).canExpandMemory2
      argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat := by
    simp only [State.canExpandMemory2, State.consumeGas]; rw [hC] at h_gas; omega
  simp only [chargeMem2, dif_pos h_mem]
  rw [dif_pos (by
        simp only [State.consumeMemExp2, State.consumeGas]
        rw [hC] at h_gas
        simp only [MachineState.memExpansionDelta2, Operation.DELEGATECALL] at h_gas ⊢
        omega)]
  rw [dif_pos (by
        simp only [State.consumeMemExp2, State.consumeGas, Operation.DELEGATECALL] at *
        unfold Gas.delegatecallCommitted at *
        simp_all only [Nat.sub_sub]
        simp only [State.fork, MachineState.memExpansionDelta2, Operation.DELEGATECALL]
          at h_afford ⊢
        exact h_afford)]
  rw [if_neg (by
        simpa only [State.consumeGas, State.consumeMemExp2] using h_take)]
  simp only [State.consumeGas, State.consumeMemExp2,
    State.enterCallFor, State.activeWordsAfterUInt256_2, State.callTargetCode,
    State.delegateOf, MachineState.memExpansionDelta2, hC, State.fork, h_fwd]
  grind

/-- Completeness for `StepRunning.delegatecallFail`. -/
theorem complete_delegatecallFail (s : State)
        (gasArg toArg argsOff argsLen retOff retLen : UInt256)
        (rest : List UInt256)
        (h_op    : s.decodedOp = some .DELEGATECALL)
        (h_stack : s.stack =
                     gasArg :: toArg :: argsOff :: argsLen :: retOff :: retLen :: rest)
        (h_gas   : Gas.delegatecallCommitted s argsOff argsLen retOff retLen toArg
                     ≤ s.gasAvailable)
        -- Mirrors `callFail`'s `h_afford`: DELEGATECALL first appeared in
        -- Homestead (pre-EIP-150), so `gasArg > gasAvailable - commit`
        -- must OOG rather than silent-fail on depth. Post-EIP-150 the
        -- `g - g/64` cap makes this trivial.
        (h_afford : Gas.forwardGas s.executionEnv.fork
                      (s.gasAvailable
                        - Gas.delegatecallCommitted s argsOff argsLen retOff retLen toArg)
                      gasArg.toNat
                    ≤ s.gasAvailable
                      - Gas.delegatecallCommitted s argsOff argsLen retOff retLen toArg)
        (h_fail  : s.executionEnv.depth ≥ 1024)
        (h_cap   : s.stack.length + Operation.pushArity .DELEGATECALL
                     ≤ 1024 + Operation.popArity .DELEGATECALL)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          ({ s with
              gasAvailable := s.gasAvailable
                              - Gas.delegatecallCommitted s argsOff argsLen retOff retLen toArg
              activeWords  := s.activeWordsAfterUInt256_2
                                argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat
              returnData   := .empty
              -- EIP-2929: target warmed even on the depth silent-fail path.
              substate     := State.warmCallTarget s s.substate (AccountAddress.ofUInt256 toArg)
              stack        := UInt256.ofNat 0 :: rest
              pc           := s.pc.succ })
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  have hC : Gas.delegatecallCommitted s argsOff argsLen retOff retLen toArg
      = Gas.baseCost s.fork .DELEGATECALL
        + MachineState.memExpansionDelta2 s.activeWords.toNat
            argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat
        + (Gas.accountColdSurcharge s (AccountAddress.ofUInt256 toArg)
            + Gas.delegationAccessCost s (AccountAddress.ofUInt256 toArg)) := rfl
  have h_base : Gas.baseCost s.fork .DELEGATECALL ≤ s.gasAvailable := by rw [hC] at h_gas; omega
  refine stepF_eq_ok ?_
  rw [stepFE_dispatch h_run h_np h_dec h_cap h_base]
  simp only [stepF.system, h_stack]
  have h_mem : (s.consumeGas (Gas.baseCost s.fork .DELEGATECALL) h_base).canExpandMemory2
      argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat := by
    simp only [State.canExpandMemory2, State.consumeGas]; rw [hC] at h_gas; omega
  simp only [chargeMem2, dif_pos h_mem]
  rw [dif_pos (by
        simp only [State.consumeMemExp2, State.consumeGas]
        rw [hC] at h_gas
        simp only [MachineState.memExpansionDelta2, Operation.DELEGATECALL] at h_gas ⊢
        omega)]
  rw [dif_pos (by
        simp only [State.consumeMemExp2, State.consumeGas, Operation.DELEGATECALL] at *
        unfold Gas.delegatecallCommitted at *
        simp_all only [Nat.sub_sub]
        simp only [State.fork, MachineState.memExpansionDelta2, Operation.DELEGATECALL]
          at h_afford ⊢
        exact h_afford)]
  rw [if_pos (by
        simpa only [State.consumeGas, State.consumeMemExp2] using h_fail)]
  simp [State.consumeGas, State.consumeMemExp2, State.replaceStackAndIncrPC,
    State.activeWordsAfterUInt256_2, Gas.delegatecallCommitted, MachineState.memExpansionDelta2,
    State.warmCallTarget, Substate.addAccessedAccount, Substate.addAccessedAccountOpt,
    State.fork, UInt256.succ,
    show ∀ (a b : UInt256), a + b = a.add b from fun _ _ => rfl]
  grind

/-- Completeness for `StepRunning.staticcall`. -/
theorem complete_staticcall (s : State)
        (gasArg toArg argsOff argsLen retOff retLen : UInt256)
        (rest : List UInt256) (forwarded : Nat)
        (h_op    : s.decodedOp = some .STATICCALL)
        (h_stack : s.stack =
                     gasArg :: toArg :: argsOff :: argsLen :: retOff :: retLen :: rest)
        (h_gas   : Gas.staticcallCommitted s argsOff argsLen retOff retLen toArg
                     ≤ s.gasAvailable)
        (h_take  : ¬ s.executionEnv.depth ≥ 1024)
        (h_fwd   : forwarded = Gas.forwardGas s.executionEnv.fork
                     (s.gasAvailable
                       - Gas.staticcallCommitted s argsOff argsLen retOff retLen toArg)
                     gasArg.toNat)
        (h_afford : forwarded ≤ s.gasAvailable
                      - Gas.staticcallCommitted s argsOff argsLen retOff retLen toArg)
        (h_cap   : s.stack.length + Operation.pushArity .STATICCALL
                     ≤ 1024 + Operation.popArity .STATICCALL)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          (({ s with
                gasAvailable := s.gasAvailable
                                - Gas.staticcallCommitted s argsOff argsLen retOff retLen toArg
                                - forwarded
                activeWords  := s.activeWordsAfterUInt256_2
                                  argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat }
           ).enterCallFor .StaticCall rest (AccountAddress.ofUInt256 toArg)
             ⟨0⟩
             (MachineState.readPadded s.memory argsOff.toNat argsLen.toNat)
             (State.callTargetCode s (AccountAddress.ofUInt256 toArg))
             forwarded retOff.toNat retLen.toNat)
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  have hC : Gas.staticcallCommitted s argsOff argsLen retOff retLen toArg
      = Gas.baseCost s.fork .STATICCALL
        + MachineState.memExpansionDelta2 s.activeWords.toNat
            argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat
        + (Gas.accountColdSurcharge s (AccountAddress.ofUInt256 toArg)
            + Gas.delegationAccessCost s (AccountAddress.ofUInt256 toArg)) := rfl
  have h_base : Gas.baseCost s.fork .STATICCALL ≤ s.gasAvailable := by
    rw [hC] at h_gas; omega
  refine stepF_eq_ok ?_
  rw [stepFE_dispatch h_run h_np h_dec h_cap h_base]
  simp only [stepF.system, h_stack]
  have h_mem : (s.consumeGas (Gas.baseCost s.fork .STATICCALL) h_base).canExpandMemory2
      argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat := by
    simp only [State.canExpandMemory2, State.consumeGas]; rw [hC] at h_gas; omega
  simp only [chargeMem2, dif_pos h_mem]
  rw [dif_pos (by
        simp only [State.consumeMemExp2, State.consumeGas]
        rw [hC] at h_gas
        simp only [MachineState.memExpansionDelta2, Operation.STATICCALL] at h_gas ⊢
        omega)]
  rw [dif_pos (by
        simp only [State.consumeMemExp2, State.consumeGas, Operation.STATICCALL] at *
        unfold Gas.staticcallCommitted at *
        simp_all only [Nat.sub_sub]
        simp only [State.fork, MachineState.memExpansionDelta2, Operation.STATICCALL]
          at h_afford ⊢
        exact h_afford)]
  rw [if_neg (by
        simpa only [State.consumeGas, State.consumeMemExp2] using h_take)]
  simp only [State.consumeGas, State.consumeMemExp2,
    State.enterCallFor, State.activeWordsAfterUInt256_2, State.callTargetCode,
    State.delegateOf, MachineState.memExpansionDelta2, hC, State.fork, h_fwd]
  grind

/-- Completeness for `StepRunning.staticcallFail`. -/
theorem complete_staticcallFail (s : State)
        (gasArg toArg argsOff argsLen retOff retLen : UInt256)
        (rest : List UInt256)
        (h_op    : s.decodedOp = some .STATICCALL)
        (h_stack : s.stack =
                     gasArg :: toArg :: argsOff :: argsLen :: retOff :: retLen :: rest)
        (h_gas   : Gas.staticcallCommitted s argsOff argsLen retOff retLen toArg
                     ≤ s.gasAvailable)
        -- Same `h_afford` as `callFail`. STATICCALL is Byzantium+ so
        -- post-EIP-150 always: the `g - g/64` cap makes this trivial,
        -- but we keep the premise for symmetry with the rest of the
        -- call family.
        (h_afford : Gas.forwardGas s.executionEnv.fork
                      (s.gasAvailable
                        - Gas.staticcallCommitted s argsOff argsLen retOff retLen toArg)
                      gasArg.toNat
                    ≤ s.gasAvailable
                      - Gas.staticcallCommitted s argsOff argsLen retOff retLen toArg)
        (h_fail  : s.executionEnv.depth ≥ 1024)
        (h_cap   : s.stack.length + Operation.pushArity .STATICCALL
                     ≤ 1024 + Operation.popArity .STATICCALL)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          ({ s with
              gasAvailable := s.gasAvailable
                              - Gas.staticcallCommitted s argsOff argsLen retOff retLen toArg
              activeWords  := s.activeWordsAfterUInt256_2
                                argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat
              returnData   := .empty
              -- EIP-2929: target warmed even on the depth silent-fail path.
              substate     := State.warmCallTarget s s.substate (AccountAddress.ofUInt256 toArg)
              stack        := UInt256.ofNat 0 :: rest
              pc           := s.pc.succ })
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  have hC : Gas.staticcallCommitted s argsOff argsLen retOff retLen toArg
      = Gas.baseCost s.fork .STATICCALL
        + MachineState.memExpansionDelta2 s.activeWords.toNat
            argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat
        + (Gas.accountColdSurcharge s (AccountAddress.ofUInt256 toArg)
            + Gas.delegationAccessCost s (AccountAddress.ofUInt256 toArg)) := rfl
  have h_base : Gas.baseCost s.fork .STATICCALL ≤ s.gasAvailable := by rw [hC] at h_gas; omega
  refine stepF_eq_ok ?_
  rw [stepFE_dispatch h_run h_np h_dec h_cap h_base]
  simp only [stepF.system, h_stack]
  have h_mem : (s.consumeGas (Gas.baseCost s.fork .STATICCALL) h_base).canExpandMemory2
      argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat := by
    simp only [State.canExpandMemory2, State.consumeGas]; rw [hC] at h_gas; omega
  simp only [chargeMem2, dif_pos h_mem]
  rw [dif_pos (by
        simp only [State.consumeMemExp2, State.consumeGas]
        rw [hC] at h_gas
        simp only [MachineState.memExpansionDelta2, Operation.STATICCALL] at h_gas ⊢
        omega)]
  rw [dif_pos (by
        simp only [State.consumeMemExp2, State.consumeGas, Operation.STATICCALL] at *
        unfold Gas.staticcallCommitted at *
        simp_all only [Nat.sub_sub]
        simp only [State.fork, MachineState.memExpansionDelta2, Operation.STATICCALL]
          at h_afford ⊢
        exact h_afford)]
  rw [if_pos (by
        simpa only [State.consumeGas, State.consumeMemExp2] using h_fail)]
  simp [State.consumeGas, State.consumeMemExp2, State.replaceStackAndIncrPC,
    State.activeWordsAfterUInt256_2, Gas.staticcallCommitted, MachineState.memExpansionDelta2,
    State.warmCallTarget, Substate.addAccessedAccount, Substate.addAccessedAccountOpt,
    State.fork, UInt256.succ,
    show ∀ (a b : UInt256), a + b = a.add b from fun _ _ => rfl]
  grind

end StepComplete
end EVM
end EvmSemantics
