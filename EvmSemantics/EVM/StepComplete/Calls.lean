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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

end StepComplete
end EVM
end EvmSemantics
