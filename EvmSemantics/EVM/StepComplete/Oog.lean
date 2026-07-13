module

public import EvmSemantics.EVM.StepComplete.Dispatch

/-!
`StepComplete.Oog` — completeness for the generic `outOfGas` exception rule of
`StepRunning`: its priority premises pin `stepF`'s path to exactly this
error kind. Proven by case analysis over the decoded operation.
-/

@[expose] public section

namespace EvmSemantics
namespace EVM
namespace StepComplete

/-! ### `Gas.totalCost` reduction lemmas (local copies)

One per dynamic-cost opcode: given the stack shape, `Gas.totalCost`
reduces to the op's concrete total. These mirror the private lemmas at
the OOG sites of `Equiv.lean` (re-proven here because those are
`private` to that file). -/

private theorem totalCost_exp {s : State} {a b : UInt256} {rest : List UInt256}
    (h : s.stack = a :: b :: rest) :
    Gas.totalCost s (.StopArith .EXP)
      = Gas.baseCost s.fork (.StopArith .EXP) + Gas.expByteCost s.fork b := by
  unfold Gas.totalCost; rw [h]

private theorem totalCost_keccak {s : State} {offset size : UInt256} {rest : List UInt256}
    (h : s.stack = offset :: size :: rest) :
    Gas.totalCost s (.Keccak .KECCAK256) = Gas.keccakTotal s offset size := by
  unfold Gas.totalCost; rw [h]

private theorem totalCost_balance {s : State} {a : UInt256} {rest : List UInt256}
    (h : s.stack = a :: rest) :
    Gas.totalCost s (.Env .BALANCE) = Gas.balanceTotal s a := by
  unfold Gas.totalCost; rw [h]

private theorem totalCost_extcodesize {s : State} {a : UInt256} {rest : List UInt256}
    (h : s.stack = a :: rest) :
    Gas.totalCost s (.Env .EXTCODESIZE) = Gas.extcodesizeTotal s a := by
  unfold Gas.totalCost; rw [h]

private theorem totalCost_extcodehash {s : State} {a : UInt256} {rest : List UInt256}
    (h : s.stack = a :: rest) :
    Gas.totalCost s (.Env .EXTCODEHASH) = Gas.extcodehashTotal s a := by
  unfold Gas.totalCost; rw [h]

private theorem totalCost_calldatacopy {s : State} {destOff srcOff sz : UInt256}
    {rest : List UInt256} (h : s.stack = destOff :: srcOff :: sz :: rest) :
    Gas.totalCost s (.Env .CALLDATACOPY) = Gas.calldatacopyTotal s destOff sz := by
  unfold Gas.totalCost; rw [h]

private theorem totalCost_codecopy {s : State} {destOff srcOff sz : UInt256}
    {rest : List UInt256} (h : s.stack = destOff :: srcOff :: sz :: rest) :
    Gas.totalCost s (.Env .CODECOPY) = Gas.codecopyTotal s destOff sz := by
  unfold Gas.totalCost; rw [h]

private theorem totalCost_extcodecopy {s : State} {a destOff srcOff sz : UInt256}
    {rest : List UInt256} (h : s.stack = a :: destOff :: srcOff :: sz :: rest) :
    Gas.totalCost s (.Env .EXTCODECOPY) = Gas.extcodecopyTotal s a destOff sz := by
  unfold Gas.totalCost; rw [h]

private theorem totalCost_returndatacopy {s : State} {destOff srcOff sz : UInt256}
    {rest : List UInt256} (h : s.stack = destOff :: srcOff :: sz :: rest) :
    Gas.totalCost s (.Env .RETURNDATACOPY) = Gas.returndatacopyTotal s destOff sz := by
  unfold Gas.totalCost; rw [h]

private theorem totalCost_mload {s : State} {offset : UInt256} {rest : List UInt256}
    (h : s.stack = offset :: rest) :
    Gas.totalCost s (.StackMemFlow .MLOAD) = Gas.mloadTotal s offset := by
  unfold Gas.totalCost; rw [h]

private theorem totalCost_mstore {s : State} {offset : UInt256} {rest : List UInt256}
    (h : s.stack = offset :: rest) :
    Gas.totalCost s (.StackMemFlow .MSTORE) = Gas.mstoreTotal s offset := by
  unfold Gas.totalCost; rw [h]

private theorem totalCost_mstore8 {s : State} {offset : UInt256} {rest : List UInt256}
    (h : s.stack = offset :: rest) :
    Gas.totalCost s (.StackMemFlow .MSTORE8) = Gas.mstore8Total s offset := by
  unfold Gas.totalCost; rw [h]

private theorem totalCost_sload {s : State} {key : UInt256} {rest : List UInt256}
    (h : s.stack = key :: rest) :
    Gas.totalCost s (.StackMemFlow .SLOAD) = Gas.sloadTotal s key := by
  unfold Gas.totalCost; rw [h]

private theorem totalCost_sstore {s : State} {key value : UInt256} {rest : List UInt256}
    (h : s.stack = key :: value :: rest) :
    Gas.totalCost s (.StackMemFlow .SSTORE)
      = Nat.max (Gas.baseCost s.fork (.StackMemFlow .SSTORE)
                  + Gas.sstoreSentryFloor s.fork)
                (Gas.sstoreTotal s key value) := by
  unfold Gas.totalCost; rw [h]

private theorem totalCost_sstore_nil {s : State} (h : s.stack = []) :
    Gas.totalCost s (.StackMemFlow .SSTORE)
      = Gas.baseCost s.fork (.StackMemFlow .SSTORE) + Gas.sstoreSentryFloor s.fork := by
  unfold Gas.totalCost; rw [h]

private theorem totalCost_sstore_one {s : State} {key : UInt256} (h : s.stack = [key]) :
    Gas.totalCost s (.StackMemFlow .SSTORE)
      = Gas.baseCost s.fork (.StackMemFlow .SSTORE) + Gas.sstoreSentryFloor s.fork := by
  unfold Gas.totalCost; rw [h]

private theorem totalCost_mcopy {s : State} {destOff srcOff sz : UInt256}
    {rest : List UInt256} (h : s.stack = destOff :: srcOff :: sz :: rest) :
    Gas.totalCost s (.StackMemFlow .MCOPY) = Gas.mcopyTotal s destOff srcOff sz := by
  unfold Gas.totalCost; rw [h]

private theorem totalCost_log {s : State} (l : Operation.LogOp) {offset size : UInt256}
    {rest : List UInt256} (h : s.stack = offset :: size :: rest) :
    Gas.totalCost s (.Log l)
      = Gas.baseCost s.fork (.Log l)
        + MachineState.memExpansionDelta s.activeWords.toNat offset.toNat size.toNat
        + Gas.logDataCost size := by
  unfold Gas.totalCost; rw [h]

private theorem totalCost_return {s : State} {offset size : UInt256} {rest : List UInt256}
    (h : s.stack = offset :: size :: rest) :
    Gas.totalCost s (.System .RETURN) = Gas.returnTotal s offset size := by
  unfold Gas.totalCost; rw [h]

private theorem totalCost_revert {s : State} {offset size : UInt256} {rest : List UInt256}
    (h : s.stack = offset :: size :: rest) :
    Gas.totalCost s (.System .REVERT) = Gas.revertTotal s offset size := by
  unfold Gas.totalCost; rw [h]

private theorem totalCost_call {s : State}
    {gasArg toArg value argsOff argsLen retOff retLen : UInt256} {rest : List UInt256}
    (h : s.stack = gasArg :: toArg :: value :: argsOff :: argsLen :: retOff :: retLen :: rest) :
    Gas.totalCost s (.System .CALL)
      = Gas.callCommitted s value argsOff argsLen retOff retLen toArg
        + Gas.forwardGas s.fork
            (s.gasAvailable - Gas.callCommitted s value argsOff argsLen retOff retLen toArg)
            gasArg.toNat := by
  unfold Gas.totalCost; rw [h]

private theorem totalCost_callcode {s : State}
    {gasArg toArg value argsOff argsLen retOff retLen : UInt256} {rest : List UInt256}
    (h : s.stack = gasArg :: toArg :: value :: argsOff :: argsLen :: retOff :: retLen :: rest) :
    Gas.totalCost s (.System .CALLCODE)
      = Gas.callcodeCommitted s value argsOff argsLen retOff retLen toArg
        + Gas.forwardGas s.fork
            (s.gasAvailable
              - Gas.callcodeCommitted s value argsOff argsLen retOff retLen toArg)
            gasArg.toNat := by
  unfold Gas.totalCost; rw [h]

private theorem totalCost_delegatecall {s : State}
    {gasArg toArg argsOff argsLen retOff retLen : UInt256} {rest : List UInt256}
    (h : s.stack = gasArg :: toArg :: argsOff :: argsLen :: retOff :: retLen :: rest) :
    Gas.totalCost s (.System .DELEGATECALL)
      = Gas.delegatecallCommitted s argsOff argsLen retOff retLen toArg
        + Gas.forwardGas s.fork
            (s.gasAvailable - Gas.delegatecallCommitted s argsOff argsLen retOff retLen toArg)
            gasArg.toNat := by
  unfold Gas.totalCost; rw [h]

private theorem totalCost_staticcall {s : State}
    {gasArg toArg argsOff argsLen retOff retLen : UInt256} {rest : List UInt256}
    (h : s.stack = gasArg :: toArg :: argsOff :: argsLen :: retOff :: retLen :: rest) :
    Gas.totalCost s (.System .STATICCALL)
      = Gas.staticcallCommitted s argsOff argsLen retOff retLen toArg
        + Gas.forwardGas s.fork
            (s.gasAvailable - Gas.staticcallCommitted s argsOff argsLen retOff retLen toArg)
            gasArg.toNat := by
  unfold Gas.totalCost; rw [h]

private theorem totalCost_selfdestruct {s : State} {beneficiary : UInt256}
    {rest : List UInt256} (h : s.stack = beneficiary :: rest) :
    Gas.totalCost s (.System .SELFDESTRUCT) = Gas.selfDestructTotal s beneficiary := by
  unfold Gas.totalCost; rw [h]

private theorem totalCost_create {s : State} {value offset size : UInt256}
    {rest : List UInt256} (h : s.stack = value :: offset :: size :: rest) :
    Gas.totalCost s (.System .CREATE)
      = Gas.createCommitted s offset size
        + Gas.allButOneSixtyFourth s.fork
            (s.gasAvailable - Gas.createCommitted s offset size) := by
  unfold Gas.totalCost; rw [h]

private theorem totalCost_create2 {s : State} {value offset size salt : UInt256}
    {rest : List UInt256} (h : s.stack = value :: offset :: size :: salt :: rest) :
    Gas.totalCost s (.System .CREATE2)
      = Gas.create2Committed s offset size
        + Gas.allButOneSixtyFourth s.fork
            (s.gasAvailable - Gas.create2Committed s offset size) := by
  unfold Gas.totalCost; rw [h]

/-- The 63/64 cap never exceeds its argument (and pre-EIP-150 it is the
    identity, still `≤`). Discharges the CREATE-family forward stage. -/
private theorem allBut64_le (f : Fork) (g : Nat) : Gas.allButOneSixtyFourth f g ≤ g := by
  unfold Gas.allButOneSixtyFourth; split <;> omega

/-- With the EIP-2200 sentry *not* firing, the SSTORE sentry-floor total
    is affordable — so `gasAvailable < base + sstoreSentryFloor` is
    contradictory. -/
private theorem sstore_floor_contra {s : State}
    (hb : Gas.baseCost s.fork (.StackMemFlow .SSTORE) ≤ s.gasAvailable)
    (hsent : ¬ Gas.sstoreSentry s.fork
      (s.gasAvailable - Gas.baseCost s.fork (.StackMemFlow .SSTORE)) = true)
    (hlt : s.gasAvailable < Gas.baseCost s.fork (.StackMemFlow .SSTORE)
      + Gas.sstoreSentryFloor s.fork) : False := by
  unfold Gas.sstoreSentry at hsent
  unfold Gas.sstoreSentryFloor Gas.callStipend at hlt
  split at hsent
  · simp only [decide_eq_true_eq] at hsent
    rename_i hist
    rw [if_pos hist] at hlt
    omega
  · rename_i hist
    rw [if_neg hist] at hlt
    omega

/-- Completeness for `StepRunning.outOfGas`. -/
theorem complete_outOfGas (s : State) (op : Operation) (cost : Nat)
        (h_op       : s.decodedOp = some op)
        (h_cap      : s.stack.length + op.pushArity ≤ 1024 + op.popArity)
        (h_reach    : s.gasAvailable < Gas.baseCost s.fork op ∨ s.oogReach op)
        (h_cost_ub  : cost ≤ Gas.totalCost s op)
        (h_gas      : s.gasAvailable < cost)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s = ({ s with halt := .Exception .OutOfGas })
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  refine stepF_eq_error ?_
  have hlt : s.gasAvailable < Gas.totalCost s op := by omega
  clear h_cost_ub h_gas h_op
  rcases h_reach with hbase | h_reach
  · exact stepFE_baseOog h_run h_np h_dec h_cap hbase
  by_cases hb : Gas.baseCost s.fork op ≤ s.gasAvailable
  case neg => exact stepFE_baseOog h_run h_np h_dec h_cap (by omega)
  rw [stepFE_dispatch h_run h_np h_dec h_cap hb]
  cases op with
  | StopArith o =>
    cases o
    case EXP =>
      show stepF.stopArith s
          (s.consumeGas (Gas.baseCost s.fork (.StopArith .EXP)) hb) .EXP
        = .error .OutOfGas
      have hlen : 2 ≤ s.stack.length := h_reach
      rcases hs : s.stack with _ | ⟨a, _ | ⟨b, rest⟩⟩
      · simp [hs] at hlen
      · simp [hs] at hlen
      · rw [totalCost_exp hs] at hlt
        have hdyn : ¬ Gas.expByteCost s.fork b ≤
            (s.consumeGas (Gas.baseCost s.fork (.StopArith .EXP)) hb).gasAvailable := by
          show ¬ Gas.expByteCost s.fork b
              ≤ s.gasAvailable - Gas.baseCost s.fork (.StopArith .EXP)
          omega
        simp only [stepF.stopArith, hs, dif_neg hdyn]
    all_goals exact absurd hb (Nat.not_le.mpr hlt)
  | CompBit o => exact absurd hb (Nat.not_le.mpr hlt)
  | Keccak o =>
    cases o
    case KECCAK256 =>
      show stepF.keccak s
          (s.consumeGas (Gas.baseCost s.fork (.Keccak .KECCAK256)) hb) .KECCAK256
        = .error .OutOfGas
      have hlen : 2 ≤ s.stack.length := h_reach
      rcases hs : s.stack with _ | ⟨offset, _ | ⟨size, rest⟩⟩
      · simp [hs] at hlen
      · simp [hs] at hlen
      · rw [totalCost_keccak hs] at hlt
        by_cases hmem : (s.consumeGas (Gas.baseCost s.fork (.Keccak .KECCAK256))
            hb).canExpandMemory offset.toNat size.toNat
        · simp only [stepF.keccak, hs, chargeMem, dif_pos hmem]
          split
          · rename_i hdyn
            exfalso
            have hmem' : MachineState.memCost (MachineState.activeWordsAfter
                  s.activeWords.toNat offset.toNat size.toNat)
                - MachineState.memCost s.activeWords.toNat
                ≤ s.gasAvailable - Gas.baseCost s.fork (.Keccak .KECCAK256) := hmem
            have hdyn' : Gas.keccakWordCost size
                ≤ s.gasAvailable - Gas.baseCost s.fork (.Keccak .KECCAK256)
                  - (MachineState.memCost (MachineState.activeWordsAfter
                      s.activeWords.toNat offset.toNat size.toNat)
                    - MachineState.memCost s.activeWords.toNat) := hdyn
            have hlt' : s.gasAvailable < Gas.baseCost s.fork (.Keccak .KECCAK256)
                + (MachineState.memCost (MachineState.activeWordsAfter
                    s.activeWords.toNat offset.toNat size.toNat)
                  - MachineState.memCost s.activeWords.toNat)
                + Gas.keccakWordCost size := hlt
            omega
          · rfl
        · simp only [stepF.keccak, hs, chargeMem, dif_neg hmem]
  | Env o =>
    cases o
    case BALANCE =>
      show stepF.env s
          (s.consumeGas (Gas.baseCost s.fork (.Env .BALANCE)) hb) .BALANCE
        = .error .OutOfGas
      have hlen : 1 ≤ s.stack.length := h_reach
      rcases hs : s.stack with _ | ⟨a, rest⟩
      · simp [hs] at hlen
      · rw [totalCost_balance hs] at hlt
        simp only [stepF.env, hs, dif_neg (Nat.not_le.mpr hlt)]
    case EXTCODESIZE =>
      show stepF.env s
          (s.consumeGas (Gas.baseCost s.fork (.Env .EXTCODESIZE)) hb) .EXTCODESIZE
        = .error .OutOfGas
      have hlen : 1 ≤ s.stack.length := h_reach
      rcases hs : s.stack with _ | ⟨a, rest⟩
      · simp [hs] at hlen
      · rw [totalCost_extcodesize hs] at hlt
        simp only [stepF.env, hs, dif_neg (Nat.not_le.mpr hlt)]
    case EXTCODEHASH =>
      show stepF.env s
          (s.consumeGas (Gas.baseCost s.fork (.Env .EXTCODEHASH)) hb) .EXTCODEHASH
        = .error .OutOfGas
      have hlen : 1 ≤ s.stack.length := h_reach
      rcases hs : s.stack with _ | ⟨a, rest⟩
      · simp [hs] at hlen
      · rw [totalCost_extcodehash hs] at hlt
        simp only [stepF.env, hs, dif_neg (Nat.not_le.mpr hlt)]
    case CALLDATACOPY =>
      show stepF.env s
          (s.consumeGas (Gas.baseCost s.fork (.Env .CALLDATACOPY)) hb) .CALLDATACOPY
        = .error .OutOfGas
      have hlen : 3 ≤ s.stack.length := h_reach
      rcases hs : s.stack with _ | ⟨destOff, _ | ⟨srcOff, _ | ⟨sz, rest⟩⟩⟩
      · simp [hs] at hlen
      · simp [hs] at hlen
      · simp [hs] at hlen
      · rw [totalCost_calldatacopy hs] at hlt
        by_cases hmem : (s.consumeGas (Gas.baseCost s.fork (.Env .CALLDATACOPY))
            hb).canExpandMemory destOff.toNat sz.toNat
        · simp only [stepF.env, hs, chargeMem, dif_pos hmem]
          split
          · rename_i hdyn
            exfalso
            have hmem' : MachineState.memCost (MachineState.activeWordsAfter
                  s.activeWords.toNat destOff.toNat sz.toNat)
                - MachineState.memCost s.activeWords.toNat
                ≤ s.gasAvailable - Gas.baseCost s.fork (.Env .CALLDATACOPY) := hmem
            have hdyn' : Gas.copyWordCost sz
                ≤ s.gasAvailable - Gas.baseCost s.fork (.Env .CALLDATACOPY)
                  - (MachineState.memCost (MachineState.activeWordsAfter
                      s.activeWords.toNat destOff.toNat sz.toNat)
                    - MachineState.memCost s.activeWords.toNat) := hdyn
            have hlt' : s.gasAvailable < Gas.baseCost s.fork (.Env .CALLDATACOPY)
                + (MachineState.memCost (MachineState.activeWordsAfter
                    s.activeWords.toNat destOff.toNat sz.toNat)
                  - MachineState.memCost s.activeWords.toNat)
                + Gas.copyWordCost sz := hlt
            omega
          · rfl
        · simp only [stepF.env, hs, chargeMem, dif_neg hmem]
    case CODECOPY =>
      show stepF.env s
          (s.consumeGas (Gas.baseCost s.fork (.Env .CODECOPY)) hb) .CODECOPY
        = .error .OutOfGas
      have hlen : 3 ≤ s.stack.length := h_reach
      rcases hs : s.stack with _ | ⟨destOff, _ | ⟨srcOff, _ | ⟨sz, rest⟩⟩⟩
      · simp [hs] at hlen
      · simp [hs] at hlen
      · simp [hs] at hlen
      · rw [totalCost_codecopy hs] at hlt
        by_cases hmem : (s.consumeGas (Gas.baseCost s.fork (.Env .CODECOPY))
            hb).canExpandMemory destOff.toNat sz.toNat
        · simp only [stepF.env, hs, chargeMem, dif_pos hmem]
          split
          · rename_i hdyn
            exfalso
            have hmem' : MachineState.memCost (MachineState.activeWordsAfter
                  s.activeWords.toNat destOff.toNat sz.toNat)
                - MachineState.memCost s.activeWords.toNat
                ≤ s.gasAvailable - Gas.baseCost s.fork (.Env .CODECOPY) := hmem
            have hdyn' : Gas.copyWordCost sz
                ≤ s.gasAvailable - Gas.baseCost s.fork (.Env .CODECOPY)
                  - (MachineState.memCost (MachineState.activeWordsAfter
                      s.activeWords.toNat destOff.toNat sz.toNat)
                    - MachineState.memCost s.activeWords.toNat) := hdyn
            have hlt' : s.gasAvailable < Gas.baseCost s.fork (.Env .CODECOPY)
                + (MachineState.memCost (MachineState.activeWordsAfter
                    s.activeWords.toNat destOff.toNat sz.toNat)
                  - MachineState.memCost s.activeWords.toNat)
                + Gas.copyWordCost sz := hlt
            omega
          · rfl
        · simp only [stepF.env, hs, chargeMem, dif_neg hmem]
    case EXTCODECOPY =>
      show stepF.env s
          (s.consumeGas (Gas.baseCost s.fork (.Env .EXTCODECOPY)) hb) .EXTCODECOPY
        = .error .OutOfGas
      have hlen : 4 ≤ s.stack.length := h_reach
      rcases hs : s.stack with _ | ⟨a, _ | ⟨destOff, _ | ⟨srcOff, _ | ⟨sz, rest⟩⟩⟩⟩
      · simp [hs] at hlen
      · simp [hs] at hlen
      · simp [hs] at hlen
      · simp [hs] at hlen
      · rw [totalCost_extcodecopy hs] at hlt
        by_cases hmem : (s.consumeGas (Gas.baseCost s.fork (.Env .EXTCODECOPY))
            hb).canExpandMemory destOff.toNat sz.toNat
        · simp only [stepF.env, hs, chargeMem, dif_pos hmem]
          split
          · rename_i hdyn
            exfalso
            have hmem' : MachineState.memCost (MachineState.activeWordsAfter
                  s.activeWords.toNat destOff.toNat sz.toNat)
                - MachineState.memCost s.activeWords.toNat
                ≤ s.gasAvailable - Gas.baseCost s.fork (.Env .EXTCODECOPY) := hmem
            have hdyn' : Gas.copyWordCost sz
                  + Gas.accountColdSurcharge s (AccountAddress.ofUInt256 a)
                ≤ s.gasAvailable - Gas.baseCost s.fork (.Env .EXTCODECOPY)
                  - (MachineState.memCost (MachineState.activeWordsAfter
                      s.activeWords.toNat destOff.toNat sz.toNat)
                    - MachineState.memCost s.activeWords.toNat) := hdyn
            have hlt' : s.gasAvailable < Gas.baseCost s.fork (.Env .EXTCODECOPY)
                + (MachineState.memCost (MachineState.activeWordsAfter
                    s.activeWords.toNat destOff.toNat sz.toNat)
                  - MachineState.memCost s.activeWords.toNat)
                + (Gas.copyWordCost sz
                   + Gas.accountColdSurcharge s (AccountAddress.ofUInt256 a)) := hlt
            omega
          · rfl
        · simp only [stepF.env, hs, chargeMem, dif_neg hmem]
    case RETURNDATACOPY =>
      show stepF.env s
          (s.consumeGas (Gas.baseCost s.fork (.Env .RETURNDATACOPY)) hb) .RETURNDATACOPY
        = .error .OutOfGas
      unfold State.oogReach at h_reach
      rcases hs : s.stack with _ | ⟨destOff, _ | ⟨srcOff, _ | ⟨sz, rest⟩⟩⟩
      · rw [hs] at h_reach; exact h_reach.elim
      · rw [hs] at h_reach; exact h_reach.elim
      · rw [hs] at h_reach; exact h_reach.elim
      · rw [hs] at h_reach
        have hoob : srcOff.toNat + sz.toNat ≤ s.returnData.size := h_reach
        have hno : ¬ srcOff.toNat + sz.toNat > s.returnData.size := by omega
        rw [totalCost_returndatacopy hs] at hlt
        by_cases hmem : (s.consumeGas (Gas.baseCost s.fork (.Env .RETURNDATACOPY))
            hb).canExpandMemory destOff.toNat sz.toNat
        · simp only [stepF.env, hs, if_neg hno, chargeMem, dif_pos hmem]
          split
          · rename_i hdyn
            exfalso
            have hmem' : MachineState.memCost (MachineState.activeWordsAfter
                  s.activeWords.toNat destOff.toNat sz.toNat)
                - MachineState.memCost s.activeWords.toNat
                ≤ s.gasAvailable - Gas.baseCost s.fork (.Env .RETURNDATACOPY) := hmem
            have hdyn' : Gas.copyWordCost sz
                ≤ s.gasAvailable - Gas.baseCost s.fork (.Env .RETURNDATACOPY)
                  - (MachineState.memCost (MachineState.activeWordsAfter
                      s.activeWords.toNat destOff.toNat sz.toNat)
                    - MachineState.memCost s.activeWords.toNat) := hdyn
            have hlt' : s.gasAvailable < Gas.baseCost s.fork (.Env .RETURNDATACOPY)
                + (MachineState.memCost (MachineState.activeWordsAfter
                    s.activeWords.toNat destOff.toNat sz.toNat)
                  - MachineState.memCost s.activeWords.toNat)
                + Gas.copyWordCost sz := hlt
            omega
          · rfl
        · simp only [stepF.env, hs, if_neg hno, chargeMem, dif_neg hmem]
    all_goals exact absurd hb (Nat.not_le.mpr hlt)
  | Block o => exact absurd hb (Nat.not_le.mpr hlt)
  | StackMemFlow o =>
    cases o
    case MLOAD =>
      show stepF.stackMemFlow s
          (s.consumeGas (Gas.baseCost s.fork (.StackMemFlow .MLOAD)) hb) .MLOAD
        = .error .OutOfGas
      have hlen : 1 ≤ s.stack.length := h_reach
      rcases hs : s.stack with _ | ⟨offset, rest⟩
      · simp [hs] at hlen
      · rw [totalCost_mload hs] at hlt
        by_cases hmem : (s.consumeGas (Gas.baseCost s.fork (.StackMemFlow .MLOAD))
            hb).canExpandMemory offset.toNat 32
        · exfalso
          have hmem' : MachineState.memCost (MachineState.activeWordsAfter
                s.activeWords.toNat offset.toNat 32)
              - MachineState.memCost s.activeWords.toNat
              ≤ s.gasAvailable - Gas.baseCost s.fork (.StackMemFlow .MLOAD) := hmem
          have hlt' : s.gasAvailable < Gas.baseCost s.fork (.StackMemFlow .MLOAD)
              + (MachineState.memCost (MachineState.activeWordsAfter
                  s.activeWords.toNat offset.toNat 32)
                - MachineState.memCost s.activeWords.toNat) := hlt
          omega
        · simp only [stepF.stackMemFlow, hs, chargeMem, dif_neg hmem]
    case MSTORE =>
      show stepF.stackMemFlow s
          (s.consumeGas (Gas.baseCost s.fork (.StackMemFlow .MSTORE)) hb) .MSTORE
        = .error .OutOfGas
      have hlen : 2 ≤ s.stack.length := h_reach
      rcases hs : s.stack with _ | ⟨offset, _ | ⟨value, rest⟩⟩
      · simp [hs] at hlen
      · simp [hs] at hlen
      · rw [totalCost_mstore hs] at hlt
        by_cases hmem : (s.consumeGas (Gas.baseCost s.fork (.StackMemFlow .MSTORE))
            hb).canExpandMemory offset.toNat 32
        · exfalso
          have hmem' : MachineState.memCost (MachineState.activeWordsAfter
                s.activeWords.toNat offset.toNat 32)
              - MachineState.memCost s.activeWords.toNat
              ≤ s.gasAvailable - Gas.baseCost s.fork (.StackMemFlow .MSTORE) := hmem
          have hlt' : s.gasAvailable < Gas.baseCost s.fork (.StackMemFlow .MSTORE)
              + (MachineState.memCost (MachineState.activeWordsAfter
                  s.activeWords.toNat offset.toNat 32)
                - MachineState.memCost s.activeWords.toNat) := hlt
          omega
        · simp only [stepF.stackMemFlow, hs, chargeMem, dif_neg hmem]
    case MSTORE8 =>
      show stepF.stackMemFlow s
          (s.consumeGas (Gas.baseCost s.fork (.StackMemFlow .MSTORE8)) hb) .MSTORE8
        = .error .OutOfGas
      have hlen : 2 ≤ s.stack.length := h_reach
      rcases hs : s.stack with _ | ⟨offset, _ | ⟨value, rest⟩⟩
      · simp [hs] at hlen
      · simp [hs] at hlen
      · rw [totalCost_mstore8 hs] at hlt
        by_cases hmem : (s.consumeGas (Gas.baseCost s.fork (.StackMemFlow .MSTORE8))
            hb).canExpandMemory offset.toNat 1
        · exfalso
          have hmem' : MachineState.memCost (MachineState.activeWordsAfter
                s.activeWords.toNat offset.toNat 1)
              - MachineState.memCost s.activeWords.toNat
              ≤ s.gasAvailable - Gas.baseCost s.fork (.StackMemFlow .MSTORE8) := hmem
          have hlt' : s.gasAvailable < Gas.baseCost s.fork (.StackMemFlow .MSTORE8)
              + (MachineState.memCost (MachineState.activeWordsAfter
                  s.activeWords.toNat offset.toNat 1)
                - MachineState.memCost s.activeWords.toNat) := hlt
          omega
        · simp only [stepF.stackMemFlow, hs, chargeMem, dif_neg hmem]
    case SLOAD =>
      show stepF.stackMemFlow s
          (s.consumeGas (Gas.baseCost s.fork (.StackMemFlow .SLOAD)) hb) .SLOAD
        = .error .OutOfGas
      have hlen : 1 ≤ s.stack.length := h_reach
      rcases hs : s.stack with _ | ⟨key, rest⟩
      · simp [hs] at hlen
      · rw [totalCost_sload hs] at hlt
        simp only [stepF.stackMemFlow, hs, dif_neg (Nat.not_le.mpr hlt)]
    case SSTORE =>
      show stepF.stackMemFlow s
          (s.consumeGas (Gas.baseCost s.fork (.StackMemFlow .SSTORE)) hb) .SSTORE
        = .error .OutOfGas
      have hperm : s.executionEnv.permitStateMutation = true := h_reach
      have hns : ¬ ¬ (s.executionEnv.permitStateMutation = true) := by simp [hperm]
      by_cases hsent : Gas.sstoreSentry s.fork
          (s.consumeGas (Gas.baseCost s.fork (.StackMemFlow .SSTORE)) hb).gasAvailable = true
      · simp only [stepF.stackMemFlow, if_neg hns, if_pos hsent]
      · rcases hs : s.stack with _ | ⟨key, _ | ⟨value, rest⟩⟩
        · rw [totalCost_sstore_nil hs] at hlt
          exact (sstore_floor_contra hb hsent hlt).elim
        · rw [totalCost_sstore_one hs] at hlt
          exact (sstore_floor_contra hb hsent hlt).elim
        · rw [totalCost_sstore hs] at hlt
          have hcost : ¬ (Gas.sstoreCost s.fork
                (s.substate.originalStorage s.executionEnv.address key)
                ((s.accountMap s.executionEnv.address).storage key) value
              + Gas.sstoreColdSurcharge s key
              ≤ (s.consumeGas (Gas.baseCost s.fork (.StackMemFlow .SSTORE))
                  hb).gasAvailable) := by
            intro hc
            have hc' : Gas.sstoreCost s.fork
                  (s.substate.originalStorage s.executionEnv.address key)
                  ((s.accountMap s.executionEnv.address).storage key) value
                + Gas.sstoreColdSurcharge s key
                ≤ s.gasAvailable - Gas.baseCost s.fork (.StackMemFlow .SSTORE) := hc
            have htot : Gas.sstoreTotal s key value
                = Gas.baseCost s.fork (.StackMemFlow .SSTORE)
                  + (Gas.sstoreCost s.fork
                      (s.substate.originalStorage s.executionEnv.address key)
                      ((s.accountMap s.executionEnv.address).storage key) value
                    + Gas.sstoreColdSurcharge s key) := rfl
            rw [htot] at hlt
            rcases Nat.lt_or_ge s.gasAvailable
                (Gas.baseCost s.fork (.StackMemFlow .SSTORE)
                  + Gas.sstoreSentryFloor s.fork) with h1 | h1
            · exact sstore_floor_contra hb hsent h1
            · have h2 : Nat.max
                  (Gas.baseCost s.fork (.StackMemFlow .SSTORE)
                    + Gas.sstoreSentryFloor s.fork)
                  (Gas.baseCost s.fork (.StackMemFlow .SSTORE)
                    + (Gas.sstoreCost s.fork
                        (s.substate.originalStorage s.executionEnv.address key)
                        ((s.accountMap s.executionEnv.address).storage key) value
                      + Gas.sstoreColdSurcharge s key))
                  ≤ s.gasAvailable := Nat.max_le.mpr ⟨h1, by omega⟩
              omega
          simp only [stepF.stackMemFlow, if_neg hns, if_neg hsent, hs, dif_neg hcost]
    case MCOPY =>
      show stepF.stackMemFlow s
          (s.consumeGas (Gas.baseCost s.fork (.StackMemFlow .MCOPY)) hb) .MCOPY
        = .error .OutOfGas
      have hlen : 3 ≤ s.stack.length := h_reach
      rcases hs : s.stack with _ | ⟨destOff, _ | ⟨srcOff, _ | ⟨sz, rest⟩⟩⟩
      · simp [hs] at hlen
      · simp [hs] at hlen
      · simp [hs] at hlen
      · rw [totalCost_mcopy hs] at hlt
        by_cases hmem : (s.consumeGas (Gas.baseCost s.fork (.StackMemFlow .MCOPY))
            hb).canExpandMemory2 destOff.toNat sz.toNat srcOff.toNat sz.toNat
        · simp only [stepF.stackMemFlow, hs, chargeMem2, dif_pos hmem]
          split
          · rename_i hdyn
            exfalso
            have hmem' : MachineState.memCost (MachineState.activeWordsAfter
                  (MachineState.activeWordsAfter s.activeWords.toNat
                    destOff.toNat sz.toNat) srcOff.toNat sz.toNat)
                - MachineState.memCost s.activeWords.toNat
                ≤ s.gasAvailable - Gas.baseCost s.fork (.StackMemFlow .MCOPY) := hmem
            have hdyn' : Gas.copyWordCost sz
                ≤ s.gasAvailable - Gas.baseCost s.fork (.StackMemFlow .MCOPY)
                  - (MachineState.memCost (MachineState.activeWordsAfter
                      (MachineState.activeWordsAfter s.activeWords.toNat
                        destOff.toNat sz.toNat) srcOff.toNat sz.toNat)
                    - MachineState.memCost s.activeWords.toNat) := hdyn
            have hlt' : s.gasAvailable < Gas.baseCost s.fork (.StackMemFlow .MCOPY)
                + (MachineState.memCost (MachineState.activeWordsAfter
                    (MachineState.activeWordsAfter s.activeWords.toNat
                      destOff.toNat sz.toNat) srcOff.toNat sz.toNat)
                  - MachineState.memCost s.activeWords.toNat)
                + Gas.copyWordCost sz := hlt
            omega
          · rfl
        · simp only [stepF.stackMemFlow, hs, chargeMem2, dif_neg hmem]
    all_goals exact absurd hb (Nat.not_le.mpr hlt)
  | Push o => exact absurd hb (Nat.not_le.mpr hlt)
  | Dup o => exact absurd hb (Nat.not_le.mpr hlt)
  | Swap o => exact absurd hb (Nat.not_le.mpr hlt)
  | DupN o => exact absurd hb (Nat.not_le.mpr hlt)
  | SwapN o => exact absurd hb (Nat.not_le.mpr hlt)
  | Exchange o => exact absurd hb (Nat.not_le.mpr hlt)
  | Log o =>
    show stepF.log s (s.consumeGas (Gas.baseCost s.fork (.Log o)) hb) o
      = .error .OutOfGas
    obtain ⟨hperm, hlen⟩ : s.executionEnv.permitStateMutation = true ∧ 2 ≤ s.stack.length :=
      h_reach
    have hns : ¬ ¬ (s.executionEnv.permitStateMutation = true) := by simp [hperm]
    rcases hs : s.stack with _ | ⟨offset, _ | ⟨size, rest⟩⟩
    · simp [hs] at hlen
    · simp [hs] at hlen
    · rw [totalCost_log o hs] at hlt
      by_cases hmem : (s.consumeGas (Gas.baseCost s.fork (.Log o))
          hb).canExpandMemory offset.toNat size.toNat
      · simp only [stepF.log, if_neg hns, hs, chargeMem, dif_pos hmem]
        split
        · rename_i hdyn
          exfalso
          have hmem' : MachineState.memCost (MachineState.activeWordsAfter
                s.activeWords.toNat offset.toNat size.toNat)
              - MachineState.memCost s.activeWords.toNat
              ≤ s.gasAvailable - Gas.baseCost s.fork (.Log o) := by
            simpa only [State.canExpandMemory, State.consumeGas,
                        MachineState.memExpansionDelta] using hmem
          have hdyn' : Gas.logDataCost size
              ≤ s.gasAvailable - Gas.baseCost s.fork (.Log o)
                - (MachineState.memCost (MachineState.activeWordsAfter
                    s.activeWords.toNat offset.toNat size.toNat)
                  - MachineState.memCost s.activeWords.toNat) := by
            simpa only [State.consumeMemExp, State.consumeGas] using hdyn
          have hlt' : s.gasAvailable < Gas.baseCost s.fork (.Log o)
              + (MachineState.memCost (MachineState.activeWordsAfter
                  s.activeWords.toNat offset.toNat size.toNat)
                - MachineState.memCost s.activeWords.toNat)
              + Gas.logDataCost size := by
            simpa only [MachineState.memExpansionDelta] using hlt
          omega
        · rfl
      · simp only [stepF.log, if_neg hns, hs, chargeMem, dif_neg hmem]
  | System o =>
    cases o
    case RETURN =>
      show stepF.system s
          (s.consumeGas (Gas.baseCost s.fork (.System .RETURN)) hb) .RETURN
        = .error .OutOfGas
      have hlen : 2 ≤ s.stack.length := h_reach
      rcases hs : s.stack with _ | ⟨offset, _ | ⟨size, rest⟩⟩
      · simp [hs] at hlen
      · simp [hs] at hlen
      · rw [totalCost_return hs] at hlt
        by_cases hmem : (s.consumeGas (Gas.baseCost s.fork (.System .RETURN))
            hb).canExpandMemory offset.toNat size.toNat
        · exfalso
          have hmem' : MachineState.memCost (MachineState.activeWordsAfter
                s.activeWords.toNat offset.toNat size.toNat)
              - MachineState.memCost s.activeWords.toNat
              ≤ s.gasAvailable - Gas.baseCost s.fork (.System .RETURN) := hmem
          have hlt' : s.gasAvailable < Gas.baseCost s.fork (.System .RETURN)
              + (MachineState.memCost (MachineState.activeWordsAfter
                  s.activeWords.toNat offset.toNat size.toNat)
                - MachineState.memCost s.activeWords.toNat) := hlt
          omega
        · simp only [stepF.system, hs, chargeMem, dif_neg hmem]
    case REVERT =>
      show stepF.system s
          (s.consumeGas (Gas.baseCost s.fork (.System .REVERT)) hb) .REVERT
        = .error .OutOfGas
      have hlen : 2 ≤ s.stack.length := h_reach
      rcases hs : s.stack with _ | ⟨offset, _ | ⟨size, rest⟩⟩
      · simp [hs] at hlen
      · simp [hs] at hlen
      · rw [totalCost_revert hs] at hlt
        by_cases hmem : (s.consumeGas (Gas.baseCost s.fork (.System .REVERT))
            hb).canExpandMemory offset.toNat size.toNat
        · exfalso
          have hmem' : MachineState.memCost (MachineState.activeWordsAfter
                s.activeWords.toNat offset.toNat size.toNat)
              - MachineState.memCost s.activeWords.toNat
              ≤ s.gasAvailable - Gas.baseCost s.fork (.System .REVERT) := hmem
          have hlt' : s.gasAvailable < Gas.baseCost s.fork (.System .REVERT)
              + (MachineState.memCost (MachineState.activeWordsAfter
                  s.activeWords.toNat offset.toNat size.toNat)
                - MachineState.memCost s.activeWords.toNat) := hlt
          omega
        · simp only [stepF.system, hs, chargeMem, dif_neg hmem]
    case CALL =>
      show stepF.system s
          (s.consumeGas (Gas.baseCost s.fork (.System .CALL)) hb) .CALL
        = .error .OutOfGas
      unfold State.oogReach at h_reach
      rcases hs : s.stack with
        _ | ⟨gasArg, _ | ⟨toArg, _ | ⟨value, _ | ⟨argsOff,
          _ | ⟨argsLen, _ | ⟨retOff, _ | ⟨retLen, rest⟩⟩⟩⟩⟩⟩⟩
      · rw [hs] at h_reach; exact h_reach.elim
      · rw [hs] at h_reach; exact h_reach.elim
      · rw [hs] at h_reach; exact h_reach.elim
      · rw [hs] at h_reach; exact h_reach.elim
      · rw [hs] at h_reach; exact h_reach.elim
      · rw [hs] at h_reach; exact h_reach.elim
      · rw [hs] at h_reach; exact h_reach.elim
      · rw [hs] at h_reach
        have hr : s.executionEnv.permitStateMutation = true ∨ value.toNat = 0 := h_reach
        have hns : ¬ (¬ s.executionEnv.permitStateMutation = true ∧ value.toNat ≠ 0) :=
          fun hc => hr.elim (fun h => hc.1 h) (fun h => hc.2 h)
        rw [totalCost_call hs] at hlt
        by_cases hmem : (s.consumeGas (Gas.baseCost s.fork (.System .CALL))
            hb).canExpandMemory2 argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat
        · simp only [stepF.system, hs, if_neg hns, chargeMem2, dif_pos hmem]
          split
          · rename_i hsc
            split
            · rename_i hfw
              exfalso
              have hCC : Gas.callCommitted s value argsOff argsLen retOff retLen toArg
                  = Gas.baseCost s.fork (.System .CALL)
                    + (MachineState.memCost (MachineState.activeWordsAfter
                        (MachineState.activeWordsAfter s.activeWords.toNat
                          argsOff.toNat argsLen.toNat) retOff.toNat retLen.toNat)
                      - MachineState.memCost s.activeWords.toNat)
                    + (Gas.callSurcharge s.fork (value.toNat != 0)
                        (Gas.callTargetIsNew s.fork s.accountMap
                          (AccountAddress.ofUInt256 toArg))
                      + Gas.accountColdSurcharge s (AccountAddress.ofUInt256 toArg)
                      + Gas.delegationAccessCost s (AccountAddress.ofUInt256 toArg)) := rfl
              have hmem' : MachineState.memCost (MachineState.activeWordsAfter
                    (MachineState.activeWordsAfter s.activeWords.toNat
                      argsOff.toNat argsLen.toNat) retOff.toNat retLen.toNat)
                  - MachineState.memCost s.activeWords.toNat
                  ≤ s.gasAvailable - Gas.baseCost s.fork (.System .CALL) := hmem
              have hsc' : Gas.callSurcharge s.fork (value.toNat != 0)
                    (Gas.callTargetIsNew s.fork s.accountMap
                      (AccountAddress.ofUInt256 toArg))
                  + Gas.accountColdSurcharge s (AccountAddress.ofUInt256 toArg)
                  + Gas.delegationAccessCost s (AccountAddress.ofUInt256 toArg)
                  ≤ s.gasAvailable - Gas.baseCost s.fork (.System .CALL)
                    - (MachineState.memCost (MachineState.activeWordsAfter
                        (MachineState.activeWordsAfter s.activeWords.toNat
                          argsOff.toNat argsLen.toNat) retOff.toNat retLen.toNat)
                      - MachineState.memCost s.activeWords.toNat) := hsc
              have hfw' : Gas.forwardGas s.fork
                    (s.gasAvailable - Gas.baseCost s.fork (.System .CALL)
                      - (MachineState.memCost (MachineState.activeWordsAfter
                          (MachineState.activeWordsAfter s.activeWords.toNat
                            argsOff.toNat argsLen.toNat) retOff.toNat retLen.toNat)
                        - MachineState.memCost s.activeWords.toNat)
                      - (Gas.callSurcharge s.fork (value.toNat != 0)
                          (Gas.callTargetIsNew s.fork s.accountMap
                            (AccountAddress.ofUInt256 toArg))
                        + Gas.accountColdSurcharge s (AccountAddress.ofUInt256 toArg)
                        + Gas.delegationAccessCost s (AccountAddress.ofUInt256 toArg)))
                    gasArg.toNat
                  ≤ s.gasAvailable - Gas.baseCost s.fork (.System .CALL)
                    - (MachineState.memCost (MachineState.activeWordsAfter
                        (MachineState.activeWordsAfter s.activeWords.toNat
                          argsOff.toNat argsLen.toNat) retOff.toNat retLen.toNat)
                      - MachineState.memCost s.activeWords.toNat)
                    - (Gas.callSurcharge s.fork (value.toNat != 0)
                        (Gas.callTargetIsNew s.fork s.accountMap
                          (AccountAddress.ofUInt256 toArg))
                      + Gas.accountColdSurcharge s (AccountAddress.ofUInt256 toArg)
                      + Gas.delegationAccessCost s (AccountAddress.ofUInt256 toArg)) := hfw
              have harg : s.gasAvailable
                    - Gas.callCommitted s value argsOff argsLen retOff retLen toArg
                  = s.gasAvailable - Gas.baseCost s.fork (.System .CALL)
                    - (MachineState.memCost (MachineState.activeWordsAfter
                        (MachineState.activeWordsAfter s.activeWords.toNat
                          argsOff.toNat argsLen.toNat) retOff.toNat retLen.toNat)
                      - MachineState.memCost s.activeWords.toNat)
                    - (Gas.callSurcharge s.fork (value.toNat != 0)
                        (Gas.callTargetIsNew s.fork s.accountMap
                          (AccountAddress.ofUInt256 toArg))
                      + Gas.accountColdSurcharge s (AccountAddress.ofUInt256 toArg)
                      + Gas.delegationAccessCost s (AccountAddress.ofUInt256 toArg)) := by
                omega
              rw [harg] at hlt
              omega
            · rfl
          · rfl
        · simp only [stepF.system, hs, if_neg hns, chargeMem2, dif_neg hmem]
    case CALLCODE =>
      show stepF.system s
          (s.consumeGas (Gas.baseCost s.fork (.System .CALLCODE)) hb) .CALLCODE
        = .error .OutOfGas
      have hlen : 7 ≤ s.stack.length := h_reach
      rcases hs : s.stack with
        _ | ⟨gasArg, _ | ⟨toArg, _ | ⟨value, _ | ⟨argsOff,
          _ | ⟨argsLen, _ | ⟨retOff, _ | ⟨retLen, rest⟩⟩⟩⟩⟩⟩⟩
      · simp [hs] at hlen
      · simp [hs] at hlen
      · simp [hs] at hlen
      · simp [hs] at hlen
      · simp [hs] at hlen
      · simp [hs] at hlen
      · simp [hs] at hlen
      · rw [totalCost_callcode hs] at hlt
        by_cases hmem : (s.consumeGas (Gas.baseCost s.fork (.System .CALLCODE))
            hb).canExpandMemory2 argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat
        · simp only [stepF.system, hs, chargeMem2, dif_pos hmem]
          split
          · rename_i hsc
            split
            · rename_i hfw
              exfalso
              have hCC : Gas.callcodeCommitted s value argsOff argsLen retOff retLen toArg
                  = Gas.baseCost s.fork (.System .CALLCODE)
                    + (MachineState.memCost (MachineState.activeWordsAfter
                        (MachineState.activeWordsAfter s.activeWords.toNat
                          argsOff.toNat argsLen.toNat) retOff.toNat retLen.toNat)
                      - MachineState.memCost s.activeWords.toNat)
                    + (Gas.callSurcharge s.fork (value.toNat != 0) false
                      + Gas.accountColdSurcharge s (AccountAddress.ofUInt256 toArg)
                      + Gas.delegationAccessCost s (AccountAddress.ofUInt256 toArg)) := rfl
              have hmem' : MachineState.memCost (MachineState.activeWordsAfter
                    (MachineState.activeWordsAfter s.activeWords.toNat
                      argsOff.toNat argsLen.toNat) retOff.toNat retLen.toNat)
                  - MachineState.memCost s.activeWords.toNat
                  ≤ s.gasAvailable - Gas.baseCost s.fork (.System .CALLCODE) := hmem
              have hsc' : Gas.callSurcharge s.fork (value.toNat != 0) false
                  + Gas.accountColdSurcharge s (AccountAddress.ofUInt256 toArg)
                  + Gas.delegationAccessCost s (AccountAddress.ofUInt256 toArg)
                  ≤ s.gasAvailable - Gas.baseCost s.fork (.System .CALLCODE)
                    - (MachineState.memCost (MachineState.activeWordsAfter
                        (MachineState.activeWordsAfter s.activeWords.toNat
                          argsOff.toNat argsLen.toNat) retOff.toNat retLen.toNat)
                      - MachineState.memCost s.activeWords.toNat) := hsc
              have hfw' : Gas.forwardGas s.fork
                    (s.gasAvailable - Gas.baseCost s.fork (.System .CALLCODE)
                      - (MachineState.memCost (MachineState.activeWordsAfter
                          (MachineState.activeWordsAfter s.activeWords.toNat
                            argsOff.toNat argsLen.toNat) retOff.toNat retLen.toNat)
                        - MachineState.memCost s.activeWords.toNat)
                      - (Gas.callSurcharge s.fork (value.toNat != 0) false
                        + Gas.accountColdSurcharge s (AccountAddress.ofUInt256 toArg)
                        + Gas.delegationAccessCost s (AccountAddress.ofUInt256 toArg)))
                    gasArg.toNat
                  ≤ s.gasAvailable - Gas.baseCost s.fork (.System .CALLCODE)
                    - (MachineState.memCost (MachineState.activeWordsAfter
                        (MachineState.activeWordsAfter s.activeWords.toNat
                          argsOff.toNat argsLen.toNat) retOff.toNat retLen.toNat)
                      - MachineState.memCost s.activeWords.toNat)
                    - (Gas.callSurcharge s.fork (value.toNat != 0) false
                      + Gas.accountColdSurcharge s (AccountAddress.ofUInt256 toArg)
                      + Gas.delegationAccessCost s (AccountAddress.ofUInt256 toArg)) := hfw
              have harg : s.gasAvailable
                    - Gas.callcodeCommitted s value argsOff argsLen retOff retLen toArg
                  = s.gasAvailable - Gas.baseCost s.fork (.System .CALLCODE)
                    - (MachineState.memCost (MachineState.activeWordsAfter
                        (MachineState.activeWordsAfter s.activeWords.toNat
                          argsOff.toNat argsLen.toNat) retOff.toNat retLen.toNat)
                      - MachineState.memCost s.activeWords.toNat)
                    - (Gas.callSurcharge s.fork (value.toNat != 0) false
                      + Gas.accountColdSurcharge s (AccountAddress.ofUInt256 toArg)
                      + Gas.delegationAccessCost s (AccountAddress.ofUInt256 toArg)) := by
                omega
              rw [harg] at hlt
              omega
            · rfl
          · rfl
        · simp only [stepF.system, hs, chargeMem2, dif_neg hmem]
    case DELEGATECALL =>
      show stepF.system s
          (s.consumeGas (Gas.baseCost s.fork (.System .DELEGATECALL)) hb) .DELEGATECALL
        = .error .OutOfGas
      have hlen : 6 ≤ s.stack.length := h_reach
      rcases hs : s.stack with
        _ | ⟨gasArg, _ | ⟨toArg, _ | ⟨argsOff,
          _ | ⟨argsLen, _ | ⟨retOff, _ | ⟨retLen, rest⟩⟩⟩⟩⟩⟩
      · simp [hs] at hlen
      · simp [hs] at hlen
      · simp [hs] at hlen
      · simp [hs] at hlen
      · simp [hs] at hlen
      · simp [hs] at hlen
      · rw [totalCost_delegatecall hs] at hlt
        by_cases hmem : (s.consumeGas (Gas.baseCost s.fork (.System .DELEGATECALL))
            hb).canExpandMemory2 argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat
        · simp only [stepF.system, hs, chargeMem2, dif_pos hmem]
          split
          · rename_i hsc
            split
            · rename_i hfw
              exfalso
              have hCC : Gas.delegatecallCommitted s argsOff argsLen retOff retLen toArg
                  = Gas.baseCost s.fork (.System .DELEGATECALL)
                    + (MachineState.memCost (MachineState.activeWordsAfter
                        (MachineState.activeWordsAfter s.activeWords.toNat
                          argsOff.toNat argsLen.toNat) retOff.toNat retLen.toNat)
                      - MachineState.memCost s.activeWords.toNat)
                    + (Gas.accountColdSurcharge s (AccountAddress.ofUInt256 toArg)
                      + Gas.delegationAccessCost s (AccountAddress.ofUInt256 toArg)) := rfl
              have hmem' : MachineState.memCost (MachineState.activeWordsAfter
                    (MachineState.activeWordsAfter s.activeWords.toNat
                      argsOff.toNat argsLen.toNat) retOff.toNat retLen.toNat)
                  - MachineState.memCost s.activeWords.toNat
                  ≤ s.gasAvailable - Gas.baseCost s.fork (.System .DELEGATECALL) := hmem
              have hsc' : Gas.accountColdSurcharge s (AccountAddress.ofUInt256 toArg)
                  + Gas.delegationAccessCost s (AccountAddress.ofUInt256 toArg)
                  ≤ s.gasAvailable - Gas.baseCost s.fork (.System .DELEGATECALL)
                    - (MachineState.memCost (MachineState.activeWordsAfter
                        (MachineState.activeWordsAfter s.activeWords.toNat
                          argsOff.toNat argsLen.toNat) retOff.toNat retLen.toNat)
                      - MachineState.memCost s.activeWords.toNat) := hsc
              have hfw' : Gas.forwardGas s.fork
                    (s.gasAvailable - Gas.baseCost s.fork (.System .DELEGATECALL)
                      - (MachineState.memCost (MachineState.activeWordsAfter
                          (MachineState.activeWordsAfter s.activeWords.toNat
                            argsOff.toNat argsLen.toNat) retOff.toNat retLen.toNat)
                        - MachineState.memCost s.activeWords.toNat)
                      - (Gas.accountColdSurcharge s (AccountAddress.ofUInt256 toArg)
                        + Gas.delegationAccessCost s (AccountAddress.ofUInt256 toArg)))
                    gasArg.toNat
                  ≤ s.gasAvailable - Gas.baseCost s.fork (.System .DELEGATECALL)
                    - (MachineState.memCost (MachineState.activeWordsAfter
                        (MachineState.activeWordsAfter s.activeWords.toNat
                          argsOff.toNat argsLen.toNat) retOff.toNat retLen.toNat)
                      - MachineState.memCost s.activeWords.toNat)
                    - (Gas.accountColdSurcharge s (AccountAddress.ofUInt256 toArg)
                      + Gas.delegationAccessCost s (AccountAddress.ofUInt256 toArg)) := hfw
              have harg : s.gasAvailable
                    - Gas.delegatecallCommitted s argsOff argsLen retOff retLen toArg
                  = s.gasAvailable - Gas.baseCost s.fork (.System .DELEGATECALL)
                    - (MachineState.memCost (MachineState.activeWordsAfter
                        (MachineState.activeWordsAfter s.activeWords.toNat
                          argsOff.toNat argsLen.toNat) retOff.toNat retLen.toNat)
                      - MachineState.memCost s.activeWords.toNat)
                    - (Gas.accountColdSurcharge s (AccountAddress.ofUInt256 toArg)
                      + Gas.delegationAccessCost s (AccountAddress.ofUInt256 toArg)) := by
                omega
              rw [harg] at hlt
              omega
            · rfl
          · rfl
        · simp only [stepF.system, hs, chargeMem2, dif_neg hmem]
    case STATICCALL =>
      show stepF.system s
          (s.consumeGas (Gas.baseCost s.fork (.System .STATICCALL)) hb) .STATICCALL
        = .error .OutOfGas
      have hlen : 6 ≤ s.stack.length := h_reach
      rcases hs : s.stack with
        _ | ⟨gasArg, _ | ⟨toArg, _ | ⟨argsOff,
          _ | ⟨argsLen, _ | ⟨retOff, _ | ⟨retLen, rest⟩⟩⟩⟩⟩⟩
      · simp [hs] at hlen
      · simp [hs] at hlen
      · simp [hs] at hlen
      · simp [hs] at hlen
      · simp [hs] at hlen
      · simp [hs] at hlen
      · rw [totalCost_staticcall hs] at hlt
        by_cases hmem : (s.consumeGas (Gas.baseCost s.fork (.System .STATICCALL))
            hb).canExpandMemory2 argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat
        · simp only [stepF.system, hs, chargeMem2, dif_pos hmem]
          split
          · rename_i hsc
            split
            · rename_i hfw
              exfalso
              have hCC : Gas.staticcallCommitted s argsOff argsLen retOff retLen toArg
                  = Gas.baseCost s.fork (.System .STATICCALL)
                    + (MachineState.memCost (MachineState.activeWordsAfter
                        (MachineState.activeWordsAfter s.activeWords.toNat
                          argsOff.toNat argsLen.toNat) retOff.toNat retLen.toNat)
                      - MachineState.memCost s.activeWords.toNat)
                    + (Gas.accountColdSurcharge s (AccountAddress.ofUInt256 toArg)
                      + Gas.delegationAccessCost s (AccountAddress.ofUInt256 toArg)) := rfl
              have hmem' : MachineState.memCost (MachineState.activeWordsAfter
                    (MachineState.activeWordsAfter s.activeWords.toNat
                      argsOff.toNat argsLen.toNat) retOff.toNat retLen.toNat)
                  - MachineState.memCost s.activeWords.toNat
                  ≤ s.gasAvailable - Gas.baseCost s.fork (.System .STATICCALL) := hmem
              have hsc' : Gas.accountColdSurcharge s (AccountAddress.ofUInt256 toArg)
                  + Gas.delegationAccessCost s (AccountAddress.ofUInt256 toArg)
                  ≤ s.gasAvailable - Gas.baseCost s.fork (.System .STATICCALL)
                    - (MachineState.memCost (MachineState.activeWordsAfter
                        (MachineState.activeWordsAfter s.activeWords.toNat
                          argsOff.toNat argsLen.toNat) retOff.toNat retLen.toNat)
                      - MachineState.memCost s.activeWords.toNat) := hsc
              have hfw' : Gas.forwardGas s.fork
                    (s.gasAvailable - Gas.baseCost s.fork (.System .STATICCALL)
                      - (MachineState.memCost (MachineState.activeWordsAfter
                          (MachineState.activeWordsAfter s.activeWords.toNat
                            argsOff.toNat argsLen.toNat) retOff.toNat retLen.toNat)
                        - MachineState.memCost s.activeWords.toNat)
                      - (Gas.accountColdSurcharge s (AccountAddress.ofUInt256 toArg)
                        + Gas.delegationAccessCost s (AccountAddress.ofUInt256 toArg)))
                    gasArg.toNat
                  ≤ s.gasAvailable - Gas.baseCost s.fork (.System .STATICCALL)
                    - (MachineState.memCost (MachineState.activeWordsAfter
                        (MachineState.activeWordsAfter s.activeWords.toNat
                          argsOff.toNat argsLen.toNat) retOff.toNat retLen.toNat)
                      - MachineState.memCost s.activeWords.toNat)
                    - (Gas.accountColdSurcharge s (AccountAddress.ofUInt256 toArg)
                      + Gas.delegationAccessCost s (AccountAddress.ofUInt256 toArg)) := hfw
              have harg : s.gasAvailable
                    - Gas.staticcallCommitted s argsOff argsLen retOff retLen toArg
                  = s.gasAvailable - Gas.baseCost s.fork (.System .STATICCALL)
                    - (MachineState.memCost (MachineState.activeWordsAfter
                        (MachineState.activeWordsAfter s.activeWords.toNat
                          argsOff.toNat argsLen.toNat) retOff.toNat retLen.toNat)
                      - MachineState.memCost s.activeWords.toNat)
                    - (Gas.accountColdSurcharge s (AccountAddress.ofUInt256 toArg)
                      + Gas.delegationAccessCost s (AccountAddress.ofUInt256 toArg)) := by
                omega
              rw [harg] at hlt
              omega
            · rfl
          · rfl
        · simp only [stepF.system, hs, chargeMem2, dif_neg hmem]
    case SELFDESTRUCT =>
      show stepF.system s
          (s.consumeGas (Gas.baseCost s.fork (.System .SELFDESTRUCT)) hb) .SELFDESTRUCT
        = .error .OutOfGas
      obtain ⟨hperm, hlen⟩ :
          s.executionEnv.permitStateMutation = true ∧ 1 ≤ s.stack.length := h_reach
      have hns : ¬ ¬ (s.executionEnv.permitStateMutation = true) := by simp [hperm]
      rcases hs : s.stack with _ | ⟨beneficiary, rest⟩
      · simp [hs] at hlen
      · rw [totalCost_selfdestruct hs] at hlt
        by_cases hsc : Gas.selfDestructSurcharge s.fork
              ((s.accountMap (AccountAddress.ofUInt256 beneficiary)).isEmpty)
              ((s.accountMap s.executionEnv.address).balance.toNat != 0)
            + Gas.selfDestructColdSurcharge s (AccountAddress.ofUInt256 beneficiary)
            ≤ (s.consumeGas (Gas.baseCost s.fork (.System .SELFDESTRUCT)) hb).gasAvailable
        · exfalso
          have hsc' : Gas.selfDestructSurcharge s.fork
                ((s.accountMap (AccountAddress.ofUInt256 beneficiary)).isEmpty)
                ((s.accountMap s.executionEnv.address).balance.toNat != 0)
              + Gas.selfDestructColdSurcharge s (AccountAddress.ofUInt256 beneficiary)
              ≤ s.gasAvailable - Gas.baseCost s.fork (.System .SELFDESTRUCT) := hsc
          have hlt' : s.gasAvailable < Gas.baseCost s.fork (.System .SELFDESTRUCT)
              + (Gas.selfDestructSurcharge s.fork
                  ((s.accountMap (AccountAddress.ofUInt256 beneficiary)).isEmpty)
                  ((s.accountMap s.executionEnv.address).balance.toNat != 0)
                + Gas.selfDestructColdSurcharge s
                    (AccountAddress.ofUInt256 beneficiary)) := hlt
          omega
        · simp only [stepF.system, hs, if_neg hns, dif_neg hsc]
    case CREATE =>
      show stepF.system s
          (s.consumeGas (Gas.baseCost s.fork (.System .CREATE)) hb) .CREATE
        = .error .OutOfGas
      obtain ⟨hperm, hlen⟩ :
          s.executionEnv.permitStateMutation = true ∧ 3 ≤ s.stack.length := h_reach
      have hns : ¬ ¬ (s.executionEnv.permitStateMutation = true) := by simp [hperm]
      rcases hs : s.stack with _ | ⟨value, _ | ⟨offset, _ | ⟨size, rest⟩⟩⟩
      · simp [hs] at hlen
      · simp [hs] at hlen
      · simp [hs] at hlen
      · by_cases hlarge : Gas.initCodeTooLarge s.fork size.toNat = true
        · simp only [stepF.system, hs, if_neg hns, if_pos hlarge]
        · rw [totalCost_create hs] at hlt
          by_cases hmem : (s.consumeGas (Gas.baseCost s.fork (.System .CREATE))
              hb).canExpandMemory offset.toNat size.toNat
          · simp only [stepF.system, hs, if_neg hns, if_neg hlarge, chargeMem, dif_pos hmem]
            split
            · rename_i hic
              exfalso
              have hCC : Gas.createCommitted s offset size
                  = Gas.baseCost s.fork (.System .CREATE)
                    + (MachineState.memCost (MachineState.activeWordsAfter
                        s.activeWords.toNat offset.toNat size.toNat)
                      - MachineState.memCost s.activeWords.toNat)
                    + Gas.initCodeWordCost s.fork size.toNat := rfl
              have hmem' : MachineState.memCost (MachineState.activeWordsAfter
                    s.activeWords.toNat offset.toNat size.toNat)
                  - MachineState.memCost s.activeWords.toNat
                  ≤ s.gasAvailable - Gas.baseCost s.fork (.System .CREATE) := by
                simpa only [State.canExpandMemory, State.consumeGas,
                            MachineState.memExpansionDelta] using hmem
              have hic' : Gas.initCodeWordCost s.fork size.toNat
                  ≤ s.gasAvailable - Gas.baseCost s.fork (.System .CREATE)
                    - (MachineState.memCost (MachineState.activeWordsAfter
                        s.activeWords.toNat offset.toNat size.toNat)
                      - MachineState.memCost s.activeWords.toNat) := by
                simpa only [State.consumeMemExp, State.consumeGas] using hic
              have hfree : Gas.allButOneSixtyFourth s.fork
                    (s.gasAvailable - Gas.createCommitted s offset size)
                  ≤ s.gasAvailable - Gas.createCommitted s offset size :=
                allBut64_le _ _
              omega
            · rfl
          · simp only [stepF.system, hs, if_neg hns, if_neg hlarge, chargeMem, dif_neg hmem]
    case CREATE2 =>
      show stepF.system s
          (s.consumeGas (Gas.baseCost s.fork (.System .CREATE2)) hb) .CREATE2
        = .error .OutOfGas
      obtain ⟨hperm, hlen⟩ :
          s.executionEnv.permitStateMutation = true ∧ 4 ≤ s.stack.length := h_reach
      have hns : ¬ ¬ (s.executionEnv.permitStateMutation = true) := by simp [hperm]
      rcases hs : s.stack with _ | ⟨value, _ | ⟨offset, _ | ⟨size, _ | ⟨salt, rest⟩⟩⟩⟩
      · simp [hs] at hlen
      · simp [hs] at hlen
      · simp [hs] at hlen
      · simp [hs] at hlen
      · by_cases hlarge : Gas.initCodeTooLarge s.fork size.toNat = true
        · simp only [stepF.system, hs, if_neg hns, if_pos hlarge]
        · rw [totalCost_create2 hs] at hlt
          by_cases hmem : (s.consumeGas (Gas.baseCost s.fork (.System .CREATE2))
              hb).canExpandMemory offset.toNat size.toNat
          · simp only [stepF.system, hs, if_neg hns, if_neg hlarge, chargeMem, dif_pos hmem]
            split
            · rename_i hhash
              exfalso
              have hCC : Gas.create2Committed s offset size
                  = Gas.baseCost s.fork (.System .CREATE2)
                    + (MachineState.memCost (MachineState.activeWordsAfter
                        s.activeWords.toNat offset.toNat size.toNat)
                      - MachineState.memCost s.activeWords.toNat)
                    + Gas.create2HashCost size.toNat
                    + Gas.initCodeWordCost s.fork size.toNat := rfl
              have hmem' : MachineState.memCost (MachineState.activeWordsAfter
                    s.activeWords.toNat offset.toNat size.toNat)
                  - MachineState.memCost s.activeWords.toNat
                  ≤ s.gasAvailable - Gas.baseCost s.fork (.System .CREATE2) := by
                simpa only [State.canExpandMemory, State.consumeGas,
                            MachineState.memExpansionDelta] using hmem
              have hhash' : Gas.create2HashCost size.toNat
                    + Gas.initCodeWordCost s.fork size.toNat
                  ≤ s.gasAvailable - Gas.baseCost s.fork (.System .CREATE2)
                    - (MachineState.memCost (MachineState.activeWordsAfter
                        s.activeWords.toNat offset.toNat size.toNat)
                      - MachineState.memCost s.activeWords.toNat) := by
                simpa only [State.consumeMemExp, State.consumeGas] using hhash
              have hfree : Gas.allButOneSixtyFourth s.fork
                    (s.gasAvailable - Gas.create2Committed s offset size)
                  ≤ s.gasAvailable - Gas.create2Committed s offset size :=
                allBut64_le _ _
              omega
            · rfl
          · simp only [stepF.system, hs, if_neg hns, if_neg hlarge, chargeMem, dif_neg hmem]
    all_goals exact absurd hb (Nat.not_le.mpr hlt)

end StepComplete
end EVM
end EvmSemantics
