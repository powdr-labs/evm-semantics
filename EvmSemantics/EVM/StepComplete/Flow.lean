module

public import EvmSemantics.EVM.StepComplete.Dispatch

/-!
`StepComplete.Flow` — completeness cases for the Flow constructors of
`StepRunning`: each constructor's premises force `stepF` to compute
exactly that constructor's successor. Assembled into
`stepRunning_complete` in `StepDeterminism.lean`.
-/

@[expose] public section

namespace EvmSemantics
namespace EVM
namespace StepComplete

private theorem popN_go_append (topics rest acc : List UInt256) :
    stepF.popN.go (topics ++ rest) topics.length acc
      = some (acc.reverse ++ topics, rest) := by
  induction topics generalizing acc with
  | nil => simp [stepF.popN.go]
  | cons t ts ih =>
    simp only [List.cons_append, List.length_cons, stepF.popN.go, Nat.succ_sub_one]
    rw [ih]
    simp

private theorem popN_append (topics rest : List UInt256) :
    stepF.popN (topics ++ rest) topics.length = some (topics, rest) := by
  unfold stepF.popN
  rw [popN_go_append]
  simp

/-- Completeness for `StepRunning.push0`. -/
theorem complete_push0 (s : State)
        (h_op      : s.decodedOp = some (.Push ⟨0, by decide⟩))
        (h_gas     : Gas.baseCost s.fork (.Push ⟨0, by decide⟩) ≤ s.gasAvailable)
        (h_cap     : s.stack.length < 1024)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := ⟨0⟩ :: s.stack
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork (.Push ⟨0, by decide⟩) }
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  refine stepF_eq_ok ?_
  rw [stepFE_dispatch h_run h_np h_dec
        (by simp only [Operation.pushArity, Operation.popArity]; omega) h_gas]
  simp only [stepF.push]
  rfl

/-- Completeness for `StepRunning.pushN`. -/
theorem complete_pushN (s : State) (k : Fin 33) (data : UInt256) (immWidth : Nat)
        (h_k_pos   : 0 < k.val)
        (h_op      : s.decoded = some (.Push ⟨k, k.isLt⟩, some (data, immWidth)))
        (h_gas     : Gas.baseCost s.fork (.Push ⟨k, k.isLt⟩) ≤ s.gasAvailable)
        (h_cap     : s.stack.length < 1024)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := data :: s.stack
              pc           := s.pc + UInt256.ofNat (immWidth + 1)
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork (.Push ⟨k, k.isLt⟩) }
    := by
  refine stepF_eq_ok ?_
  rw [stepFE_dispatch h_run h_np h_op
        (by simp only [Operation.pushArity, Operation.popArity]; omega) h_gas]
  simp only [stepF.push]
  split
  · omega
  · next _ _ _ _ _ _ hsome =>
      obtain ⟨rfl, rfl⟩ := Option.some.inj hsome
      rfl
  · rename_i heq
    simp at heq

/-- Completeness for `StepRunning.dup`. -/
theorem complete_dup (s : State) (n : Fin 16) (v : UInt256)
        (h_op      : s.decodedOp = some (.Dup ⟨n⟩))
        (h_gas     : Gas.baseCost s.fork (.Dup ⟨n⟩) ≤ s.gasAvailable)
        (h_get     : s.stack[n.val]? = some v)
        (h_cap     : s.stack.length < 1024)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := v :: s.stack
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork (.Dup ⟨n⟩) }
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  refine stepF_eq_ok ?_
  rw [stepFE_dispatch h_run h_np h_dec
        (by simp only [Operation.pushArity, Operation.popArity]; omega) h_gas]
  simp only [stepF.dup, h_get]
  rfl

/-- Completeness for `StepRunning.swap`. -/
theorem complete_swap (s : State) (n : Fin 16) (stk' : List UInt256)
        (h_op      : s.decodedOp = some (.Swap ⟨n⟩))
        (h_gas     : Gas.baseCost s.fork (.Swap ⟨n⟩) ≤ s.gasAvailable)
        (h_swap    : s.stack.exchange 0 (n.val + 1) = some stk')
        (h_cap   : s.stack.length + Operation.pushArity (.Swap ⟨n⟩)
                     ≤ 1024 + Operation.popArity (.Swap ⟨n⟩))
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := stk'
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork (.Swap ⟨n⟩) }
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  refine stepF_eq_ok ?_
  rw [stepFE_dispatch h_run h_np h_dec h_cap h_gas]
  simp only [stepF.swap, h_swap]
  rfl

/-- Completeness for `StepRunning.jump`. -/
theorem complete_jump (s : State) (dest : UInt256) (rest : List UInt256)
        (h_op    : s.decodedOp = some .JUMP)
        (h_gas   : Gas.baseCost s.fork .JUMP ≤ s.gasAvailable)
        (h_stack : s.stack = dest :: rest)
        (h_valid : Decode.isValidJumpDest s.executionEnv.code dest.toNat = true)
        (h_cap   : s.stack.length + Operation.pushArity .JUMP
                     ≤ 1024 + Operation.popArity .JUMP)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := rest
              pc           := dest
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .JUMP }
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  refine stepF_eq_ok ?_
  rw [stepFE_dispatch h_run h_np h_dec h_cap h_gas]
  simp only [stepF.stackMemFlow, h_stack]
  rw [if_pos h_valid]
  rfl

/-- Completeness for `StepRunning.jumpi_taken`. -/
theorem complete_jumpi_taken (s : State) (dest cond : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .JUMPI)
        (h_gas     : Gas.baseCost s.fork .JUMPI ≤ s.gasAvailable)
        (h_stack   : s.stack = dest :: cond :: rest)
        (h_cond    : UInt256.isTrue cond)
        (h_valid   : Decode.isValidJumpDest s.executionEnv.code dest.toNat = true)
        (h_cap   : s.stack.length + Operation.pushArity .JUMPI
                     ≤ 1024 + Operation.popArity .JUMPI)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := rest
              pc           := dest
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .JUMPI }
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  refine stepF_eq_ok ?_
  rw [stepFE_dispatch h_run h_np h_dec h_cap h_gas]
  simp only [stepF.stackMemFlow, h_stack]
  rw [if_neg h_cond, if_pos h_valid]
  rfl

/-- Completeness for `StepRunning.jumpi_notTaken`. -/
theorem complete_jumpi_notTaken (s : State) (dest cond : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .JUMPI)
        (h_gas     : Gas.baseCost s.fork .JUMPI ≤ s.gasAvailable)
        (h_stack   : s.stack = dest :: cond :: rest)
        (h_cond    : ¬ UInt256.isTrue cond)
        (h_cap   : s.stack.length + Operation.pushArity .JUMPI
                     ≤ 1024 + Operation.popArity .JUMPI)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .JUMPI }
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  refine stepF_eq_ok ?_
  rw [stepFE_dispatch h_run h_np h_dec h_cap h_gas]
  simp only [stepF.stackMemFlow, h_stack]
  rw [if_pos (not_not.mp h_cond)]
  rfl

/-- Completeness for `StepRunning.pc`. -/
theorem complete_pc (s : State)
        (h_op      : s.decodedOp = some .PC)
        (h_gas     : Gas.baseCost s.fork .PC ≤ s.gasAvailable)
        (h_cap     : s.stack.length < 1024)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := s.pc :: s.stack
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .PC }
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  refine stepF_eq_ok ?_
  rw [stepFE_dispatch h_run h_np h_dec
        (by simp only [Operation.pushArity, Operation.popArity]; omega) h_gas]
  simp only [stepF.stackMemFlow]
  rfl

/-- Completeness for `StepRunning.gas`. -/
theorem complete_gas (s : State)
        (h_op      : s.decodedOp = some .GAS)
        (h_gas     : Gas.baseCost s.fork .GAS ≤ s.gasAvailable)
        (h_cap     : s.stack.length < 1024)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := UInt256.ofNat (s.gasAvailable - Gas.baseCost s.fork .GAS)
                                :: s.stack
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .GAS }
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  refine stepF_eq_ok ?_
  rw [stepFE_dispatch h_run h_np h_dec
        (by simp only [Operation.pushArity, Operation.popArity]; omega) h_gas]
  simp only [stepF.stackMemFlow]
  rfl

/-- Completeness for `StepRunning.jumpdest`. -/
theorem complete_jumpdest (s : State)
        (h_op      : s.decodedOp = some .JUMPDEST)
        (h_gas     : Gas.baseCost s.fork .JUMPDEST ≤ s.gasAvailable)
        (h_cap   : s.stack.length + Operation.pushArity .JUMPDEST
                     ≤ 1024 + Operation.popArity .JUMPDEST)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .JUMPDEST }
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  refine stepF_eq_ok ?_
  rw [stepFE_dispatch h_run h_np h_dec h_cap h_gas]
  simp only [stepF.stackMemFlow]
  rfl

/-- Completeness for `StepRunning.log`. -/
theorem complete_log (s : State) (n : Fin 5) (offset size : UInt256)
        (topics : List UInt256) (rest : List UInt256)
        (h_op       : s.decodedOp = some (.Log ⟨n⟩))
        (h_perm     : s.executionEnv.permitStateMutation = true)
        (h_topics_n : topics.length = n.val)
        (h_stack    : s.stack = offset :: size :: topics ++ rest)
        (h_gas      : Gas.logTotal s n offset size ≤ s.gasAvailable)
        (h_cap   : s.stack.length + Operation.pushArity (.Log ⟨n⟩)
                     ≤ 1024 + Operation.popArity (.Log ⟨n⟩))
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.logTotal s n offset size
              activeWords  := s.activeWordsAfterUInt256 offset.toNat size.toNat
              substate     := s.substate.appendLog
                                { address := s.executionEnv.address
                                  topics  := topics.toArray
                                  data    := MachineState.readPadded s.memory
                                               offset.toNat size.toNat } }
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  have hL : Gas.logTotal s n offset size
      = Gas.baseCost s.fork (.Log ⟨n⟩)
        + MachineState.memExpansionDelta s.activeWords.toNat offset.toNat size.toNat
        + Gas.logDataCost size := rfl
  have h_base : Gas.baseCost s.fork (.Log ⟨n⟩) ≤ s.gasAvailable := by
    rw [hL] at h_gas; omega
  refine stepF_eq_ok ?_
  rw [stepFE_dispatch h_run h_np h_dec h_cap h_base]
  simp only [stepF.log, h_perm, not_true, if_false, h_stack, List.cons_append]
  have h_mem : (s.consumeGas (Gas.baseCost s.fork (.Log ⟨n⟩)) h_base).canExpandMemory
                 offset.toNat size.toNat := by
    simp only [State.canExpandMemory, State.consumeGas]
    rw [hL] at h_gas; omega
  simp only [chargeMem, dif_pos h_mem]
  have h_dyn : Gas.logDataCost size ≤
      ((s.consumeGas (Gas.baseCost s.fork (.Log ⟨n⟩)) h_base).consumeMemExp
        offset.toNat size.toNat h_mem).gasAvailable := by
    simp only [State.consumeMemExp, State.consumeGas]
    rw [hL] at h_gas
    simp only [MachineState.memExpansionDelta] at h_gas h_mem ⊢
    omega
  simp only [dif_pos h_dyn]
  rw [← h_topics_n, popN_append]
  simp only [State.consumeGas, State.consumeMemExp, State.replaceStackAndIncrPC,
    State.activeWordsAfterUInt256, Gas.logTotal, UInt256.succ,
    MachineState.memExpansionDelta,
    show ∀ (a b : UInt256), a + b = a.add b from fun _ _ => rfl]
  grind

/-- Completeness for `StepRunning.dupN`. -/
theorem complete_dupN (s : State) (n : Fin 256) (v : UInt256)
        (h_op      : s.decodedOp = some (.DupN ⟨n⟩))
        (h_gas     : Gas.baseCost s.fork (.DupN ⟨n⟩) ≤ s.gasAvailable)
        (h_get     : s.stack[n.val]? = some v)
        (h_cap     : s.stack.length < 1024)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := v :: s.stack
              pc           := s.pc + UInt256.ofNat 2
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork (.DupN ⟨n⟩) }
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  refine stepF_eq_ok ?_
  rw [stepFE_dispatch h_run h_np h_dec
        (by simp only [Operation.pushArity, Operation.popArity]; omega) h_gas]
  simp only [stepF.dupN, h_get]
  rfl

/-- Completeness for `StepRunning.swapN`. -/
theorem complete_swapN (s : State) (n : Fin 256) (stk' : List UInt256)
        (h_op      : s.decodedOp = some (.SwapN ⟨n⟩))
        (h_gas     : Gas.baseCost s.fork (.SwapN ⟨n⟩) ≤ s.gasAvailable)
        (h_swap    : s.stack.exchange 0 (n.val + 1) = some stk')
        (h_cap   : s.stack.length + Operation.pushArity (.SwapN ⟨n⟩)
                     ≤ 1024 + Operation.popArity (.SwapN ⟨n⟩))
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := stk'
              pc           := s.pc + UInt256.ofNat 2
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork (.SwapN ⟨n⟩) }
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  refine stepF_eq_ok ?_
  rw [stepFE_dispatch h_run h_np h_dec h_cap h_gas]
  simp only [stepF.swapN, h_swap]
  rfl

/-- Completeness for `StepRunning.exchange`. -/
theorem complete_exchange (s : State) (b : Fin 256) (stk' : List UInt256)
        (h_op      : s.decodedOp = some (.Exchange ⟨b⟩))
        (h_gas     : Gas.baseCost s.fork (.Exchange ⟨b⟩) ≤ s.gasAvailable)
        (h_swap    : s.stack.exchange
                      (b.val >>> 4 + 1)
                      ((b.val &&& 0xf) + 1) = some stk')
        (h_cap   : s.stack.length + Operation.pushArity (.Exchange ⟨b⟩)
                     ≤ 1024 + Operation.popArity (.Exchange ⟨b⟩))
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := stk'
              pc           := s.pc + UInt256.ofNat 2
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork (.Exchange ⟨b⟩) }
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  refine stepF_eq_ok ?_
  rw [stepFE_dispatch h_run h_np h_dec h_cap h_gas]
  simp only [stepF.exchange, Operation.ExchangeOp.n, Operation.ExchangeOp.m, h_swap]
  rfl

end StepComplete
end EVM
end EvmSemantics
