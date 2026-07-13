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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

end StepComplete
end EVM
end EvmSemantics
