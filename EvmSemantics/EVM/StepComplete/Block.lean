module

public import EvmSemantics.EVM.StepComplete.Dispatch

/-!
`StepComplete.Block` — completeness cases for the Block constructors of
`StepRunning`: each constructor's premises force `stepF` to compute
exactly that constructor's successor. Assembled into
`stepRunning_complete` in `StepDeterminism.lean`.
-/

@[expose] public section

namespace EvmSemantics
namespace EVM
namespace StepComplete

/-- Completeness for `StepRunning.blockhash`. -/
theorem complete_blockhash (s : State) (n : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .BLOCKHASH)
        (h_gas     : Gas.baseCost s.fork .BLOCKHASH ≤ s.gasAvailable)
        (h_stack   : s.stack = n :: rest)
        (h_cap   : s.stack.length + Operation.pushArity .BLOCKHASH
                     ≤ 1024 + Operation.popArity .BLOCKHASH)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := s.executionEnv.header.blockHash n :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .BLOCKHASH }
    := by
  sorry

/-- Completeness for `StepRunning.coinbase`. -/
theorem complete_coinbase (s : State)
        (h_op      : s.decodedOp = some .COINBASE)
        (h_gas     : Gas.baseCost s.fork .COINBASE ≤ s.gasAvailable)
        (h_cap     : s.stack.length < 1024)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := s.executionEnv.header.coinbase.toUInt256 :: s.stack
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .COINBASE }
    := by
  sorry

/-- Completeness for `StepRunning.timestamp`. -/
theorem complete_timestamp (s : State)
        (h_op      : s.decodedOp = some .TIMESTAMP)
        (h_gas     : Gas.baseCost s.fork .TIMESTAMP ≤ s.gasAvailable)
        (h_cap     : s.stack.length < 1024)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := s.executionEnv.header.timestamp :: s.stack
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .TIMESTAMP }
    := by
  sorry

/-- Completeness for `StepRunning.number`. -/
theorem complete_number (s : State)
        (h_op      : s.decodedOp = some .NUMBER)
        (h_gas     : Gas.baseCost s.fork .NUMBER ≤ s.gasAvailable)
        (h_cap     : s.stack.length < 1024)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := s.executionEnv.header.number :: s.stack
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .NUMBER }
    := by
  sorry

/-- Completeness for `StepRunning.prevrandao`. -/
theorem complete_prevrandao (s : State)
        (h_op      : s.decodedOp = some .PREVRANDAO)
        (h_gas     : Gas.baseCost s.fork .PREVRANDAO ≤ s.gasAvailable)
        (h_cap     : s.stack.length < 1024)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := s.executionEnv.header.prevRandao :: s.stack
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .PREVRANDAO }
    := by
  sorry

/-- Completeness for `StepRunning.gaslimit`. -/
theorem complete_gaslimit (s : State)
        (h_op      : s.decodedOp = some .GASLIMIT)
        (h_gas     : Gas.baseCost s.fork .GASLIMIT ≤ s.gasAvailable)
        (h_cap     : s.stack.length < 1024)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := s.executionEnv.header.gasLimit :: s.stack
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .GASLIMIT }
    := by
  sorry

/-- Completeness for `StepRunning.chainid`. -/
theorem complete_chainid (s : State)
        (h_op      : s.decodedOp = some .CHAINID)
        (h_gas     : Gas.baseCost s.fork .CHAINID ≤ s.gasAvailable)
        (h_cap     : s.stack.length < 1024)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := s.executionEnv.header.chainId :: s.stack
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .CHAINID }
    := by
  sorry

/-- Completeness for `StepRunning.selfbalance`. -/
theorem complete_selfbalance (s : State)
        (h_op      : s.decodedOp = some .SELFBALANCE)
        (h_gas     : Gas.baseCost s.fork .SELFBALANCE ≤ s.gasAvailable)
        (h_cap     : s.stack.length < 1024)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := (s.accountMap s.executionEnv.address).balance :: s.stack
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .SELFBALANCE }
    := by
  sorry

/-- Completeness for `StepRunning.basefee`. -/
theorem complete_basefee (s : State)
        (h_op      : s.decodedOp = some .BASEFEE)
        (h_gas     : Gas.baseCost s.fork .BASEFEE ≤ s.gasAvailable)
        (h_cap     : s.stack.length < 1024)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := s.executionEnv.header.baseFeePerGas :: s.stack
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .BASEFEE }
    := by
  sorry

/-- Completeness for `StepRunning.blobhash`. -/
theorem complete_blobhash (s : State) (i : UInt256) (rest : List UInt256) (h : UInt256)
        (h_op      : s.decodedOp = some .BLOBHASH)
        (h_gas     : Gas.baseCost s.fork .BLOBHASH ≤ s.gasAvailable)
        (h_stack   : s.stack = i :: rest)
        (h_get     : s.executionEnv.blobVersionedHashes[i.toNat]? = some h)
        (h_cap   : s.stack.length + Operation.pushArity .BLOBHASH
                     ≤ 1024 + Operation.popArity .BLOBHASH)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := h :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .BLOBHASH }
    := by
  sorry

/-- Completeness for `StepRunning.blobhash_oob`. -/
theorem complete_blobhash_oob (s : State) (i : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .BLOBHASH)
        (h_gas     : Gas.baseCost s.fork .BLOBHASH ≤ s.gasAvailable)
        (h_stack   : s.stack = i :: rest)
        (h_oob     : s.executionEnv.blobVersionedHashes[i.toNat]? = none)
        (h_cap   : s.stack.length + Operation.pushArity .BLOBHASH
                     ≤ 1024 + Operation.popArity .BLOBHASH)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := ⟨0⟩ :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .BLOBHASH }
    := by
  sorry

/-- Completeness for `StepRunning.blobbasefee`. -/
theorem complete_blobbasefee (s : State)
        (h_op      : s.decodedOp = some .BLOBBASEFEE)
        (h_gas     : Gas.baseCost s.fork .BLOBBASEFEE ≤ s.gasAvailable)
        (h_cap     : s.stack.length < 1024)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s =
          { s with
              stack        := s.executionEnv.header.blobBaseFee :: s.stack
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .BLOBBASEFEE }
    := by
  sorry

end StepComplete
end EVM
end EvmSemantics
