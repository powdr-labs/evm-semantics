module

/-!
`ExecutionException` — the eight halt-with-error conditions used by the
EVM step relation. Mirrors `EvmYul.EVM.Exception.ExecutionException`.
-/

@[expose] public section

namespace EvmSemantics

inductive ExecutionException where
  | OutOfFuel
  | InvalidInstruction
  | OutOfGas
  | BadJumpDestination
  | StackOverflow
  | StackUnderflow
  | InvalidMemoryAccess
  | StaticModeViolation
  deriving BEq, DecidableEq, Repr, Inhabited

end EvmSemantics
