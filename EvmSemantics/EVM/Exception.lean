/-!
`ExecutionException` — the eight halt-with-error conditions used by the
EVM step relation. Mirrors `EvmYul.EVM.Exception.ExecutionException`.
-/

namespace EvmSemantics

/-- The eight ways an EVM frame can halt with an error. -/
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
