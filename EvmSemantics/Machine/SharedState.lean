import EvmSemantics.State.Account
import EvmSemantics.State.Substate
import EvmSemantics.State.ExecutionEnv
import EvmSemantics.Machine.MachineState

/-!
`SharedState` — the world state (`AccountMap` + accrued `Substate` +
`ExecutionEnv` + `BlockHeader`) bundled with the per-frame `MachineState`.

This is the "everything except the EVM-specific pc + stack" record.
-/

namespace EvmSemantics

structure SharedState extends MachineState where
  accountMap   : AccountMap
  substate     : Substate
  executionEnv : ExecutionEnv
  deriving Inhabited

end EvmSemantics
