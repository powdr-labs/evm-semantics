module

public import EvmSemantics.State.Account
public import EvmSemantics.State.Substate
public import EvmSemantics.State.ExecutionEnv
public import EvmSemantics.Machine.MachineState

/-!
`SharedState` — the world state (`AccountMap` + accrued `Substate` +
`ExecutionEnv` + `BlockHeader`) bundled with the per-frame `MachineState`.

This is the "everything except the EVM-specific pc + stack" record.
-/

@[expose] public section

namespace EvmSemantics

structure SharedState extends MachineState where
  accountMap   : AccountMap
  substate     : Substate
  executionEnv : ExecutionEnv
  deriving Inhabited

end EvmSemantics
