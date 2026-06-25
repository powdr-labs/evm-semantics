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

/-- World state (account map + accrued substate + execution environment)
    bundled with the per-frame machine state. -/
structure SharedState extends MachineState where
  /-- `σ` — global address → account mapping. -/
  accountMap   : AccountMap
  /-- `A` — accrued transaction-level substate (logs, accesses, refunds). -/
  substate     : Substate
  /-- `I` — execution environment of the current frame. -/
  executionEnv : ExecutionEnv
  deriving Inhabited

end EvmSemantics
