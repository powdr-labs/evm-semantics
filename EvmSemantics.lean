import EvmSemantics.Data.UInt256
import EvmSemantics.Data.Stack
import EvmSemantics.State.Account
import EvmSemantics.State.BlockHeader
import EvmSemantics.State.ExecutionEnv
import EvmSemantics.State.Substate
import EvmSemantics.Machine.MachineState
import EvmSemantics.Machine.SharedState
import EvmSemantics.EVM.Exception
import EvmSemantics.EVM.State
import EvmSemantics.EVM.Operation
import EvmSemantics.EVM.Halted
import EvmSemantics.EVM.Decode
import EvmSemantics.EVM.Gas
import EvmSemantics.EVM.Step
import EvmSemantics.EVM.BigStep
import EvmSemantics.EVM.StepF
import EvmSemantics.EVM.Equiv

/-!
`EvmSemantics` — a relational small-step / big-step semantics of the
Ethereum Virtual Machine in Lean 4. Modelled on
https://github.com/NethermindEth/EVMYulLean but expressed as `Prop`-valued
inductive relations rather than executable functions.

This module re-exports the entry points. Start at `EvmSemantics.EVM.Step`
(the small-step relation) and `EvmSemantics.EVM.BigStep` (the big-step
relation).
-/
