module

public import EvmSemantics.Data.UInt256
public import EvmSemantics.State.Account
public import EvmSemantics.State.BlockHeader
public import EvmSemantics.State.ExecutionEnv
public import EvmSemantics.State.Substate
public import EvmSemantics.Machine.MachineState
public import EvmSemantics.Machine.SharedState
public import EvmSemantics.EVM.Exception
public import EvmSemantics.EVM.State
public import EvmSemantics.EVM.Operation
public import EvmSemantics.EVM.Halted
public import EvmSemantics.EVM.Decode
public import EvmSemantics.EVM.Gas
public import EvmSemantics.EVM.Step
public import EvmSemantics.EVM.BigStep
public import EvmSemantics.EVM.StepF
public import EvmSemantics.EVM.Equiv
public import EvmSemantics.Tx
public import EvmSemantics.Crypto.Keccak256
public import EvmSemantics.Data.Mpt

/-!
`EvmSemantics` — a relational small-step / big-step semantics of the
Ethereum Virtual Machine in Lean 4. Modelled on
https://github.com/NethermindEth/EVMYulLean but expressed as `Prop`-valued
inductive relations rather than executable functions.

This module re-exports the entry points. Start at `EvmSemantics.EVM.Step`
(the small-step relation) and `EvmSemantics.EVM.BigStep` (the big-step
relation).
-/
