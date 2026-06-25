module

public import EvmSemantics.Data.UInt256
public import EvmSemantics.State.Account
public import EvmSemantics.State.BlockHeader

/-!
`ExecutionEnv` — the per-frame execution environment `I` from the Yellow
Paper. For v1 (no calls) this is fixed once at the start of a run.
-/

@[expose] public section

namespace EvmSemantics

/-- Per-frame execution environment `I` (Yellow Paper §9.3). -/
structure ExecutionEnv where
  /-- `Iₐ` — the address of the contract currently being executed. -/
  codeOwner : AccountAddress
  /-- `Iₒ` — the original transaction sender (transaction `from`). -/
  sender    : AccountAddress
  /-- `Iₛ` — the immediate caller of this frame (for v1 = `sender`). -/
  source    : AccountAddress
  /-- `Iᵥ` — the value transferred (wei) into this frame. -/
  weiValue  : UInt256
  /-- `I_d` — the input calldata. -/
  calldata  : ByteArray
  /-- `I_b` — the bytecode being executed. -/
  code      : ByteArray
  /-- `Iₚ` — the gas price of the originating transaction. -/
  gasPrice  : UInt256
  /-- `I_H` — the block header in which this execution occurs. -/
  header    : BlockHeader
  /-- `Iₑ` — the call-stack depth. Always 0 in v1. -/
  depth     : Nat
  /-- `I_w` — whether state-mutating ops are permitted (false ⇒ static). -/
  permitStateMutation : Bool
  /-- EIP-4844 versioned-hash list. Read by `BLOBHASH`. -/
  blobVersionedHashes : Array UInt256
  deriving Inhabited

end EvmSemantics
