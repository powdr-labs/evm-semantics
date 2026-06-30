module

public import EvmSemantics.Data.UInt256
public import EvmSemantics.State.Account
public import EvmSemantics.State.BlockHeader
public import EvmSemantics.EVM.Fork

/-!
`ExecutionEnv` — the per-frame execution environment `I` from the Yellow
Paper. Fixed at frame entry and threaded through the small-step
relation; a CALL/CREATE pushes a new `ExecutionEnv` for the callee.
-/

@[expose] public section

namespace EvmSemantics

/-- Per-frame execution environment `I` (Yellow Paper §9.3). -/
structure ExecutionEnv where
  /-- `Iₐ` — the executing account's address (what `ADDRESS` returns).
      For `CALL`/`STATICCALL` this is the call target; for `CALLCODE`/
      `DELEGATECALL` the parent frame's `address` is preserved (the
      "self" identity stays with the caller even though the code is
      borrowed). Also the storage / transient-storage / `SELFBALANCE`
      context. -/
  address   : AccountAddress
  /-- `Iₒ` — the original transaction sender (the EOA that signed the
      tx; what the `ORIGIN` opcode returns). -/
  origin    : AccountAddress
  /-- `Iₛ` — the immediate caller of this frame (what the `CALLER`
      opcode returns). At depth 0 this equals `origin`; for nested
      frames it's the parent frame's `address`. -/
  caller    : AccountAddress
  /-- `Iᵥ` — the value transferred (wei) into this frame. -/
  weiValue  : UInt256
  /-- `I_d` — the input calldata. -/
  calldata  : ByteArray
  /-- `I_b` — the bytecode being executed. -/
  code      : ByteArray
  /-- The address whose bytecode `code` was read from — i.e. the
      target of the surrounding `CALL`/`CALLCODE`/`DELEGATECALL`/
      `STATICCALL`. For `CALL`/`STATICCALL` this equals `address`; for
      `CALLCODE`/`DELEGATECALL` it differs from `address` (those two
      borrow code from `codeAddr` but keep the caller's `address`).
      Used by the precompile dispatch (YP §9): a frame whose `codeAddr`
      lies in `0x01..0x09` runs the corresponding native operation in
      place of `code`. Not in the Yellow Paper's `I` tuple — added here
      because we need a stable per-frame handle on the borrowed-from
      address to key the precompile-vs-bytecode decision off of. -/
  codeAddr  : AccountAddress
  /-- `Iₚ` — the gas price of the originating transaction. -/
  gasPrice  : UInt256
  /-- `I_H` — the block header in which this execution occurs. -/
  header    : BlockHeader
  /-- `Iₑ` — the call-stack depth. -/
  depth     : Nat
  /-- `I_w` — whether state-mutating ops are permitted (false ⇒ static). -/
  permitStateMutation : Bool
  /-- EIP-4844 versioned-hash list. Read by `BLOBHASH`. -/
  blobVersionedHashes : Array UInt256
  /-- EVM hard-fork version against which gas costs and any
      fork-conditional semantics are computed. -/
  fork                : Fork
  deriving Inhabited

end EvmSemantics
