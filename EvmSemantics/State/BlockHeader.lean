module

public import EvmSemantics.Data.UInt256
public import EvmSemantics.State.Account

/-!
A minimal `BlockHeader` carrying only the fields the step relation
reads (COINBASE / TIMESTAMP / NUMBER / PREVRANDAO / GASLIMIT / BASEFEE /
CHAINID-via-state).
-/

@[expose] public section

namespace EvmSemantics

/-- Block header `H` — only the fields the step relation reads. -/
structure BlockHeader where
  /-- `H_c` — beneficiary (miner) address. -/
  coinbase     : AccountAddress
  /-- `H_s` — block timestamp (seconds since epoch). -/
  timestamp    : UInt256
  /-- `H_i` — block number. -/
  number       : UInt256
  /-- `H_a` — `PREVRANDAO` mix (post-Merge replacement for difficulty). -/
  prevRandao   : UInt256
  /-- `H_l` — block gas limit. -/
  gasLimit     : UInt256
  /-- `H_f` — EIP-1559 base fee per gas. -/
  baseFeePerGas : UInt256
  /-- Chain ID (EIP-155). -/
  chainId      : UInt256
  /-- Used by `BLOCKHASH`. For unknown block numbers the implementation
      should return 0; we abstract over the lookup so the relation can
      stay independent of how block hashes are stored. -/
  blockHash    : UInt256 → UInt256
  /-- EIP-7516 base fee per blob gas. Used by `BLOBBASEFEE`. -/
  blobBaseFee  : UInt256
  deriving Inhabited

end EvmSemantics
