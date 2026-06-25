module

public import EvmSemantics.Data.UInt256
public import EvmSemantics.State.Account

/-!
A minimal `BlockHeader` carrying only the fields the v1 step relation
reads (COINBASE / TIMESTAMP / NUMBER / PREVRANDAO / GASLIMIT / BASEFEE /
CHAINID-via-state).
-/

@[expose] public section

namespace EvmSemantics

structure BlockHeader where
  coinbase     : AccountAddress
  timestamp    : UInt256
  number       : UInt256
  prevRandao   : UInt256
  gasLimit     : UInt256
  baseFeePerGas : UInt256
  chainId      : UInt256
  /-- Used by `BLOCKHASH`. For unknown block numbers the implementation
      should return 0; we abstract over the lookup so the relation can
      stay independent of how block hashes are stored. -/
  blockHash    : UInt256 → UInt256
  /-- EIP-7516 base fee per blob gas. Used by `BLOBBASEFEE`. -/
  blobBaseFee  : UInt256
  deriving Inhabited

end EvmSemantics
