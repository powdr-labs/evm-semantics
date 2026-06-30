module

public import EvmSemantics.Data.UInt256
public import EvmSemantics.State.Account

/-!
`EvmSemantics.EVM.Precompile` — the YP §9 precompiled contracts at
addresses `0x01..0x09`.

When a CALL-family opcode targets one of these addresses, the EVM does
*not* execute bytecode (there is no code stored at the address);
instead, it invokes the corresponding native operation. From the
caller's view, the call returns either successfully (with an output
byte string and a known gas cost) or out-of-gas (no output, all
forwarded gas consumed).

`Precompile.run` is the dispatch entry point. It returns:

* `.notAPrecompile` — the target isn't a precompile; the caller falls
  through to the normal `enterCall` / frame-push path.
* `.success output gasUsed` — the precompile ran; `output` is the
  return bytes (to be written to the caller's `retOff:retLen` window
  by the resume machinery) and `gasUsed ≤ childGas`.
* `.outOfGas` — the precompile would have run but its gas requirement
  exceeded `childGas`; the entire `childGas` is forfeited, no output.

Extending with a new precompile is a two-step edit:

1. Add a `runFoo : ByteArray → Nat → Result` implementing the
   operation's behaviour and gas cost.
2. Add the address → handler entry to the dispatch table in `run`.

This file currently implements only `0x04 IDENTITY`; the dispatch
table has explicit fall-through cases ready for the rest.
-/

@[expose] public section

namespace EvmSemantics
namespace EVM
namespace Precompile

/-- Outcome of a precompile dispatch attempt. See module docstring. -/
inductive Result where
  /-- The target address is not assigned to any precompile in the
      currently modelled set. Callers should fall through to the
      normal `enterCall` code path. -/
  | notAPrecompile
  /-- The precompile ran successfully. `output` is the return bytes;
      `gasUsed ≤ childGas` is the amount consumed (the caller refunds
      `childGas - gasUsed` to itself). -/
  | success (output : ByteArray) (gasUsed : Nat)
  /-- The precompile's gas requirement exceeded `childGas`. The
      CALL-family op behaves like an exceptional callee halt: push
      `0`, empty `returnData`, lose the entire `childGas`, value
      transfer (if any) is rolled back via the resume-time snapshot. -/
  | outOfGas
  deriving Inhabited

/-- True iff `addr` is one of the YP §9 precompile addresses
    (`0x01..0x09`). Used as the gating predicate by `run` and by the
    no-precompile branch of the existing `StepRunning.call` rules
    (so a non-precompile target falls through). -/
def isPrecompile (addr : AccountAddress) : Bool :=
  let n := addr.toUInt256.toNat
  decide (1 ≤ n ∧ n ≤ 9)

----------------------------------------------------------------------------
-- 0x04 IDENTITY — return calldata unchanged.
----------------------------------------------------------------------------

/-- The IDENTITY precompile's address `0x04`. -/
def identityAddress : AccountAddress :=
  AccountAddress.ofUInt256 (UInt256.ofNat 4)

/-- IDENTITY gas (YP §9.4.4): `G_identity + G_identityword · ⌈|input|/32⌉
    = 15 + 3 · ⌈|input|/32⌉`. -/
@[inline] def identityGas (input : ByteArray) : Nat :=
  15 + 3 * ((input.size + 31) / 32)

/-- Run the `0x04 IDENTITY` precompile: returns `input` unchanged,
    consuming `identityGas input` gas. -/
def runIdentity (input : ByteArray) (childGas : Nat) : Result :=
  let cost := identityGas input
  if cost ≤ childGas then .success input cost else .outOfGas

----------------------------------------------------------------------------
-- Dispatch.
----------------------------------------------------------------------------

/-- Dispatch `addr` to the corresponding precompile. Returns
    `.notAPrecompile` for any address not yet implemented (including
    the precompile range `0x01..0x09` minus the entries below). Add
    new precompiles as further arms here. -/
def run (addr : AccountAddress) (input : ByteArray) (childGas : Nat) : Result :=
  if addr = identityAddress then runIdentity input childGas
  -- 0x01 ECRECOVER, 0x02 SHA256, 0x03 RIPEMD160, 0x05 MODEXP,
  -- 0x06 ECADD, 0x07 ECMUL, 0x08 ECPAIRING, 0x09 BLAKE2F — not yet
  -- implemented; fall through to `.notAPrecompile`.
  else .notAPrecompile

end Precompile
end EVM
end EvmSemantics
