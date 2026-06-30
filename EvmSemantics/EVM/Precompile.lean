module

public import EvmSemantics.Data.UInt256
public import EvmSemantics.State.Account
public import EvmSemantics.EVM.Fork

/-!
`EvmSemantics.EVM.Precompile` — the YP §9 precompiled contracts at
addresses `0x01..0x09` (and beyond, fork-dependent).

When a CALL-family opcode targets one of these addresses, the EVM does
*not* execute bytecode (there is no code stored at the address);
instead, it invokes the corresponding native operation. From the
caller's view, the call returns either successfully (with an output
byte string and a known gas cost) or out-of-gas (no output, all
forwarded gas consumed).

This module is a closed pair:

* **`isPrecompile fork addr`** — decides, per fork, whether `addr` is
  a precompile we model. The set is fork-dependent in YP terms
  (Byzantium added ECADD/ECMUL/ECPAIRING/MODEXP; Istanbul added
  BLAKE2F; Cancun added KZG point evaluation; Prague added the
  BLS12-381 set) and is the gate `Step.running` uses to decide
  bytecode-vs-precompile dispatch.

* **`run fork addr input childGas h`** — total on the subset
  `isPrecompile fork addr = true`. The proof `h` discharges
  totality: the body's branches must cover every address for which
  `isPrecompile` returns `true`, and we hold both definitions in
  lockstep. Result is either `.success output gasUsed` (with
  `gasUsed ≤ childGas`) or `.outOfGas` (precompile cost exceeded
  `childGas`). There is **no** `.notAPrecompile` arm — the precondition
  has ruled it out.

Extending with a new precompile is a synchronized three-line edit:

1. Add a `runFoo : ByteArray → Nat → Result` implementing the
   operation's behaviour and gas cost.
2. Add `addr = fooAddress` (gated by `fork.atLeast …` if the
   precompile is fork-conditional) to `isPrecompile`.
3. Add a `if addr = fooAddress then runFoo …` branch in `run`.

This file currently implements only `0x04 IDENTITY` (available from
Frontier onwards).
-/

@[expose] public section

namespace EvmSemantics
namespace EVM
namespace Precompile

/-- Outcome of a precompile invocation. -/
inductive Result where
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
-- Membership predicate + dispatch.
----------------------------------------------------------------------------

/-- True iff `addr` is one of the precompile addresses *we model* in
    `fork`. Currently: just IDENTITY (`0x04`), available since
    Frontier. As we add precompiles, this function grows in lockstep
    with `run`'s branches; `run`'s totality proof tracks that they stay
    aligned.

    The `fork` argument is part of the signature because the YP set
    is fork-dependent — ECADD/ECMUL/ECPAIRING/MODEXP from Byzantium,
    BLAKE2F from Istanbul, KZG from Cancun, BLS12-381 from Prague —
    even though the only modelled entry today (`identity`) is
    available in every fork. -/
def isPrecompile (_fork : Fork) (addr : AccountAddress) : Bool :=
  addr = identityAddress

/-- Run a precompile. Total only on the subset
    `isPrecompile fork addr = true`; the hypothesis `h` discharges
    totality by guaranteeing one of the branches below matches.

    The body's branch coverage must stay in lockstep with
    `isPrecompile` — if you add a precompile in one, add it in the
    other (and the `else` discharge will keep working). -/
def run (fork : Fork) (addr : AccountAddress)
        (input : ByteArray) (childGas : Nat)
        (h : isPrecompile fork addr = true) : Result :=
  if h_id : addr = identityAddress then
    runIdentity input childGas
  -- Add new precompiles here as further branches.
  else
    -- Unreachable: every `addr` for which `isPrecompile fork addr =
    -- true` is matched by a branch above. `absurd h …` discharges
    -- this case from `h` plus the negated branch guards.
    absurd h (by simp [isPrecompile, h_id])

end Precompile
end EVM
end EvmSemantics
