module

public import EvmSemantics.EVM.Operation
public import EvmSemantics.EVM.Fork
public import EvmSemantics.Data.UInt256

/-!
`Gas` — gas-cost functions, parameterised by the EVM hard fork
(`EvmSemantics.Fork`).

* `Gas.baseCost fork op` — the *static* per-opcode fee. For opcodes whose
  real cost has a dynamic component (memory expansion, per-word/byte/topic,
  EIP-2929 cold/warm, value-dependent SSTORE) this returns only the base;
  memory expansion is charged separately by `stepF.chargeMem`, and the
  SSTORE dynamic delta by `Gas.sstoreCost`.
* `Gas.sstoreCost fork original current new` — the SSTORE dynamic cost,
  separated from `baseCost` because it depends on the storage state.

The two supported forks (`Constantinople` and `Cancun`) mostly share their
fixed fees; the differences (cold/warm-priced reads, modern SSTORE rules)
are captured by branching on the `fork` argument. Cold/warm is not yet
tracked in the substate, so the `Cancun` schedule uses **warm** prices
throughout (which is a lower bound on the real cost).

Reference Yellow-Paper constants:

| Symbol         | Value | Used by                                                  |
| -------------- | -----:| -------------------------------------------------------- |
| `G_zero`       |     0 | STOP, RETURN, REVERT, INVALID                            |
| `G_jumpdest`   |     1 | JUMPDEST                                                 |
| `G_base`       |     2 | environment / block reads, POP, PC, MSIZE, GAS, …        |
| `G_verylow`    |     3 | ADD/SUB, comparisons, bitwise, MLOAD/MSTORE/MSTORE8, …   |
| `G_low`        |     5 | MUL/DIV/MOD/SDIV/SMOD, SIGNEXTEND, SELFBALANCE           |
| `G_mid`        |     8 | ADDMOD/MULMOD, JUMP                                      |
| `G_high`       |    10 | JUMPI, EXP (base)                                        |
| `G_keccak256`  |    30 | KECCAK256 (base; per-word part omitted)                  |
| `G_warmaccess` |   100 | warm-priced reads (Cancun)                               |
| `G_log`        |   375 | LOG`n` base + `n·G_log` (per-topic)                      |
| `G_blockhash`  |    20 | BLOCKHASH                                                |
-/

@[expose] public section

namespace EvmSemantics
namespace EVM

/-- Static (base) gas cost of executing one instance of `op` under `fork`. -/
def Gas.baseCost (fork : Fork) : Operation → Nat
  | .StopArith op => match op with
    | .STOP                                                  => 0
    | .ADD | .SUB                                            => 3
    | .MUL | .DIV | .SDIV | .MOD | .SMOD | .SIGNEXTEND       => 5
    | .ADDMOD | .MULMOD                                      => 8
    | .EXP                                                   => 10
  | .CompBit _                                               => 3
  | .Keccak _                                                => 30
  | .Env op => match op with
    | .ADDRESS | .ORIGIN | .CALLER | .CALLVALUE
    | .CALLDATASIZE | .CODESIZE | .GASPRICE | .RETURNDATASIZE => 2
    | .CALLDATALOAD                                          => 3
    | .CALLDATACOPY | .CODECOPY | .RETURNDATACOPY            => 3
    -- BALANCE / EXTCODESIZE / EXTCODEHASH / EXTCODECOPY:
    -- pre-EIP-2929 (Constantinople) used flat 400 / 700 / 700 / 700 — we
    -- use `1` as a placeholder since none of these are gas-comparable yet.
    -- Post-EIP-2929 (Cancun) is cold 2600 / warm 100 — we use warm.
    | .BALANCE | .EXTCODESIZE | .EXTCODEHASH | .EXTCODECOPY  =>
      match fork with
      | .Constantinople => 1
      | .Cancun         => 100
  | .Block op => match op with
    | .COINBASE | .TIMESTAMP | .NUMBER | .PREVRANDAO
    | .GASLIMIT | .CHAINID | .BASEFEE | .BLOBBASEFEE         => 2
    | .SELFBALANCE                                           => 5
    | .BLOCKHASH                                             => 20
    | .BLOBHASH                                              => 3
  | .StackMemFlow op => match op with
    | .POP | .PC | .MSIZE | .GAS                             => 2
    | .JUMPDEST                                              => 1
    | .MLOAD | .MSTORE | .MSTORE8 | .MCOPY                   => 3
    | .JUMP                                                  => 8
    | .JUMPI                                                 => 10
    -- SLOAD:
    -- Constantinople: 50 (matches the legacy ethereum/tests corpus, which
    -- actually uses the Frontier value rather than Tangerine-Whistle 200).
    -- Cancun warm-access: 100 (EIP-2929). Cold (2100) not yet modelled.
    | .SLOAD                                                 =>
      match fork with
      | .Constantinople => 50
      | .Cancun         => 100
    -- SSTORE: dynamic — see `Gas.sstoreCost`. Static portion is 0.
    | .SSTORE                                                => 0
    | .TLOAD | .TSTORE                                       => 100
  | .Push p                          => if p.width.val = 0 then 2 else 3
  | .Dup _ | .Swap _                                         => 3
  | .DupN _ | .SwapN _ | .Exchange _                         => 3
  | .Log l                                  => 375 * (l.topics.val + 1)
  | .System op => match op with
    | .RETURN | .REVERT | .INVALID                           => 0
    -- Out-of-scope dynamic ops; `1` is a placeholder.
    | .CREATE | .CREATE2                                     => 1
    | .CALL | .CALLCODE | .DELEGATECALL | .STATICCALL        => 1
    | .SELFDESTRUCT                                          => 1

/-- Dynamic gas cost of an SSTORE under `fork`, given the slot's
    `original` value (at frame start), `current` value (just before this
    write), and the `new` value being written.

    **Constantinople** uses the pre-EIP-1283 schedule (EIP-1283 was
    scheduled for Constantinople but reverted in Petersburg, and the
    ethereum/tests legacy "Constantinople" corpus reflects the revert):

    | Condition                              | Cost  |
    |----------------------------------------|------:|
    | `current = 0 ∧ new ≠ 0` (fresh set)    | 20000 |
    | otherwise (reset, clear, no-op)        |  5000 |

    **Cancun** uses EIP-2200 net-metered semantics (without the EIP-2929
    cold/warm bit, which we don't yet model — Cancun's cold surcharge
    would add 2100 to the first SSTORE of a transaction):

    | Condition                                          | Cost  |
    |----------------------------------------------------|------:|
    | `current = new` (no-op)                            |   100 |
    | `current = original ∧ original = 0` (fresh set)    | 20000 |
    | `current = original ∧ original ≠ 0` (clean reset)  |  2900 |
    | otherwise (`current ≠ original`, "dirty")          |   100 |

    Refunds are tracked separately in `Substate.refundBalance` (not yet
    populated). -/
def Gas.sstoreCost (fork : Fork) (original current new : UInt256) : Nat :=
  match fork with
  | .Constantinople =>
    if current.toNat = 0 ∧ new.toNat ≠ 0 then 20000 else 5000
  | .Cancun =>
    if current.toNat = new.toNat then 100
    else if current.toNat = original.toNat then
      if original.toNat = 0 then 20000 else 2900
    else 100

/-- Per-word copy cost (Yellow Paper `G_copy = 3`): `3 · ⌈size/32⌉`.
    Used by CALLDATACOPY, CODECOPY, RETURNDATACOPY, MCOPY, EXTCODECOPY,
    and as the per-word part of `KECCAK256` (with `6` instead of `3`). -/
def Gas.copyWordCost (size : UInt256) : Nat :=
  3 * ((size.toNat + 31) / 32)

/-- Per-byte LOG data cost (Yellow Paper `G_logdata = 8`): `8 · size`. -/
def Gas.logDataCost (size : UInt256) : Nat :=
  8 * size.toNat

/-- Per-byte EXP cost: `50 · byteLen(exponent)` post-Spurious-Dragon
    (EIP-160). Both `Constantinople` and `Cancun` use the 50-per-byte
    schedule. `byteLen(0) = 0`. -/
def Gas.expByteCost (exponent : UInt256) : Nat :=
  if exponent.toNat = 0 then 0
  else 50 * (Nat.log2 exponent.toNat / 8 + 1)

end EVM
end EvmSemantics
