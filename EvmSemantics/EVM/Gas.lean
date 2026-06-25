module

public import EvmSemantics.EVM.Operation

/-!
`Gas` — fixed (static) gas-cost function for each EVM opcode.

The cost returned here is the **static** Yellow-Paper fee for the
operation: the base fee for opcodes whose Yellow-Paper cost has a
dynamic component (memory expansion, per-word copy cost, per-byte LOG
cost, topic count) returns only the base. Memory expansion is charged
separately by `stepF.chargeMem` / `chargeMem2`; per-word and per-byte
dynamic costs are not yet modelled.

Reference constants from the Yellow Paper Appendix G ("Fee Schedule"):

| Symbol         | Value | Opcodes                                                   |
| -------------- | -----:| --------------------------------------------------------- |
| `G_zero`       |     0 | STOP, RETURN, REVERT                                      |
| `G_jumpdest`   |     1 | JUMPDEST                                                  |
| `G_base`       |     2 | environment / block reads, POP, PC, MSIZE, GAS, …         |
| `G_verylow`    |     3 | ADD/SUB, comparisons, bitwise, MLOAD/MSTORE/MSTORE8, …    |
| `G_low`        |     5 | MUL/DIV/MOD/SDIV/SMOD, SIGNEXTEND, SELFBALANCE            |
| `G_mid`        |     8 | ADDMOD/MULMOD, JUMP                                       |
| `G_high`       |    10 | JUMPI, EXP (base; per-byte part omitted)                  |
| `G_keccak256`  |    30 | KECCAK256 (base; per-word part omitted)                   |
| `G_warmaccess` |   100 | BALANCE / EXT* / SLOAD (warm — we don't model cold/warm)  |
| `G_log`        |   375 | LOG`n` base + `n·G_log` (per-topic) — per-byte omitted    |
| `G_blockhash`  |    20 | BLOCKHASH                                                 |

Out-of-scope opcodes (CREATE family, CALL family, SELFDESTRUCT) are
mapped to the Yellow-Paper base of their static portion as a
forward-compatibility convenience; v1's evaluator rejects them as
`InvalidInstruction` before the cost is even consulted.
-/

@[expose] public section

namespace EvmSemantics
namespace EVM

/-!
### Opcodes priced at `1` here pending dynamic-cost support

Several opcodes' real-EVM gas cost is **not** a fixed constant — they are
priced as cost = 1 below, each tagged with a `TODO(dynamic)` comment:

* **SLOAD, BALANCE, EXTCODESIZE, EXTCODEHASH, EXTCODECOPY** — EIP-2929
  cold/warm split (2600/2100 vs 100). Needs access-list tracking in
  `Substate` to model honestly.
* **SSTORE** — EIP-2200 + EIP-3529: cost depends on the triple
  (original, current, new) × cold/warm. Anywhere from 100 (no-op warm)
  to 22100+ (creating a slot cold), plus refunds.
* **CALL, CALLCODE, DELEGATECALL, STATICCALL** — cold/warm + value-
  transfer surcharge + new-account surcharge + 63/64 forwarding.
* **CREATE, CREATE2** — 32000 base plus dynamic init-code (EIP-3860)
  and per-word memory; out-of-scope opcodes in v1.
* **SELFDESTRUCT** — 5000 base + 25000 new-account + 2600/100 beneficiary
  access cost.

All `Log`/`Keccak`/copy ops keep the *base* fee; their per-word /
per-byte / per-topic dynamic parts are not yet modelled either, but
those at least have an unambiguous static portion worth charging.
-/

/-- Static (base) gas cost of executing one instance of `op`. -/
def Gas.cost : Operation → Nat
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
    -- TODO(dynamic): EIP-2929 cold/warm 2600/100. Priced at 1 for now.
    | .BALANCE | .EXTCODESIZE | .EXTCODEHASH | .EXTCODECOPY  => 1
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
    -- TODO(dynamic): SLOAD is EIP-2929 cold/warm; SSTORE is EIP-2200/3529
    -- (depends on original/current/new value triple). Priced at 1 for now.
    -- TLOAD/TSTORE are genuinely fixed at 100 per EIP-1153.
    | .SLOAD | .SSTORE                                       => 1
    | .TLOAD | .TSTORE                                       => 100
  | .Push p                          => if p.width.val = 0 then 2 else 3
  | .Dup _ | .Swap _                                         => 3
  | .DupN _ | .SwapN _ | .Exchange _                         => 3
  | .Log l                                  => 375 * (l.topics.val + 1)
  | .System op => match op with
    | .RETURN | .REVERT | .INVALID                           => 0
    -- TODO(dynamic): CREATE/CREATE2 32000+initcode/word+memory;
    -- CALL family cold/warm+value+new-account+forwarding; SELFDESTRUCT
    -- 5000+new-account+cold/warm. All priced at 1 for now.
    | .CREATE | .CREATE2                                     => 1
    | .CALL | .CALLCODE | .DELEGATECALL | .STATICCALL        => 1
    | .SELFDESTRUCT                                          => 1

end EVM
end EvmSemantics
