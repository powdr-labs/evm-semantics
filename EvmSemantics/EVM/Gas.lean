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
    -- CREATE / CREATE2 base fee (`G_create = 32000`). Per-byte deposit
    -- cost (`G_codedeposit = 200 · |deployed_code|`) is charged from the
    -- child's remaining gas at the end of init (`State.codeDepositPerByte`,
    -- applied in `State.resumeCreateSuccess`). CREATE2 *additionally* pays
    -- a keccak hash over the init code for its address derivation
    -- (`Gas.create2HashCost`), charged at this site.
    | .CREATE | .CREATE2                                     => 32000
    -- CALL family base access fee. Constantinople (EIP-150): flat 700.
    -- Cancun warm access (EIP-2929): 100 (cold 2600 not yet modelled). The
    -- value/new-account surcharge and 63/64 forwarding are computed in
    -- `stepF.system` / `StepRunning.call`, not here (cf. memory expansion for
    -- MSTORE).
    | .CALL | .CALLCODE | .DELEGATECALL | .STATICCALL        =>
      match fork with
      | .Constantinople => 700
      | .Cancun         => 100
    -- SELFDESTRUCT base fee. The legacy ethereum/tests "Constantinople"
    -- corpus uses Frontier rules (`G_selfdestruct = 0`, no `G_newaccount`
    -- surcharge) — same pattern as our Frontier-era SLOAD = 50 and
    -- Frontier-era EXP per-byte = 10 choices for the "Constantinople"
    -- fork tag. Modern post-EIP-150 schedule (5000) lives on `Cancun`.
    -- The new-account surcharge — also fork-gated — is added by
    -- `Gas.selfDestructSurcharge` at the call site.
    | .SELFDESTRUCT                                          =>
      match fork with
      | .Constantinople => 0
      | .Cancun         => 5000

/-- EIP-2200 SSTORE stipend sentry (Istanbul onward, including Cancun):
    an SSTORE that finds `gasleft ≤ G_callstipend = 2300` at entry must
    halt with `OutOfGas` *regardless* of the actual `sstoreCost` — even
    a no-op write. Constantinople (which reverted EIP-1283) has no such
    sentry, so it returns `false` here. -/
def Gas.sstoreSentry (fork : Fork) (gas : Nat) : Bool :=
  match fork with
  | .Constantinople => false
  | .Cancun         => decide (gas ≤ 2300)

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
    Used by CALLDATACOPY, CODECOPY, RETURNDATACOPY, MCOPY, EXTCODECOPY. -/
def Gas.copyWordCost (size : UInt256) : Nat :=
  3 * ((size.toNat + 31) / 32)

/-- Per-word KECCAK256 cost (Yellow Paper `G_keccak256word = 6`):
    `6 · ⌈size/32⌉`. -/
def Gas.keccakWordCost (size : UInt256) : Nat :=
  6 * ((size.toNat + 31) / 32)

/-- Per-byte LOG data cost (Yellow Paper `G_logdata = 8`): `8 · size`. -/
def Gas.logDataCost (size : UInt256) : Nat :=
  8 * size.toNat

/-- The EIP-150 "all but one 64th" gas-forwarding cap: a CALL may forward at
    most `g - ⌊g/64⌋` of the `g` gas remaining (after the call's own
    base/value/new-account/memory costs are paid). -/
def Gas.allButOneSixtyFourth (g : Nat) : Nat := g - g / 64

/-- The stipend (`G_callstipend = 2300`) added to the gas a callee receives
    when a non-zero `value` is transferred — it is *given* to the callee on top
    of the forwarded gas (funded by the `G_callvalue` surcharge), not charged to
    the caller again. -/
def Gas.callStipend : Nat := 2300

/-- The dynamic surcharge a CALL pays on top of its base fee, given whether a
    non-zero value is transferred (`valueNonZero`) and whether the target
    account is currently empty (`targetEmpty`). `G_callvalue = 9000` for a value
    transfer; `G_newaccount = 25000` when that transfer also brings a previously
    empty account into existence. (Pre-EIP-2929 Constantinople schedule; the
    flat `G_call = 700` access fee is the `baseCost`.) -/
def Gas.callSurcharge (valueNonZero targetEmpty : Bool) : Nat :=
  (if valueNonZero then 9000 else 0) +
  (if valueNonZero && targetEmpty then 25000 else 0)

/-- The new-account surcharge a SELFDESTRUCT pays when its balance transfer
    brings a previously empty beneficiary into existence. Fork-gated to
    match the legacy ethereum/tests corpus: Frontier (= our
    `Constantinople` tag) had no `G_newaccount` surcharge yet, so we
    return 0 there; post-EIP-161 (modern, `Cancun`) returns the
    `G_newaccount = 25000` Spurious-Dragon value when both
    `beneficiaryEmpty` and `selfHasBalance` hold. -/
def Gas.selfDestructSurcharge (fork : Fork)
    (beneficiaryEmpty selfHasBalance : Bool) : Nat :=
  match fork with
  | .Constantinople => 0
  | .Cancun         => if beneficiaryEmpty && selfHasBalance then 25000 else 0

/-- CREATE2's extra per-init-code-word keccak cost: `G_keccak256word · ⌈n/32⌉`
    where `n = |initCode|`. This is the cost of the *address derivation*
    keccak (the init code is hashed once to fold into the deterministic
    address), not the optional keccak inside the init code itself. CREATE
    has no such cost (its address derivation is `keccak(rlp([sender,
    nonce]))`, where the input is constant-sized; the RLP-and-keccak cost
    is folded into the `G_create = 32000` base). -/
def Gas.create2HashCost (initCodeLen : Nat) : Nat :=
  6 * ((initCodeLen + 31) / 32)

/-- EIP-3860 (Cancun) per-init-code-word charge:
    `G_initcodeword · ⌈n/32⌉` with `G_initcodeword = 2`.

    Applied to CREATE and CREATE2 on `Cancun` only; `Constantinople`
    predates the EIP, so the cost is `0` there. -/
def Gas.initCodeWordCost (fork : Fork) (initCodeLen : Nat) : Nat :=
  match fork with
  | .Constantinople => 0
  | .Cancun         => 2 * ((initCodeLen + 31) / 32)

/-- EIP-3860 (Cancun) init-code size cap: CREATE / CREATE2 reject init
    code larger than `2 · maxCodeSize = 49152` bytes. The cap is *not*
    enforced on `Constantinople`. -/
@[inline] def Gas.maxInitCodeSize : Nat := 49152

/-- Whether `initCodeLen` exceeds the EIP-3860 cap on the active fork.
    Returns `false` on `Constantinople` (the EIP is Cancun-only). -/
def Gas.initCodeTooLarge (fork : Fork) (initCodeLen : Nat) : Bool :=
  match fork with
  | .Constantinople => false
  | .Cancun         => initCodeLen > Gas.maxInitCodeSize

/-- The SELFDESTRUCT refund (`R_selfdestruct = 24000`) added to
    `Substate.refundBalance` on the *first* time an account self-destructs
    in a transaction. Constantinople and Cancun differ on whether the
    refund applies at all — EIP-3529 (London) removed it, and EIP-6780
    (Cancun) repurposed the opcode entirely — but the legacy ethereum/tests
    "Constantinople" corpus expects the classic 24000 refund. We return `0`
    on Cancun pending EIP-6780. -/
def Gas.selfDestructRefund (fork : Fork) : Nat :=
  match fork with
  | .Constantinople => 24000
  | .Cancun         => 0

/-- Per-byte EXP cost. The per-byte multiplier is `10` at Frontier and
    `50` post-Spurious-Dragon (EIP-160). The legacy ethereum/tests
    "Constantinople" corpus uses the Frontier rate, so `Constantinople`
    selects `10`; `Cancun` uses the modern `50`. `byteLen(0) = 0`. -/
def Gas.expByteCost (fork : Fork) (exponent : UInt256) : Nat :=
  if exponent.toNat = 0 then 0
  else
    let perByte := match fork with | .Constantinople => 10 | .Cancun => 50
    perByte * (Nat.log2 exponent.toNat / 8 + 1)

end EVM
end EvmSemantics
