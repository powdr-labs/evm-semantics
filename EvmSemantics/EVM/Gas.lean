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

Eight forks supported — `Frontier`, `Homestead`, `EIP150`, `EIP158`,
`Byzantium`, `Constantinople` (with EIP-1283), `Petersburg` (=
ConstantinopleFix), and `Cancun`. The differences across them (gas
re-pricing at EIP-150, the per-byte EXP bump at EIP-158, EIP-1283
net-metered SSTORE on the original Constantinople, EIP-2200 on Cancun,
and so on) are captured by `Fork.atLeast`-style branches on the `fork`
argument. Cold/warm-priced reads (EIP-2929) are not yet tracked in
the substate, so the `Cancun` schedule uses **warm** prices throughout
(a lower bound on the real cost).

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
    -- BALANCE / EXTCODEHASH: 20 in Frontier/Homestead, raised to 400 by
    -- EIP-150 (Tangerine Whistle); EXTCODEHASH was introduced at
    -- Constantinople so the pre-Constantinople values are unreachable in
    -- a well-formed test. Cancun: warm-priced placeholder.
    | .BALANCE | .EXTCODEHASH                                =>
      if fork.atLeast .Cancun     then 100
      else if fork.atLeast .EIP150 then 400
      else                              20
    -- EXTCODESIZE / EXTCODECOPY: 20 Frontier/Homestead, raised to 700 by
    -- EIP-150. EXTCODECOPY also pays per-word `Gas.copyWordCost`,
    -- charged dynamically in `stepF.EXTCODECOPY`.
    | .EXTCODESIZE | .EXTCODECOPY                            =>
      if fork.atLeast .Cancun     then 100
      else if fork.atLeast .EIP150 then 700
      else                              20
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
    -- SLOAD: 50 Frontier/Homestead, raised to 200 by EIP-150
    -- (Tangerine Whistle), warm 100 in Cancun.
    | .SLOAD                                                 =>
      if fork.atLeast .Cancun     then 100
      else if fork.atLeast .EIP150 then 200
      else                              50
    -- SSTORE: dynamic — see `Gas.sstoreCost`. Static portion is 0.
    | .SSTORE                                                => 0
    | .TLOAD | .TSTORE                                       => 100
  | .Push p                          => if p.width.val = 0 then 2 else 3
  | .Dup _ | .Swap _                                         => 3
  | .DupN _ | .SwapN _ | .Exchange _                         => 3
  | .Log l                                  => 375 * (l.topics.val + 1)
  | .System op => match op with
    | .RETURN | .REVERT | .INVALID                           => 0
    -- CREATE / CREATE2 base fee: G_create = 32000 (fork-invariant).
    -- Per-byte deposit cost `G_codedeposit = 200 · |deployed_code|` is
    -- charged from the child's remaining gas at the end of init
    -- (`State.codeDepositPerByte`, applied in `State.resumeCreateSuccess`).
    -- CREATE2 additionally pays `Gas.create2HashCost` for its
    -- address-derivation keccak.
    | .CREATE | .CREATE2                                     => 32000
    -- CALL family base access fee: 40 in Frontier/Homestead, raised to
    -- 700 by EIP-150 (Tangerine Whistle), warm 100 in Cancun. The
    -- value/new-account surcharge and gas forwarding are computed in
    -- `stepF.system` / `StepRunning.call`, not here.
    | .CALL | .CALLCODE | .DELEGATECALL | .STATICCALL        =>
      if fork.atLeast .Cancun     then 100
      else if fork.atLeast .EIP150 then 700
      else                              40
    -- SELFDESTRUCT base fee: 0 in Frontier/Homestead, raised to 5000 by
    -- EIP-150. The new-account surcharge — also fork-gated — is added
    -- by `Gas.selfDestructSurcharge` at the call site.
    | .SELFDESTRUCT                                          =>
      if fork.atLeast .EIP150 then 5000 else 0

/-- EIP-2200 SSTORE stipend sentry (Istanbul onward, including Cancun):
    an SSTORE that finds `gasleft ≤ G_callstipend = 2300` at entry must
    halt with `OutOfGas` *regardless* of the actual `sstoreCost` — even
    a no-op write. Constantinople activated this via EIP-1283 without
    the sentry; Istanbul (post-Petersburg) re-introduced net-metering
    with the sentry. Among the forks we model, only Constantinople and
    Cancun have a sentry: Constantinople has none (EIP-1283 was
    pre-EIP-2200), Cancun has the EIP-2200 sentry. -/
def Gas.sstoreSentry (fork : Fork) (gas : Nat) : Bool :=
  match fork with
  | .Cancun => decide (gas ≤ 2300)
  | _       => false

/-- Dynamic gas cost of an SSTORE under `fork`, given the slot's
    `original` value (at frame start), `current` value (just before this
    write), and the `new` value being written.

    **Constantinople** uses the pre-EIP-1283 schedule. EIP-1283 was
    *briefly* active in the original Constantinople fork before being
    reverted at Petersburg ("ConstantinopleFix"); the legacy
    ethereum/tests `_Constantinople` corpus variant was generated
    against the *original* (with-EIP-1283) rules, while
    `_ConstantinopleFix` reverts to pre-EIP-1283. We target the
    post-revert (Petersburg) semantics — that's why `StateTestRunner`
    selects the `_ConstantinopleFix` variant, and our `Constantinople`
    fork tag matches:

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

    Refunds are tracked separately in `Substate.refundBalance` and not
    yet wired into the harness's gas comparison. -/
def Gas.sstoreCost (fork : Fork) (original current new : UInt256) : Nat :=
  match fork with
  -- Original Constantinople activated EIP-1283 net-metered SSTORE.
  | .Constantinople =>
    if current.toNat = new.toNat then 200
    else if current.toNat = original.toNat then
      if original.toNat = 0 then 20000 else 5000
    else 200
  -- Cancun uses EIP-2200 (refined EIP-1283 with sentry). EIP-2929
  -- cold/warm surcharge not yet modelled.
  | .Cancun =>
    if current.toNat = new.toNat then 100
    else if current.toNat = original.toNat then
      if original.toNat = 0 then 20000 else 2900
    else 100
  -- Frontier through Petersburg use the pre-EIP-1283 schedule.
  | _ =>
    if current.toNat = 0 ∧ new.toNat ≠ 0 then 20000 else 5000

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
    base/value/new-account/memory costs are paid). Fork-gated: pre-EIP-150
    forks (Frontier, Homestead) have *no* cap and may forward all of `g`. -/
def Gas.allButOneSixtyFourth (fork : Fork) (g : Nat) : Nat :=
  if fork.atLeast .EIP150 then g - g / 64 else g

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
    brings a previously empty beneficiary into existence. Pre-EIP-150
    (Frontier/Homestead) had no surcharge. EIP-150 (Tangerine Whistle)
    introduced `G_newaccount = 25000` when the beneficiary didn't exist.
    EIP-158 (Spurious Dragon) refined it to charge only when the
    beneficiary is *empty* AND the self-destructing account has a
    non-zero balance — i.e. only when the transfer actually delivers
    value to a fresh account. We use the EIP-158 rule from `.EIP158`
    onwards (which matches the legacy state-tests Constantinople-era
    corpus). -/
def Gas.selfDestructSurcharge (fork : Fork)
    (beneficiaryEmpty selfHasBalance : Bool) : Nat :=
  if fork.atLeast .EIP158 then
    if beneficiaryEmpty && selfHasBalance then 25000 else 0
  else if fork.atLeast .EIP150 then
    -- EIP-150 charges 25000 if beneficiary is empty, regardless of value.
    if beneficiaryEmpty then 25000 else 0
  else 0

/-- CREATE2's extra per-init-code-word keccak cost: `G_keccak256word · ⌈n/32⌉`
    where `n = |initCode|`. This is the cost of the *address derivation*
    keccak (the init code is hashed once to fold into the deterministic
    address), not the optional keccak inside the init code itself. CREATE
    has no such cost (its address derivation is `keccak(rlp([sender,
    nonce]))`, where the input is constant-sized; the RLP-and-keccak cost
    is folded into the `G_create = 32000` base). -/
def Gas.create2HashCost (initCodeLen : Nat) : Nat :=
  6 * ((initCodeLen + 31) / 32)

/-- The SELFDESTRUCT refund (`R_selfdestruct = 24000`) added to
    `Substate.refundBalance` on the *first* time an account self-destructs
    in a transaction. EIP-3529 (London) removed it; EIP-6780 (Cancun)
    repurposed the opcode entirely. For our supported forks Frontier
    through Petersburg the classic 24000 refund applies; Cancun has 0. -/
def Gas.selfDestructRefund (fork : Fork) : Nat :=
  if fork.atLeast .Cancun then 0 else 24000

/-- Per-byte EXP cost. The per-byte multiplier is `10` at Frontier
    through Tangerine Whistle and `50` post-Spurious-Dragon (EIP-160).
    `byteLen(0) = 0`. -/
def Gas.expByteCost (fork : Fork) (exponent : UInt256) : Nat :=
  if exponent.toNat = 0 then 0
  else
    let perByte := if fork.atLeast .EIP158 then 50 else 10
    perByte * (Nat.log2 exponent.toNat / 8 + 1)

end EVM
end EvmSemantics
