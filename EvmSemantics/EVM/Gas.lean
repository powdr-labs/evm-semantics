module

public import EvmSemantics.EVM.Operation
public import EvmSemantics.EVM.Fork
public import EvmSemantics.Data.UInt256
public import EvmSemantics.EVM.State

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
    -- BALANCE = 400 (EIP-150 Tangerine Whistle, unchanged through
    -- Constantinople; Istanbul EIP-1884 raised to 700 but the legacy
    -- corpus we target predates that).
    -- EXTCODEHASH = 400 (EIP-1052, introduced at Constantinople).
    | .BALANCE | .EXTCODEHASH                                =>
      match fork with
      | .Constantinople => 400
      | .Cancun         => 100  -- warm-priced placeholder for EIP-2929
    -- EXTCODESIZE = 700 (EIP-150). EXTCODECOPY = 700 base + per-word
    -- `Gas.copyWordCost`, the per-word piece is charged dynamically
    -- in `stepF.EXTCODECOPY`.
    | .EXTCODESIZE | .EXTCODECOPY                            =>
      match fork with
      | .Constantinople => 700
      | .Cancun         => 100  -- warm-priced placeholder for EIP-2929
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

----------------------------------------------------------------------------
-- Per-opcode total gas-cost functions.
--
-- Each `Gas.<opcode>Total` takes the pre-execution `State` and the
-- opcode's stack arguments and returns the total gas charge: static
-- `baseCost` + any memory-expansion delta + any per-word/per-byte
-- dynamic cost.
--
-- `Step` constructors use the function twice — once in the
-- gas-precondition hypothesis (`Gas.<opcode>Total s … ≤ s.gasAvailable`)
-- and once (via `Nat.sub_add_eq`) in the post-state's `gasAvailable`.
-- Sharing the name makes the rule Hoare-triple friendly: both sides
-- refer to the same identifier rather than two appearances of a long
-- arithmetic expression.
----------------------------------------------------------------------------

/-- Total gas cost of `KECCAK256` at `s` for stack args `offset, size`:
    static base + memory-expansion delta for `[offset, offset+size)` +
    per-word cost `6 · ⌈size/32⌉`. -/
@[inline] def Gas.keccakTotal (s : State) (offset size : UInt256) : Nat :=
  Gas.baseCost s.executionEnv.fork .KECCAK256
  + MachineState.memExpansionDelta s.activeWords.toNat offset.toNat size.toNat
  + Gas.keccakWordCost size

/-- Total gas cost of `CALLDATACOPY` at `s` for stack args
    `destOff, _srcOff, sz`: static base + memory-expansion delta for the
    destination range `[destOff, destOff+sz)` + per-word copy cost
    `3 · ⌈sz/32⌉`. Source offset doesn't affect cost (calldata is free
    to read). -/
@[inline] def Gas.calldatacopyTotal (s : State) (destOff sz : UInt256) : Nat :=
  Gas.baseCost s.executionEnv.fork .CALLDATACOPY
  + MachineState.memExpansionDelta s.activeWords.toNat destOff.toNat sz.toNat
  + Gas.copyWordCost sz

/-- Total gas cost of `CODECOPY` at `s` for stack args
    `destOff, _srcOff, sz`: static base + memory-expansion delta for the
    destination range `[destOff, destOff+sz)` + per-word copy cost
    `3 · ⌈sz/32⌉`. -/
@[inline] def Gas.codecopyTotal (s : State) (destOff sz : UInt256) : Nat :=
  Gas.baseCost s.executionEnv.fork .CODECOPY
  + MachineState.memExpansionDelta s.activeWords.toNat destOff.toNat sz.toNat
  + Gas.copyWordCost sz

/-- Total gas cost of `EXTCODECOPY` at `s` for stack args
    `_addr, destOff, _srcOff, sz`: static base (which already absorbs the
    `Constantinople`-era flat 700 access fee — see `Gas.baseCost`) +
    memory-expansion delta for `[destOff, destOff+sz)` + per-word copy
    cost `3 · ⌈sz/32⌉`. EIP-2929 cold/warm pricing is not yet modelled. -/
@[inline] def Gas.extcodecopyTotal (s : State) (destOff sz : UInt256) : Nat :=
  Gas.baseCost s.executionEnv.fork .EXTCODECOPY
  + MachineState.memExpansionDelta s.activeWords.toNat destOff.toNat sz.toNat
  + Gas.copyWordCost sz

/-- Total gas cost of `RETURNDATACOPY` at `s` for stack args
    `destOff, _srcOff, sz`: static base + memory-expansion delta for the
    destination range `[destOff, destOff+sz)` + per-word copy cost
    `3 · ⌈sz/32⌉`. -/
@[inline] def Gas.returndatacopyTotal (s : State) (destOff sz : UInt256) : Nat :=
  Gas.baseCost s.executionEnv.fork .RETURNDATACOPY
  + MachineState.memExpansionDelta s.activeWords.toNat destOff.toNat sz.toNat
  + Gas.copyWordCost sz

/-- Total gas cost of `MLOAD` at `s` for stack arg `offset`: static base
    + memory-expansion delta for the fixed 32-byte read range
    `[offset, offset+32)`. -/
@[inline] def Gas.mloadTotal (s : State) (offset : UInt256) : Nat :=
  Gas.baseCost s.executionEnv.fork .MLOAD
  + MachineState.memExpansionDelta s.activeWords.toNat offset.toNat 32

/-- Total gas cost of `MSTORE` at `s` for stack arg `offset`: static base
    + memory-expansion delta for the fixed 32-byte write range
    `[offset, offset+32)`. -/
@[inline] def Gas.mstoreTotal (s : State) (offset : UInt256) : Nat :=
  Gas.baseCost s.executionEnv.fork .MSTORE
  + MachineState.memExpansionDelta s.activeWords.toNat offset.toNat 32

/-- Total gas cost of `MSTORE8` at `s` for stack arg `offset`: static base
    + memory-expansion delta for the 1-byte write range
    `[offset, offset+1)`. -/
@[inline] def Gas.mstore8Total (s : State) (offset : UInt256) : Nat :=
  Gas.baseCost s.executionEnv.fork .MSTORE8
  + MachineState.memExpansionDelta s.activeWords.toNat offset.toNat 1

/-- Total gas cost of `MCOPY` at `s` for stack args `destOff, srcOff, sz`:
    static base + memory-expansion delta for the union of read range
    `[srcOff, srcOff+sz)` and write range `[destOff, destOff+sz)` +
    per-word copy cost `3 · ⌈sz/32⌉`. -/
@[inline] def Gas.mcopyTotal (s : State) (destOff srcOff sz : UInt256) : Nat :=
  Gas.baseCost s.executionEnv.fork .MCOPY
  + MachineState.memExpansionDelta2 s.activeWords.toNat
      destOff.toNat sz.toNat srcOff.toNat sz.toNat
  + Gas.copyWordCost sz

/-- Total gas cost of `SSTORE` at `s` for stack args `key, value`:
    static base (0 in current schedules) + the EIP-2200 net-metered
    dynamic cost `Gas.sstoreCost fork original current new`, where
    `original` is the per-tx original value from `Substate.originalStorage`
    and `current` is the live storage value. -/
@[inline] def Gas.sstoreTotal (s : State) (key value : UInt256) : Nat :=
  Gas.baseCost s.executionEnv.fork .SSTORE
  + Gas.sstoreCost s.executionEnv.fork
      (s.substate.originalStorage s.executionEnv.codeOwner key)
      ((s.accountMap s.executionEnv.codeOwner).storage key)
      value

/-- Total gas cost of `RETURN` at `s` for stack args `offset, size`:
    static base + memory-expansion delta for the read range
    `[offset, offset+size)`. -/
@[inline] def Gas.returnTotal (s : State) (offset size : UInt256) : Nat :=
  Gas.baseCost s.executionEnv.fork .RETURN
  + MachineState.memExpansionDelta s.activeWords.toNat offset.toNat size.toNat

/-- Total gas cost of `REVERT` at `s` for stack args `offset, size`:
    static base + memory-expansion delta for the read range
    `[offset, offset+size)`. -/
@[inline] def Gas.revertTotal (s : State) (offset size : UInt256) : Nat :=
  Gas.baseCost s.executionEnv.fork .REVERT
  + MachineState.memExpansionDelta s.activeWords.toNat offset.toNat size.toNat

/-- Gas charged to the parent frame before forwarding for a `CALL`:
    static base + memory-expansion delta for the union of args and return
    ranges + value/new-account surcharge. The forwarded gas (63/64 etc.) is
    separately deducted from `s.gasAvailable - callCommitted` and given to
    the callee. -/
@[inline] def Gas.callCommitted (s : State) (value : UInt256)
    (argsOff argsLen retOff retLen toArg : UInt256) : Nat :=
  Gas.baseCost s.executionEnv.fork .CALL
  + MachineState.memExpansionDelta2 s.activeWords.toNat
      argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat
  + Gas.callSurcharge (value.toNat != 0)
      (s.accountMap (AccountAddress.ofUInt256 toArg)).isEmpty

/-- Gas charged to the parent frame before forwarding for a `CALLCODE`:
    static base + memory-expansion delta + value-transfer surcharge.
    CALLCODE never creates a new account, so `targetEmpty = false`. -/
@[inline] def Gas.callcodeCommitted (s : State) (value : UInt256)
    (argsOff argsLen retOff retLen : UInt256) : Nat :=
  Gas.baseCost s.executionEnv.fork .CALLCODE
  + MachineState.memExpansionDelta2 s.activeWords.toNat
      argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat
  + Gas.callSurcharge (value.toNat != 0) false

/-- Gas charged to the parent frame before forwarding for a `DELEGATECALL`:
    static base + memory-expansion delta. No value, so no surcharge. -/
@[inline] def Gas.delegatecallCommitted (s : State)
    (argsOff argsLen retOff retLen : UInt256) : Nat :=
  Gas.baseCost s.executionEnv.fork .DELEGATECALL
  + MachineState.memExpansionDelta2 s.activeWords.toNat
      argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat

/-- Gas charged to the parent frame before forwarding for a `STATICCALL`:
    static base + memory-expansion delta. No value, so no surcharge. -/
@[inline] def Gas.staticcallCommitted (s : State)
    (argsOff argsLen retOff retLen : UInt256) : Nat :=
  Gas.baseCost s.executionEnv.fork .STATICCALL
  + MachineState.memExpansionDelta2 s.activeWords.toNat
      argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat

/-- Gas charged to the parent frame before forwarding for `CREATE`:
    static base + memory-expansion delta for the init-code window. -/
@[inline] def Gas.createCommitted (s : State) (offset size : UInt256) : Nat :=
  Gas.baseCost s.executionEnv.fork .CREATE
  + MachineState.memExpansionDelta s.activeWords.toNat offset.toNat size.toNat

/-- Gas charged to the parent frame before forwarding for `CREATE2`:
    static base + memory-expansion delta for the init-code window +
    EIP-3860 per-word hashing cost on the init code. -/
@[inline] def Gas.create2Committed (s : State) (offset size : UInt256) : Nat :=
  Gas.baseCost s.executionEnv.fork .CREATE2
  + MachineState.memExpansionDelta s.activeWords.toNat offset.toNat size.toNat
  + Gas.create2HashCost size.toNat

/-- Total gas cost of `SELFDESTRUCT` at `s` with `beneficiary`: static base
    (`G_selfdestruct = 5000`) + the EIP-150/EIP-161 `25000` new-account
    surcharge when the beneficiary is empty *and* self has a non-zero
    balance. -/
@[inline] def Gas.selfDestructTotal (s : State) (beneficiary : UInt256) : Nat :=
  Gas.baseCost s.executionEnv.fork .SELFDESTRUCT
  + Gas.selfDestructSurcharge s.executionEnv.fork
      ((s.accountMap (AccountAddress.ofUInt256 beneficiary)).isEmpty)
      ((s.accountMap s.executionEnv.codeOwner).balance.toNat != 0)

/-- Total gas cost of `LOG n` at `s` for stack args `offset, size`:
    static base (`375 + 375·n`) + memory-expansion delta for the read range
    `[offset, offset+size)` + per-byte log-data cost `8 · size`. -/
@[inline] def Gas.logTotal (s : State) (n : Fin 5) (offset size : UInt256) : Nat :=
  Gas.baseCost s.executionEnv.fork (.Log ⟨n⟩)
  + MachineState.memExpansionDelta s.activeWords.toNat offset.toNat size.toNat
  + Gas.logDataCost size

end EVM
end EvmSemantics
