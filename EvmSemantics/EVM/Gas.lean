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
    -- BALANCE / EXTCODEHASH: 20 in Frontier/Homestead, raised to 400
    -- by EIP-150 (Tangerine Whistle), 700 by EIP-1884 (Istanbul), warm
    -- 100 by EIP-2929 (Berlin; cold price not yet modelled).
    | .BALANCE | .EXTCODEHASH                                =>
      if fork.atLeast .Berlin     then 100
      else if fork.atLeast .Istanbul then 700
      else if fork.atLeast .TangerineWhistle then 400
      else                              20
    -- EXTCODESIZE / EXTCODECOPY: 20 Frontier/Homestead, raised to 700
    -- by EIP-150, warm-100 by EIP-2929 (Berlin). EXTCODECOPY also pays
    -- per-word `Gas.copyWordCost`, charged dynamically.
    | .EXTCODESIZE | .EXTCODECOPY                            =>
      if fork.atLeast .Berlin     then 100
      else if fork.atLeast .TangerineWhistle then 700
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
    -- (Tangerine Whistle), 800 by EIP-1884 (Istanbul), warm-100 by
    -- EIP-2929 (Berlin; we use the warm price since access lists
    -- aren't tracked yet).
    | .SLOAD                                                 =>
      if fork.atLeast .Berlin     then 100
      else if fork.atLeast .Istanbul then 800
      else if fork.atLeast .TangerineWhistle then 200
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
    -- CREATE / CREATE2 base fee (`G_create = 32000`). Per-byte deposit
    -- cost (`G_codedeposit = 200 · |deployed_code|`) is charged from the
    -- child's remaining gas at the end of init (`State.codeDepositPerByte`,
    -- applied in `State.resumeCreateSuccess`). CREATE2 *additionally* pays
    -- a keccak hash over the init code for its address derivation
    -- (`Gas.create2HashCost`), charged at this site.
    | .CREATE | .CREATE2                                     => 32000
    -- CALL family base access fee: 40 in Frontier/Homestead, raised
    -- to 700 by EIP-150 (Tangerine Whistle), warm-100 by EIP-2929
    -- (Berlin). The value/new-account surcharge and 63/64 forwarding
    -- are computed in `stepF.system` / `StepRunning.call`, not here.
    | .CALL | .CALLCODE | .DELEGATECALL | .STATICCALL        =>
      if fork.atLeast .Berlin     then 100
      else if fork.atLeast .TangerineWhistle then 700
      else                              40
    -- SELFDESTRUCT base fee: 0 in Frontier/Homestead, raised to 5000
    -- by EIP-150 (Tangerine Whistle). The new-account surcharge —
    -- also fork-gated — is added by `Gas.selfDestructSurcharge` at
    -- the call site.
    | .SELFDESTRUCT                                          =>
      if fork.atLeast .TangerineWhistle then 5000 else 0

/-- EIP-2200 SSTORE stipend sentry (Istanbul onward, including Cancun):
    an SSTORE that finds `gasleft ≤ G_callstipend = 2300` at entry must
    halt with `OutOfGas` *regardless* of the actual `sstoreCost` — even
    a no-op write. Pre-Istanbul (including the original Constantinople
    with EIP-1283 and Petersburg which reverted it) had no such sentry. -/
def Gas.sstoreSentry (fork : Fork) (gas : Nat) : Bool :=
  if fork.atLeast .Istanbul then decide (gas ≤ 2300) else false

/-- Dynamic gas cost of an SSTORE under `fork`, given the slot's
    `original` value (at frame start), `current` value (just before this
    write), and the `new` value being written.

    Four distinct schedules across the forks we model:

    **Pre-EIP-1283** — Frontier..Byzantium and Petersburg (which
    reverted EIP-1283):

    | Condition                              | Cost  |
    |----------------------------------------|------:|
    | `current = 0 ∧ new ≠ 0` (fresh set)    | 20000 |
    | otherwise (reset, clear, no-op)        |  5000 |

    **EIP-1283 — Constantinople only** (briefly active before being
    reverted by Petersburg; net-metered with 200-gas no-op):

    | Condition                                          | Cost  |
    |----------------------------------------------------|------:|
    | `current = new` (no-op)                            |   200 |
    | `original = current ∧ original = 0` (fresh set)    | 20000 |
    | `original = current ∧ original ≠ 0` (clean reset)  |  5000 |
    | otherwise (`original ≠ current`, "dirty")          |   200 |

    **EIP-2200 — Istanbul / MuirGlacier** (net-metered with the
    `G_callstipend = 2300` sentry checked separately by
    `Gas.sstoreSentry`, and an 800-gas no-op):

    | Condition                                          | Cost  |
    |----------------------------------------------------|------:|
    | `current = new` (no-op)                            |   800 |
    | `original = current ∧ original = 0` (fresh set)    | 20000 |
    | `original = current ∧ original ≠ 0` (clean reset)  |  5000 |
    | otherwise (dirty)                                  |   800 |

    **EIP-2929 warm placeholder — Berlin..Cancun** (we don't yet
    track cold/warm access lists, so we use warm prices throughout;
    the cold first-touch surcharge of 2100 is omitted):

    | Condition                                          | Cost  |
    |----------------------------------------------------|------:|
    | `current = new` (no-op)                            |   100 |
    | `original = current ∧ original = 0` (fresh set)    | 20000 |
    | `original = current ∧ original ≠ 0` (clean reset)  |  2900 |
    | otherwise (dirty)                                  |   100 |

    Refunds are returned by `Gas.sstoreRefund` (status: scaffolding —
    not yet applied to balance). -/
def Gas.sstoreCost (fork : Fork) (original current new : UInt256) : Nat :=
  if fork.atLeast .Berlin then
    -- EIP-2929 warm placeholder.
    if current.toNat = new.toNat then 100
    else if current.toNat = original.toNat then
      if original.toNat = 0 then 20000 else 2900
    else 100
  else if fork.atLeast .Istanbul then
    -- EIP-2200 net-metered. (MuirGlacier shares the Istanbul EVM.)
    if current.toNat = new.toNat then 800
    else if current.toNat = original.toNat then
      if original.toNat = 0 then 20000 else 5000
    else 800
  else if fork.toOrd = Fork.Constantinople.toOrd then
    -- EIP-1283: net-metered, briefly active *only* in Constantinople.
    if current.toNat = new.toNat then 200
    else if current.toNat = original.toNat then
      if original.toNat = 0 then 20000 else 5000
    else 200
  else
    -- Pre-EIP-1283 (Frontier..Byzantium + Petersburg).
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
    base/value/new-account/memory costs are paid).

    Pre-EIP-150 (Frontier, Homestead): **no cap** — the call may try to
    forward up to all of `g`. If `gas_arg > g`, the CALL OOGs (which is
    exactly why EIP-150 introduced the cap). Post-EIP-150 (Tangerine
    Whistle onwards): the cap `g - g/64` always applies. -/
def Gas.allButOneSixtyFourth (fork : Fork) (g : Nat) : Nat :=
  if fork.atLeast .TangerineWhistle then g - g / 64 else g

/-- Actual gas forwarded to a callee given the caller's remaining gas `g`
    (after the call's own base/value/new-account/memory costs are paid)
    and the user-supplied `gas_arg`. From EIP-150 onwards this is
    `min(gas_arg, allButOneSixtyFourth g)`; pre-EIP-150 there is no cap
    and the gas argument is used verbatim — if it exceeds `g`, the
    caller's subsequent `forwarded ≤ g` check fails and the CALL OOGs. -/
def Gas.forwardGas (fork : Fork) (g gas_arg : Nat) : Nat :=
  if fork.atLeast .TangerineWhistle then Nat.min gas_arg (g - g / 64)
  else gas_arg

/-- The stipend (`G_callstipend = 2300`) added to the gas a callee receives
    when a non-zero `value` is transferred — it is *given* to the callee on top
    of the forwarded gas (funded by the `G_callvalue` surcharge), not charged to
    the caller again. -/
def Gas.callStipend : Nat := 2300

/-- The "emptiness" flag `Gas.callSurcharge` consumes for the
    `G_newaccount` charge. The check differs across EIP-158:

    * **Pre-EIP-158** (Frontier, Homestead, TangerineWhistle): the
      surcharge fires whenever the target *doesn't exist* in the state
      trie. Once a CALL has touched an address (even with value = 0),
      `AccountMap.transfer` inserts an entry for it, so a *second* CALL
      to the same address should no longer be charged. Using
      structural emptiness (`Account.isEmpty`) here would double-charge
      because the inserted entry is still `{nonce=0, balance=0,
      code=∅}` and would look empty. The fix is to key on state
      membership (`!σ.contains tgt`).

    * **Post-EIP-158** (Spurious Dragon+): the surcharge fires only
      when the target is *empty* per EIP-161 (`nonce = 0 ∧ balance = 0
      ∧ code = ∅`) *and* the CALL is value-transferring — see
      `Gas.callSurcharge`. Structural emptiness (`Account.isEmpty`) is
      the right check here: EIP-161 prunes empty entries end-of-tx,
      so the distinction between "not in state" and "in state but
      empty" collapses in observable behaviour.

    The `Gas.callSurcharge` function then multiplies the returned flag
    by 25000 (pre-EIP-158 unconditionally, post-EIP-158 gated on
    `valueNonZero`). -/
def Gas.callTargetIsNew (fork : Fork) (σ : AccountMap) (tgt : AccountAddress) : Bool :=
  if fork.atLeast .SpuriousDragon then (σ tgt).isEmpty
  else ¬ σ.contains tgt

/-- The dynamic surcharge a CALL pays on top of its base fee.

    * `G_callvalue = 9000` for a value-transferring CALL (`valueNonZero`).
    * `G_newaccount = 25000` when the call brings a previously empty
      account into existence. The "into existence" condition is fork-gated:
      - Pre-EIP-158 (`Frontier`, `Homestead`, `TangerineWhistle`): charged whenever
        the target is empty, even with `value = 0` — the legacy rule is
        that any CALL to a non-existent account creates one.
      - From EIP-158 (Spurious Dragon) onwards: charged only when the
        target is empty AND the value transfer is non-zero (i.e. only
        when the transfer actually delivers wei to a fresh account). -/
def Gas.callSurcharge (fork : Fork) (valueNonZero targetEmpty : Bool) : Nat :=
  let valSurcharge : Nat := if valueNonZero then 9000 else 0
  let newSurcharge : Nat :=
    if fork.atLeast .SpuriousDragon then
      if valueNonZero && targetEmpty then 25000 else 0
    else
      if targetEmpty then 25000 else 0
  valSurcharge + newSurcharge

/-- The new-account surcharge a SELFDESTRUCT pays when its balance transfer
    brings a previously empty beneficiary into existence. Fork-gated to
    match the legacy ethereum/tests corpus: Frontier (= our
    `Constantinople` tag) had no `G_newaccount` surcharge yet, so we
    return 0 there; post-EIP-161 (modern, `Cancun`) returns the
    `G_newaccount = 25000` Spurious-Dragon value when both
    `beneficiaryEmpty` and `selfHasBalance` hold. -/
def Gas.selfDestructSurcharge (fork : Fork)
    (beneficiaryEmpty selfHasBalance : Bool) : Nat :=
  if fork.atLeast .SpuriousDragon then
    if beneficiaryEmpty && selfHasBalance then 25000 else 0
  else if fork.atLeast .TangerineWhistle then
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

/-- EIP-3860 (Cancun) per-init-code-word charge:
    `G_initcodeword · ⌈n/32⌉` with `G_initcodeword = 2`.

    Applied to CREATE and CREATE2 on `Cancun` only; `Constantinople`
    predates the EIP, so the cost is `0` there. -/
def Gas.initCodeWordCost (fork : Fork) (initCodeLen : Nat) : Nat :=
  if fork.atLeast .Shanghai then 2 * ((initCodeLen + 31) / 32) else 0

/-- EIP-3860 (Cancun) init-code size cap: CREATE / CREATE2 reject init
    code larger than `2 · maxCodeSize = 49152` bytes. The cap is *not*
    enforced on `Constantinople`. -/
@[inline] def Gas.maxInitCodeSize : Nat := 49152

/-- Whether `initCodeLen` exceeds the EIP-3860 cap on the active fork.
    Returns `false` on `Constantinople` (the EIP is Cancun-only). -/
def Gas.initCodeTooLarge (fork : Fork) (initCodeLen : Nat) : Bool :=
  fork.atLeast .Shanghai && initCodeLen > Gas.maxInitCodeSize

/-- The SELFDESTRUCT refund (`R_selfdestruct = 24000`) added to
    `Substate.refundBalance` on the *first* time an account self-destructs
    in a transaction. Constantinople and Cancun differ on whether the
    refund applies at all — EIP-3529 (London) removed it, and EIP-6780
    (Cancun) repurposed the opcode entirely — but the legacy ethereum/tests
    "Constantinople" corpus expects the classic 24000 refund. We return `0`
    on Cancun pending EIP-6780. -/
def Gas.selfDestructRefund (fork : Fork) : Nat :=
  -- London (EIP-3529) removed the SELFDESTRUCT refund entirely.
  if fork.atLeast .London then 0 else 24000

/-- Per-byte EXP cost. The per-byte multiplier is `10` at Frontier and
    `50` post-Spurious-Dragon (EIP-160). The legacy ethereum/tests
    "Constantinople" corpus uses the Frontier rate, so `Constantinople`
    selects `10`; `Cancun` uses the modern `50`. `byteLen(0) = 0`. -/
def Gas.expByteCost (fork : Fork) (exponent : UInt256) : Nat :=
  if exponent.toNat = 0 then 0
  else
    let perByte := if fork.atLeast .SpuriousDragon then 50 else 10
    perByte * (Nat.log2 exponent.toNat / 8 + 1)

/-- SSTORE refund counter delta — signed delta added to
    `Substate.refundBalance` for one SSTORE writing `new` over `current`
    when the slot's transaction-start value was `original`.

    **Status: scaffolding.** This helper computes the fork-correct
    refund delta but is *not yet wired into* `stepF` (SSTORE doesn't
    accumulate `refundBalance` on this branch). The runner therefore
    never applies refunds — they only matter for the `passFull` (sender
    balance) comparison, not the `passCore` (storage/nonce/code) one
    the regression baseline keys on. Kept here so the wiring is a
    one-line change once we want to start tracking `passFull` balances.

    * **Pre-EIP-1283** (Frontier..Byzantium and Petersburg+pre-Istanbul):
      +15000 on a clear-to-zero, otherwise 0.
    * **EIP-1283 / EIP-2200** (original Constantinople / Istanbul+):
      net-metered with negative refunds for cancellations.
    * **EIP-3529** (London+) halves several refund constants and drops
      others.

    The constants change across the net-metered forks (Yellow Paper
    §H.3 / EIP-3529):

    | constant       | EIP-1283 | EIP-2200 | EIP-3529 (London+) |
    |----------------|---------:|---------:|-------------------:|
    | `Sclear`       |    15000 |    15000 |               4800 |
    | `Sreset-Hwarm` |     4800 |     4200 |               2800 |
    | `Sset-Hwarm`   |    19800 |    19200 |              19900 | -/
def Gas.sstoreRefund (fork : Fork) (original current new : UInt256) : Int :=
  let o := original.toNat
  let c := current.toNat
  let n := new.toNat
  if c = n then 0
  else if fork.atLeast .Istanbul ∨ fork.toOrd = Fork.Constantinople.toOrd then
    -- Net-metered schedule. Same shape for EIP-1283 (Constantinople
    -- only), EIP-2200 (Istanbul/Berlin), and EIP-3529 (London+); only
    -- the three refund constants differ. Petersburg / ConstantinopleFix
    -- reverted EIP-1283 back to pre-1283, so it falls through to the
    -- clear-to-zero branch below.
    let london := fork.atLeast .London
    let eip1283 := fork.toOrd = Fork.Constantinople.toOrd
    let sclear : Int := if london then 4800 else 15000
    let sresetMinusH : Int :=
      if london then 2800
      else if eip1283 then 4800
      else 4200
    let ssetMinusH   : Int :=
      if london then 19900
      else if eip1283 then 19800
      else 19200
    if o = c then
      if o ≠ 0 ∧ n = 0 then sclear else 0
    else
      let r₀ : Int :=
        if o ≠ 0 ∧ c ≠ 0 ∧ n = 0 then sclear
        else if o ≠ 0 ∧ c = 0 then -sclear
        else 0
      let r₁ : Int :=
        if o ≠ 0 ∧ o = n then sresetMinusH
        else if o = 0 ∧ o = n then ssetMinusH
        else 0
      r₀ + r₁
  else
    -- Pre-EIP-1283 schedule: clear-to-zero only.
    if c ≠ 0 ∧ n = 0 then 15000 else 0

/-- Denominator of the end-of-tx refund cap: `refund ≤ gas_used / refundDenom`.
    Pre-EIP-3529 (everything before London) uses 2; London onwards uses
    5 per EIP-3529 (the EIP also removed the SELFDESTRUCT refund, which
    is gated separately in `Gas.selfDestructRefund`).

    **Status: scaffolding.** Used together with `Gas.sstoreRefund` once
    the runner applies end-of-tx refunds to the sender balance; see the
    note there. -/
def Gas.refundDenom (fork : Fork) : Nat :=
  if fork.atLeast .London then 5 else 2

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

/-- EIP-2929 cold-access surcharge for `SSTORE`: the full cold-SLOAD cost
    `2100` when Berlin+ and the slot `(address, key)` is not yet warm, else
    `0`. Added on top of the EIP-2200 net-metered `Gas.sstoreCost` (which
    already uses the warm `100` as its SLOAD component from Berlin). -/
@[inline] def Gas.sstoreColdSurcharge (s : State) (key : UInt256) : Nat :=
  if s.executionEnv.fork.atLeast .Berlin
     && !s.substate.isWarmStorageKey (s.executionEnv.address, key)
  then 2100 else 0

/-- Total gas cost of `SSTORE` at `s` for stack args `key, value`: static
    base (0 in current schedules) + the EIP-2200 net-metered dynamic cost
    `Gas.sstoreCost` + the EIP-2929 cold surcharge (`Gas.sstoreColdSurcharge`),
    where `original` is the per-tx original value from
    `Substate.originalStorage` and `current` is the live storage value. -/
@[inline] def Gas.sstoreTotal (s : State) (key value : UInt256) : Nat :=
  Gas.baseCost s.executionEnv.fork .SSTORE
  + (Gas.sstoreCost s.executionEnv.fork
        (s.substate.originalStorage s.executionEnv.address key)
        ((s.accountMap s.executionEnv.address).storage key)
        value
      + Gas.sstoreColdSurcharge s key)

/-- EIP-2929 cold-access surcharge for `SLOAD`: `2000` (= cold `2100` −
    warm `100`) when Berlin+ and the slot `(address, key)` is not yet warm,
    else `0`. The warm price itself is the static `Gas.baseCost .SLOAD`
    (`100` from Berlin), so this is the extra charged on a cold first touch. -/
@[inline] def Gas.sloadColdSurcharge (s : State) (key : UInt256) : Nat :=
  if s.executionEnv.fork.atLeast .Berlin
     && !s.substate.isWarmStorageKey (s.executionEnv.address, key)
  then 2000 else 0

/-- Total gas cost of `SLOAD` at `s` for stack arg `key`: the static warm
    base plus the EIP-2929 cold surcharge (`Gas.sloadColdSurcharge`). -/
@[inline] def Gas.sloadTotal (s : State) (key : UInt256) : Nat :=
  Gas.baseCost s.executionEnv.fork .SLOAD + Gas.sloadColdSurcharge s key

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
  + Gas.callSurcharge s.executionEnv.fork (value.toNat != 0)
      (Gas.callTargetIsNew s.executionEnv.fork s.accountMap
        (AccountAddress.ofUInt256 toArg))

/-- Gas charged to the parent frame before forwarding for a `CALLCODE`:
    static base + memory-expansion delta + value-transfer surcharge.
    CALLCODE never creates a new account, so `targetEmpty = false`. -/
@[inline] def Gas.callcodeCommitted (s : State) (value : UInt256)
    (argsOff argsLen retOff retLen : UInt256) : Nat :=
  Gas.baseCost s.executionEnv.fork .CALLCODE
  + MachineState.memExpansionDelta2 s.activeWords.toNat
      argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat
  + Gas.callSurcharge s.executionEnv.fork (value.toNat != 0) false

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
      ((s.accountMap s.executionEnv.address).balance.toNat != 0)

/-- Total gas cost of `LOG n` at `s` for stack args `offset, size`:
    static base (`375 + 375·n`) + memory-expansion delta for the read range
    `[offset, offset+size)` + per-byte log-data cost `8 · size`. -/
@[inline] def Gas.logTotal (s : State) (n : Fin 5) (offset size : UInt256) : Nat :=
  Gas.baseCost s.executionEnv.fork (.Log ⟨n⟩)
  + MachineState.memExpansionDelta s.activeWords.toNat offset.toNat size.toNat
  + Gas.logDataCost size

end EVM
end EvmSemantics
