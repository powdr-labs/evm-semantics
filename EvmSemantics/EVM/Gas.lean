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
    -- EIP-150 (Tangerine Whistle), 700 by EIP-1884 (Istanbul), warm-100
    -- by EIP-2929 (Berlin; access-list cold price not yet modelled).
    | .BALANCE | .EXTCODEHASH                                =>
      if fork.atLeast .Berlin     then 100
      else if fork.atLeast .Istanbul then 700
      else if fork.atLeast .EIP150 then 400
      else                              20
    -- EXTCODESIZE / EXTCODECOPY: 20 Frontier/Homestead, raised to 700 by
    -- EIP-150, warm-100 by EIP-2929 (Berlin). EXTCODECOPY also pays
    -- per-word `Gas.copyWordCost`, charged dynamically in
    -- `stepF.EXTCODECOPY`.
    | .EXTCODESIZE | .EXTCODECOPY                            =>
      if fork.atLeast .Berlin     then 100
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
    -- (Tangerine Whistle), 800 by EIP-1884 (Istanbul), then reduced
    -- to warm-100 by EIP-2929 (Berlin; we use the warm price since
    -- the access list isn't tracked yet).
    | .SLOAD                                                 =>
      if fork.atLeast .Berlin     then 100
      else if fork.atLeast .Istanbul then 800
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
    -- 700 by EIP-150 (Tangerine Whistle), reduced to warm-100 by
    -- EIP-2929 (Berlin). We don't yet track the access list so we use
    -- the warm price everywhere from Berlin onwards. The
    -- value/new-account surcharge and gas forwarding are computed in
    -- `stepF.system` / `StepRunning.call`, not here.
    | .CALL | .CALLCODE | .DELEGATECALL | .STATICCALL        =>
      if fork.atLeast .Berlin     then 100
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
  -- EIP-2200 activated the stipend sentry at Istanbul; it remains in
  -- effect through Cancun (the original Constantinople EIP-1283 did
  -- *not* have one — that was the point of EIP-2200's revision).
  if fork.atLeast .Istanbul then decide (gas ≤ 2300) else false

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
  -- Original Constantinople activated EIP-1283 net-metered SSTORE.
  if fork = .Constantinople then
    if current.toNat = new.toNat then 200
    else if current.toNat = original.toNat then
      if original.toNat = 0 then 20000 else 5000
    else 200
  -- Istanbul onwards uses EIP-2200 net-metered with 800 no-op (the
  -- SLOAD-cost). EIP-2929 cold/warm (Berlin+) adds 2100 to the first
  -- access of the tx; we don't yet track that and use the warm price
  -- everywhere. EIP-3529 (London+) doesn't change `sstoreCost`, only
  -- refund constants.
  else if fork.atLeast .Istanbul then
    if current.toNat = new.toNat then 100
    else if current.toNat = original.toNat then
      if original.toNat = 0 then 20000 else 2900
    else 100
  -- Frontier through Petersburg (and our `Petersburg` = ConstFix) use
  -- the pre-EIP-1283 schedule.
  else
    if current.toNat = 0 ∧ new.toNat ≠ 0 then 20000 else 5000

/-- SSTORE refund counter delta — signed delta added to
    `Substate.refundBalance` for one SSTORE writing `new` over `current`
    when the slot's transaction-start value was `original`.

    * **Pre-EIP-1283** (Frontier..Byzantium and Petersburg): +15000 on
      a clear-to-zero, otherwise 0.
    * **EIP-1283** (original Constantinople) / **EIP-2200**
      (Istanbul..Cancun): net-metered. The cancel branches subtract.

    The schedule values change a bit across the net-metered forks
    (Yellow Paper §H.3 / EIP-3529 in London halves the refunds):

    | constant   | EIP-1283 | EIP-2200 | EIP-3529 (London+) |
    |------------|---------:|---------:|-------------------:|
    | `Sclear`   |    15000 |    15000 |               4800 |
    | `Sreset-Hwarm` |  4800 |     4200 |               2800 |
    | `Sset-Hwarm`   | 19800 |    19200 |              19900 |

    (`Hwarm` is 200 on EIP-1283 — pre-EIP-2929 — and 100 from EIP-2200
    onwards, matching the SSTORE no-op cost on each fork.) -/
def Gas.sstoreRefund (fork : Fork) (original current new : UInt256) : Int :=
  let o := original.toNat
  let c := current.toNat
  let n := new.toNat
  if c = n then 0
  else if fork.atLeast .Istanbul ∨ fork = .Constantinople then
    -- Net-metered (EIP-1283 / EIP-2200 / EIP-3529).
    let london := fork.atLeast .London
    let sclear : Int := if london then 4800 else 15000
    let sresetMinusH : Int :=
      if london then 2800
      else if fork.atLeast .Istanbul then 4200
      else 4800   -- EIP-1283 (Constantinople-only)
    let ssetMinusH : Int :=
      if london then 19900
      else if fork.atLeast .Istanbul then 19200
      else 19800  -- EIP-1283
    if o = c then
      if n = 0 then sclear else 0
    else
      -- Dirty branch.
      let r₀ : Int :=
        if c ≠ 0 ∧ n = 0 then sclear
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
    is gated separately in `Gas.selfDestructRefund`). -/
def Gas.refundDenom (fork : Fork) : Nat :=
  if fork.atLeast .London then 5 else 2

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

/-- Cap on the gas a CALL/CREATE may forward to its callee, given the
    caller's gas `g` remaining (after the call's own base/value/
    new-account/memory costs are paid).

    * EIP-150 (Tangerine Whistle) onwards: `g - ⌊g/64⌋` — the "all but
      one 64th" rule. The forwarded gas is always `min(gas_arg, cap)`
      so the caller retains at least `g/64`.
    * Pre-EIP-150 (Frontier, Homestead): **no cap** and the gas argument
      is *not* clipped. If `gas_arg > g`, the CALL OOGs (EIP-150
      introduced the cap specifically to prevent this).

    `Gas.forwardGas fork g gas_arg` packages both rules into one
    "forwarded amount" — callers then check `forwarded ≤ g` to detect
    the pre-EIP-150 OOG path. -/
def Gas.allButOneSixtyFourth (fork : Fork) (g : Nat) : Nat :=
  if fork.atLeast .EIP150 then g - g / 64 else g

/-- Compute the actual gas forwarded to a callee. From EIP-150 onwards
    this is `min(gas_arg, allButOneSixtyFourth g)`. Pre-EIP-150 there is
    no cap — the gas argument is used verbatim, and if it exceeds `g`
    the caller will fail the subsequent `forwarded ≤ gasAvailable`
    check and the CALL OOGs. -/
def Gas.forwardGas (fork : Fork) (g gas_arg : Nat) : Nat :=
  if fork.atLeast .EIP150 then Nat.min gas_arg (g - g / 64)
  else gas_arg

/-- The stipend (`G_callstipend = 2300`) added to the gas a callee receives
    when a non-zero `value` is transferred — it is *given* to the callee on top
    of the forwarded gas (funded by the `G_callvalue` surcharge), not charged to
    the caller again. -/
def Gas.callStipend : Nat := 2300

/-- EIP-2929 cold-access surcharge added on top of the warm price for
    Berlin+ forks. Returns 2000 for an account/storage-key access
    that hasn't been touched yet in this transaction, otherwise 0.
    Pre-Berlin always returns 0 — the cold/warm distinction didn't
    exist, the static `baseCost` already encoded the full price.
    The 2000/2500 values are EIP-2929's `COLD_*_COST - WARM_*_COST`:
    `COLD_SLOAD_COST - WARM_STORAGE_READ_COST = 2100 - 100 = 2000`
    for storage, `COLD_ACCOUNT_ACCESS_COST - WARM_STORAGE_READ_COST =
    2600 - 100 = 2500` for accounts. -/
@[inline] def Gas.coldSloadExtra (fork : Fork) (warm : Bool) : Nat :=
  if fork.atLeast .Berlin ∧ !warm then 2000 else 0

@[inline] def Gas.coldAccountExtra (fork : Fork) (warm : Bool) : Nat :=
  if fork.atLeast .Berlin ∧ !warm then 2500 else 0

/-- The dynamic surcharge a CALL pays on top of its base fee.

    * `G_callvalue = 9000` for a value-transferring CALL (`valueNonZero`).
    * `G_newaccount = 25000` when the call brings a previously empty
      account into existence. The "into existence" condition is fork-gated:
      - Pre-EIP-158 (`Frontier`, `Homestead`, `EIP150`): charged whenever
        the target is empty, even with `value = 0` — the legacy rule is
        that any CALL to a non-existent account creates one.
      - From EIP-158 (Spurious Dragon) onwards: charged only when the
        target is empty AND the value transfer is non-zero (i.e. only
        when the transfer actually delivers wei to a fresh account). -/
def Gas.callSurcharge (fork : Fork) (valueNonZero targetEmpty : Bool) : Nat :=
  let valSurcharge : Nat := if valueNonZero then 9000 else 0
  let newSurcharge : Nat :=
    if fork.atLeast .EIP158 then
      if valueNonZero && targetEmpty then 25000 else 0
    else
      if targetEmpty then 25000 else 0
  valSurcharge + newSurcharge

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
  -- London (EIP-3529) removed the SELFDESTRUCT refund entirely.
  if fork.atLeast .London then 0 else 24000

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
