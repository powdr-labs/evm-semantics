# Architecture

How the **EvmSemantics** codebase is organized and what happens where. For the
operational quick-reference (commands, conventions, opcode-change checklist) see
`AGENTS.md`; for the conformance harness see `VMTESTS.md`. This document explains
the *structure* — the layers, the data flow of an execution step, and the
three-views-plus-soundness design at the heart of the project.

## The big idea

The project defines EVM execution **three times** and proves the executable
definition agrees with the relational one:

- **`Step`** — a `Prop`-valued small-step relation (the *specification*, the
  source of truth).
- **`Eval`** — a big-step relation built as the reflexive-transitive closure of
  `Step`, projected to a flat result.
- **`stepF`** — an `Except`-valued *executable* function shadowing `Step`
  opcode-by-opcode (the thing the demo and the test harness actually run).

`EVM/Equiv.lean` closes `stepF_sound : stepF s = .ok s' → Step s s'` with no
`sorry`, so any *successful* `stepF` step is backed by a derivation in the
relational spec. This covers only the `.ok s'` path — `stepF`'s `.error`
(exception) results are **not** in general matched by a `Step` successor; the
memory-expansion `OutOfGas` case (`chargeMem` → `.error`, with no Step-side
memory-OOG rule) is a current example.

## Module layers

Modules form a clean dependency stack — foundation → state → machine → EVM core
→ semantics → executables. Everything is re-exported through the root
`EvmSemantics.lean`.

```mermaid
graph TD
    subgraph Foundation
        UInt256["Data/UInt256.lean<br/>256-bit modular words,<br/>arith · bitwise · expFast"]
    end

    subgraph "State (world + frame pieces)"
        Account["State/Account.lean<br/>AccountAddress=Fin 2^160,<br/>Storage · Account · AccountMap<br/>(function-backed maps)"]
        BlockHeader["State/BlockHeader.lean<br/>BlockHeader (block context)"]
        ExecEnv["State/ExecutionEnv.lean<br/>ExecutionEnv I<br/>(code · calldata · origin · header)"]
        Substate["State/Substate.lean<br/>Substate A<br/>(logs · accessed sets · refunds)"]
    end

    subgraph Machine
        MachineState["Machine/MachineState.lean<br/>MachineState μ<br/>(gas · memory · returnData),<br/>mload/mstore/mcopy · memCost"]
        SharedState["Machine/SharedState.lean<br/>SharedState = μ + world<br/>(accountMap · substate · env)"]
    end

    subgraph "EVM core"
        Operation["EVM/Operation.lean<br/>Operation ADT (grouped)<br/>+ match_pattern abbrevs"]
        Exception["EVM/Exception.lean<br/>ExecutionException"]
        State["EVM/State.lean<br/>EVM.State = SharedState<br/>+ pc · stack · halt"]
        Decode["EVM/Decode.lean<br/>byte → Operation + immediate<br/>(end-of-code ⇒ STOP)"]
        Gas["EVM/Gas.lean<br/>Gas.baseCost : Fork → Operation → Nat"]
        Halted["EVM/Halted.lean<br/>ExecutionResult<br/>+ State.toResult"]
    end

    subgraph "Semantics (three views + proof)"
        Step["EVM/Step.lean<br/>Step wrapper (small-step Prop)<br/>StepRunning opcode rules · StepReturn resume rules"]
        BigStep["EVM/BigStep.lean<br/>Steps (rtc) · Eval (big-step)"]
        StepF["EVM/StepF.lean<br/>stepF executable shadow<br/>+ 14 per-group helpers"]
        Equiv["EVM/Equiv.lean<br/>stepF_sound (no sorry)<br/>+ 14 helper lemmas"]
    end

    subgraph Executables
        Main["Main.lean<br/>demo: run = fuel loop over stepF"]
        VMRunner["VMRunner.lean (exe vmtests)<br/>JSON harness + fuel loop"]
    end

    UInt256 --> Account & BlockHeader & ExecEnv & Substate & MachineState
    Account --> BlockHeader & ExecEnv & Substate & SharedState
    BlockHeader --> ExecEnv
    ExecEnv --> SharedState
    Substate --> SharedState
    MachineState --> SharedState
    SharedState --> State
    UInt256 --> State
    Exception --> State
    Operation --> Decode & Gas
    UInt256 --> Decode
    State --> Step
    Decode --> Step
    Gas --> Step
    State --> Halted
    Step --> BigStep & StepF
    Halted --> BigStep
    Step --> Equiv
    StepF --> Equiv
    BigStep --> Equiv
    Step -.->|re-export| Main
    StepF --> Main & VMRunner
```

### What each module owns

**Foundation**
- **`Data/UInt256.lean`** — the 256-bit word `UInt256` (a wrapper over
  `Fin (2^256)`) with modular `add/sub/mul/div/mod/addMod/mulMod`, bitwise
  `land/lor/xor/lnot/shiftLeft/shiftRight`, and two exponentiations: `exp`
  (the clean `a^b % 2^256` *spec*, used by `Step`) and `expFast` (modular
  fast-exponentiation, used by `stepF`), with `expFast_eq_exp` proving them
  equal. There is **no separate `Stack` module** — the operand stack is just
  `List UInt256`.

**State (world + per-frame pieces)** — all maps are *functions*, not hash maps,
trading enumerability for clean algebraic reasoning (`Function.update`, `simp`):
- **`Account.lean`** — `AccountAddress = Fin (2^160)`, `Storage = UInt256 →
  UInt256`, the `Account` record, and `AccountMap = AccountAddress → Account`,
  each with `get`/`set` and `@[simp]` get-set lemmas.
- **`BlockHeader.lean`** — the block-context fields BLOCK opcodes read.
- **`ExecutionEnv.lean`** — the immutable per-frame environment `I` (code,
  calldata, origin/caller/address, value, gas price, header, depth,
  `permitStateMutation` for static-call detection).
- **`Substate.lean`** — the accrued substate `A`: `LogSeries`, accessed-account
  and accessed-storage-key sets (`AddressSet`/`StorageKeySet`, also functions to
  `Prop`), and refund counter.

**Machine**
- **`MachineState.lean`** — the machine state `μ`: `gasAvailable`, `memory`
  (a `ByteArray`), `activeWords`, `returnData`, `hReturn`. Owns memory access
  (`mload`/`mstore`/`mstore8`/`mcopy`, `readPadded` with zero-padding) and the
  Yellow-Paper quadratic memory-cost machinery (`memCost`,
  `memExpansionDelta`).
- **`SharedState.lean`** — bundles `MachineState` with the world (`accountMap`,
  `substate`, `executionEnv`) via `extends`.

**EVM core**
- **`Operation.lean`** — the `Operation` ADT, deliberately *grouped* into
  sub-inductives (`StopArithOps`, `CompareBitwiseOps`, `KeccakOps`, `EnvOps`,
  `BlockOps`, `StackMemFlowOps`, `SystemOps`) and structs (`PushOp`, `DupOp`,
  `SwapOp`, `DupNOp`, `SwapNOp`, `ExchangeOp`, `LogOp`). `@[match_pattern]`
  abbrevs (`STOP`, `ADD`, …) let the rest of the code name flat opcodes while
  the grouping lets `stepF`/`Step`/`Equiv` dispatch per-group. EIP-8024
  `DUPN`/`SWAPN`/`EXCHANGE` live here.
- **`Exception.lean`** — `ExecutionException` (stack underflow/overflow, OOG,
  invalid jump, static-mode violation, …).
- **`State.lean`** — `EVM.State` extends `SharedState` with `pc`, `stack :
  List UInt256`, `execLength`, and `halt : HaltKind` (`Running | Success |
  Returned | Reverted | Exception e`). Helpers: `replaceStackAndIncrPC`,
  `incrPC`, `haltWith`.
- **`Decode.lean`** — `opcodeOf : UInt8 → Option Operation` and `decodeAt :
  ByteArray → pc → Option (Operation × Option (UInt256 × Nat))` returning the
  operation plus any PUSH immediate (value + width). Reading past code end
  decodes as `STOP` (Yellow-Paper zero-padding). Also `isValidJumpDest :
  ByteArray → Nat → Bool` — the push-data-aware jumpdest analysis used by
  JUMP/JUMPI: scans the code from pc 0, skipping each opcode's immediate
  bytes, and accepts `target` only when it is reached as an instruction
  boundary *and* `code[target] = 0x5b`.
- **`Gas.lean`** — `Gas.baseCost : Fork → Operation → Nat`, the *static*
  per-opcode fee parameterised by the hard fork (`Constantinople` /
  `Cancun`). Alongside, several **dynamic cost** helpers (also fork-aware
  where it matters):
  - `Gas.sstoreCost fork original current new` — pre-EIP-1283 (Constantinople)
    or EIP-2200 net-metered (Cancun);
  - `Gas.copyWordCost size` — `3 · ⌈size/32⌉` for all five copy opcodes;
  - `Gas.keccakWordCost size` — `6 · ⌈size/32⌉` for KECCAK256;
  - `Gas.logDataCost size` — `8 · size` for LOG;
  - `Gas.expByteCost fork exponent` — Frontier (10) or post-Spurious-Dragon
    (50) per exponent byte;
  - `Gas.sstoreSentry fork gas` — the EIP-2200 stipend (≤ 2300 → OOG) for
    Cancun only;
  - `Gas.callSurcharge valueNZ calleeEmpty` — the CALL value/new-account
    surcharge (`9000` if value ≠ 0, `+25000` if calling an empty account);
    CALLCODE passes `calleeEmpty = false` since it never creates an
    account (the code is borrowed; the storage stays with the caller);
  - `Gas.allButOneSixtyFourth gas` — EIP-150 forwarding cap (`gas - gas/64`).
  Memory expansion gas is charged separately by `stepF.chargeMem` /
  `chargeMem2`. The only remaining dynamic costs we don't yet model are
  the EIP-2929 cold/warm split on `BALANCE` / `EXTCODESIZE` / `EXTCODECOPY` /
  `EXTCODEHASH` (these are stubbed at `1` / `100` with a `TODO` comment
  pending an `accessedAccounts` set in `Substate`) and the out-of-scope
  cold/warm split family and the CALL-family dynamic surcharge. The
  legacy ethereum/tests corpus uses Frontier rules for SELFDESTRUCT
  (cost 0, no `G_newaccount` surcharge) — same convention as our
  Frontier-rate SLOAD = 50 and EXP per-byte = 10 — so on the
  `Constantinople` fork `Gas.baseCost .SELFDESTRUCT = 0` and
  `Gas.selfDestructSurcharge .Constantinople _ _ = 0`. Modern values
  (5000 + 25000) live on `Cancun`.
  Every VMTests test runs with its declared `exec.gas` budget; the
  remaining-`gas` value is compared against the corpus whenever a `post`
  block is present. See `VMTESTS.md` for the breakdown.
- **`Halted.lean`** — `ExecutionResult` and `State.toResult`, projecting a
  halted `State` into the flat success/returned/reverted/exception sum.
- **`Fork.lean`** — `inductive Fork = Constantinople | Cancun`; the active
  fork is carried on `ExecutionEnv.fork` and threaded through `Gas.baseCost` /
  `Gas.sstoreCost` / `Gas.expByteCost`.

**Crypto** (`EvmSemantics/Crypto/`)
- **`Keccak256.lean`** — a self-contained implementation of the original
  Keccak hash function (the variant Ethereum uses, delimiter `0x01`, not
  NIST SHA-3's `0x06`): the Keccak-f[1600] permutation (state = 25 ×
  64-bit lanes, 24 rounds of θ-ρ-π-χ-ι), the sponge driver specialised to
  Keccak-256 (rate 1088 bits, capacity 512 bits, 256-bit output), and a
  `keccak256Impl : ByteArray → UInt256` that packs the 32-byte digest
  big-endian. The file then declares `opaque keccak256 : ByteArray →
  UInt256` wired to `keccak256Impl` via `@[implemented_by]`. The
  relational `Step` rules see only the opaque signature, so soundness is
  independent of the hash; the executable `stepF` runs the real thing.

**Semantics** — see the next two sections.

**Executables**
- **`Main.lean`** — `initState` + a `partial def run` fuel loop over `stepF`;
  the demo runs `PUSH1 5; PUSH1 3; ADD; STOP`.
- **`VMRunner.lean`** (exe `vmtests`) — the conformance harness; see below.
- **`KeccakTest.lean`** (exe `keccak_test`) — differential check that our
  `Keccak256` agrees with well-known Ethereum hash vectors (empty input,
  `"abc"`, the ERC-20 `transfer(address,uint256)` selector).

## Data flow of one execution step

`stepF` (and the relation `Step` it shadows) turn one running `State` into the
next; the surrounding `run` loop owns the halt guard, since `stepF` itself just
errors on an already-halted state. The flow of one `run` iteration:

```mermaid
flowchart TD
    Start([run iteration: State s]) --> Halt{s.halt = Running?}
    Halt -->|no| Done([run returns s; loop ends])
    Halt -->|yes| Dec["stepF s → decodeAt code pc<br/>(Decode.lean)"]
    Dec -->|"none: unassigned byte"| Invalid["error InvalidInstruction"]
    Dec -->|"some (op, imm)<br/>(past code end ⇒ STOP)"| GasChk{"Gas.baseCost fork op<br/>≤ gasAvailable?"}
    GasChk -->|no| OOG["error OutOfGas"]
    GasChk -->|yes| Consume["consumeGas<br/>(proof-carrying)"]
    Consume --> Dispatch{"dispatch on<br/>Operation group"}
    Dispatch --> H1["stopArith"]
    Dispatch --> H2["compBit"]
    Dispatch --> H3["env / block"]
    Dispatch --> H4["stackMemFlow<br/>(mem · storage · jumps)"]
    Dispatch --> H5["push/dup/swap/<br/>dupN/swapN/exchange"]
    Dispatch --> H6["log · keccak · system"]
    H1 & H2 & H3 & H4 & H5 & H6 --> Outcome{stack/mem ok?}
    Outcome -->|underflow / bad jump / etc.| Err["error ExecutionException"]
    Outcome -->|ok| Next["ok s' :<br/>new stack/pc/mem/halt"]
```

The dispatch arms map one-to-one to the `stepF.*` helpers in `StepF.lean`
(`stopArith`, `compBit`, `keccak`, `env`, `block`, `stackMemFlow`, `push`,
`dup`, `swap`, `dupN`, `swapN`, `exchange`, `log`, `system`) — and one-to-one to
the soundness lemmas in `Equiv.lean`. The halting opcodes are ordinary `ok s'`
outcomes that set `s'.halt` (STOP ⇒ `Success` in `stopArith`; RETURN/REVERT ⇒
`Returned`/`Reverted` in `system`) — including the implicit STOP from running
off the end of the code. Neither `stepF` nor `Step` loops on its own; iteration
to a halt is the `run` fuel loop in each executable, which is also what skips
already-halted states — `stepF` called directly on a non-`Running` state just
returns `.error .InvalidInstruction`.

## Call frames

All four inter-contract opcodes — `CALL`, `CALLCODE`, `DELEGATECALL`, and
`STATICCALL` — are implemented. They live in `stepF.system`'s matching
arms with `StepRunning.call` / `callFail` / `callStatic`, `callcode` /
`callcodeFail`, `delegatecall` / `delegatecallFail`, and `staticcall` /
`staticcallFail` constructors, all wrapped by `Step.running` in the
combined relation. The four kinds share a common skeleton (see the
`CallKind` enum + `State.calleeEnvFor` / `State.enterCallFor` helpers in
`State.lean`); per-kind differences are isolated to the `calleeCodeOwner`
/ `calleeSource` / `calleeWeiValue` / `calleePermit` / `transfersValue`
projections. Call-frame state is kept on a
per-`State` `callStack : List Frame` (defined in `State.lean`): each `Frame`
snapshots the caller's `pc`, `stack`, `gasAvailable`, `activeWords`, `memory`,
`returnData`, `executionEnv`, the `retOffset`/`retSize` window the caller
asked for, and the world snapshot (`snapAccountMap`, `snapSubstate`) used to
roll back on revert / exception.

The `CALL` arm fires in this order:

1. **Static-mode check** — if `¬ permitStateMutation ∧ value ≠ 0`, halt with
   `.StaticModeViolation` (mirrored by `StepRunning.callStatic`). Zero-value
   CALLs remain permitted in static frames.
2. **Memory expansion** — `chargeMem2` for the union of the args range and
   the return range.
3. **Surcharge** — `Gas.callSurcharge` (9000 if value ≠ 0; +25000 if calling
   an empty account).
4. **Depth/balance pre-check** — if `depth ≥ 1024 ∨ caller.balance < value`,
   the call is *not taken*: push `0`, clear `returnData`, advance PC, keep
   the unspent forwarded gas. (`StepRunning.callFail`.)
5. **63/64 forwarding** — `Gas.allButOneSixtyFourth` caps the gas the callee
   receives; the value stipend is added for non-zero-value calls.
6. **Enter callee** — `State.enterCall` snapshots the caller frame onto
   `callStack`, transfers `value`, installs the callee env, and clears
   `memory` / `returnData` / `hReturn`.

The `CALLCODE` arm runs the same six-step pipeline with three differences:
(1) **no static-mode check** — the "transfer" is caller→caller and the
opcode is therefore not a state mutation at this site (state-mutating
opcodes inside the callee are still rejected because `permitStateMutation`
propagates); (2) **surcharge** passes `targetEmpty = false` — CALLCODE
never creates a new account; (3) **enter callee** passes the caller's own
`address` as the call target, so `enterCall`'s self-transfer is a balance
no-op and the callee's `address` stays the caller, while `calleeCode` is
read from the target account so the borrowed code is what executes.

`DELEGATECALL` and `STATICCALL` both pop *six* stack items (no `value`),
skip the surcharge entirely (`Gas.callSurcharge false false = 0`), perform
no balance / value transfer, and have no `*Static` constructor — they
cannot mutate value directly. They share the same pipeline (memory
expansion → depth-limit pre-check → 63/64 forwarding → `enterCallFor`):
* `DELEGATECALL` sets `CallKind.DelegateCall`: the callee inherits the
  caller's `caller` (msg.sender) and `weiValue` (CALLVALUE), runs in the
  caller's storage context, executes the target's code.
* `STATICCALL` sets `CallKind.StaticCall`: the callee runs in the
  target's context (address = target) but with `permitStateMutation`
  forced to `false`, so any state-mutating opcode in the new frame is
  rejected. `CALLVALUE` is forced to `0`.

## SELFDESTRUCT

`SELFDESTRUCT` lives in `stepF.system .SELFDESTRUCT` with matching
`StepRunning.selfDestruct` / `StepRunning.selfDestructStatic`
constructors. It pops the beneficiary address, rejects under
`permitStateMutation = false`, charges base `G_selfdestruct = 5000`
plus the `Gas.selfDestructSurcharge` (25000 iff the beneficiary is
empty *and* self has non-zero balance), then calls
`State.selfDestructTo`. That helper credits the beneficiary with
self's balance and zeroes self's balance in *credit-then-debit* order
(not `AccountMap.transfer`'s set-then-set, which would net-cancel a
self-beneficiary's update and leave the balance unchanged instead of
burning it). It also marks `self` in `Substate.selfDestructSet` and
adds `R_selfdestruct = 24000` to the refund counter on Constantinople
(`0` on Cancun pending EIP-6780). The frame halts with `.Success`. The
account is *not* deleted at this site — pre-Cancun semantics defer
deletion to end-of-transaction; for our single-tx test corpora the
post-state comparison only enumerates accounts listed in the test's
`post`, so leaving the self-destructed account's storage/code in place
is observably equivalent to immediate deletion.

## CREATE / CREATE2

`CREATE` and `CREATE2` open an *init-code* sub-frame whose `codeOwner`
is the freshly-derived `newAddr` and whose `code` is the init bytes
read from caller memory. The frame is marked on the call stack by a
new field `Frame.createAddr : Option AccountAddress` (`none` for CALL
frames, `some addr` for CREATE frames), and `State.resumeByHalt`
routes the child halt through one of three new CREATE-specific resume
helpers — `resumeCreateSuccess` (deploy `hReturn` as `addr`'s code,
charging `G_codedeposit = 200 · |code|` from the child's remaining gas;
if unaffordable, treat as exception and roll back),
`resumeCreateRevert` (rollback, push `0`, keep `hReturn` as
returnData), and `resumeCreateException` (rollback, push `0`, refund
nothing). The pushed value on success is `addr.toUInt256`, not the
CALL-family `1`/`0` flag.

Address derivation:

* **CREATE:** `keccak256(rlp([sender, sender.nonce]))[12:]`. The RLP
  encoder lives in `EvmSemantics/Data/Rlp.lean` and only handles the
  `[20-byte address, uint nonce]` shape (short-string + short-list
  paths only; the `>55 byte` length-of-length prefixes are not
  reachable here since the encoded list is ≤ 30 bytes).
* **CREATE2:** `keccak256(0xff || sender(20) || salt(32) ||
  keccak256(initcode)(32))[12:]`. CREATE2 additionally pays
  `Gas.create2HashCost size = 6 · ⌈size/32⌉` for the init-code keccak.

The pre-frame pipeline (memory expansion → depth/balance pre-check →
63/64 forwarding → `State.enterCreate`) bumps the caller's nonce by 1
*before* installing the child frame (the address derivation has
already used the pre-bump nonce); transfers `value` to the new
account; sets the new account's nonce to `1` (EIP-161 "exists" marker
so the account isn't `isEmpty`). On `Frame.snapAccountMap` rollback,
both the nonce bump and the value transfer are undone.

**Address-collision detection** uses a `Bool`-valued helper
`Account.isContract` (= `code.size != 0 || nonce.toNat != 0`,
stricter than `Account.isEmpty` because balance is excluded — per the
Yellow Paper a pre-funded address with no code and `nonce = 0` is
still a valid creation target). The CREATE / CREATE2 arms dispatch
via `match … .isContract with | true => … | false => …`; on
`true` the caller's nonce is still bumped, `0` is pushed, and no
transfer or frame entry occurs (forwarded gas is also not spent). The
discriminator is `Bool` rather than `Prop` so the Equiv-proof's
`split at h` produces clean `true`/`false` cases instead of going
through a `Decidable` instance for `ByteArray.size = 0` that the
elaborator normalises to `ByteArray = ByteArray.empty` — that
normalisation tangle is what blocked the first attempt.

When the callee halts the *active frame's* `halt` becomes non-`Running` but
`callStack` is still non-empty — `stepF`'s halt arm calls `State.resumeByHalt`
to dispatch on the callee's halt kind:

CALL-family frames (`Frame.createAddr = none`):

| callee `halt` | rule              | flag | return data        | world         |
|---------------|-------------------|:----:|--------------------|---------------|
| `.Success`    | `resumeSuccess`   | `1`  | `child.hReturn`    | keep child's  |
| `.Returned`   | `resumeSuccess`   | `1`  | `child.hReturn`    | keep child's  |
| `.Reverted`   | `resumeRevert`    | `0`  | `child.hReturn`    | snapshot      |
| `.Exception _`| `resumeException` | `0`  | `∅`                | snapshot      |

CREATE-family frames (`Frame.createAddr = some addr`):

| callee `halt` | rule                     | pushed     | return data     | world after                                                       |
|---------------|--------------------------|:----------:|-----------------|-------------------------------------------------------------------|
| `.Success`    | `resumeCreateSuccess`    | `addr`     | `∅`             | child + `addr.code := hReturn` (if `200·|code| ≤ child gas`)      |
| `.Returned`   | `resumeCreateSuccess`    | `addr`     | `∅`             | child + `addr.code := hReturn` (if affordable; else: rollback)    |
| `.Reverted`   | `resumeCreateRevert`     | `0`        | `child.hReturn` | snapshot                                                          |
| `.Exception _`| `resumeCreateException`  | `0`        | `∅`             | snapshot                                                          |

`State.writeReturn` copies `min(retSize, hReturn.size)` bytes back into the
caller's memory — and short-circuits when that count is `0`, so a CALL with
`retSize = 0` and a huge `retOffset` does *not* allocate memory.

An in-frame `Except.error` from `stepF` is treated as a callee-side exception
when `callStack ≠ []`: the `run` loops in `Main.lean`, `VMRunner.lean`, and
`StateTestRunner.lean` all convert it to `{ s with halt := .Exception e }`
and re-enter `stepF` so `resumeException` fires. Only a top-frame error
(`callStack = []`) propagates as a top-level abort.

## The three views and the soundness bridge

```mermaid
flowchart LR
    subgraph "Specification (Prop)"
        Step["Step s s'<br/>small-step relation<br/>EVM/Step.lean"]
        Eval["Eval s result<br/>big-step = rtc of Step<br/>EVM/BigStep.lean"]
        Step -->|"Steps = refl-trans closure,<br/>then toResult"| Eval
    end
    subgraph "Executable (Except)"
        StepF["stepF s : Except _ State<br/>EVM/StepF.lean"]
        Run["run = fuel loop<br/>Main.lean · VMRunner.lean"]
        StepF --> Run
    end
    StepF -.->|"stepF_sound:<br/>stepF s = ok s' → Step s s'<br/>EVM/Equiv.lean (no sorry)"| Step
```

- **`Step`** (`EVM/Step.lean`) — a thin two-constructor wrapper around
  the actual per-opcode relation. `Step.running` guards a `StepRunning`
  derivation with `s.halt = .Running`; `Step.returning` wraps a
  `StepReturn` (each of whose constructors pins a concrete non-`Running`
  halt kind and a non-empty `callStack`). Splitting the running
  precondition out onto the wrapper is what lets the ~90 `StepRunning`
  constructors omit `h_running` entirely.
  - `StepRunning` carries the per-opcode logic. Each success
    constructor names its premises explicitly. The typical shape is
    `h_op : s.decodedOp = some .X` (where `s.decodedOp : Option
    Operation` is the op-only projection of `s.decoded`), `h_gas`
    (`Gas.baseCost s.fork op ≤ s.gasAvailable`, a `Nat` `≤`), and an
    `h_stack` shape, but it varies: `stop` carries no `h_gas`/`h_stack`
    (while `RETURN`/`REVERT` keep `h_gas`/`h_stack`/`h_mem`) and
    stackless reads omit `h_stack`. `pushN` is the one success rule that
    uses the full `s.decoded`, because it consumes the PUSH immediate.
  - `StepReturn` has the three `callReturn*` resume rules.
  - `consumeGas` takes the gas-sufficiency proof as an argument so the
    saturating subtraction is provably safe. `keccak256` is declared
    `opaque` in `Crypto/Keccak256.lean` (so the relational rules are
    independent of any particular hash); the executable evaluator runs
    the real Keccak-256 thanks to a sibling
    `@[implemented_by keccak256Impl]` attribute that points at the
    self-contained implementation in `Crypto/Keccak256.lean`. *Done*
    states (halted with empty call stack) have no successors under
    `Step` (`Step.not_from_done`).
- **`Eval`** (`EVM/BigStep.lean`) — `Steps` is the reflexive-transitive closure;
  `Eval s r` holds when `Steps` reaches a halted state whose `toResult` is `r`.
- **`stepF`** (`EVM/StepF.lean`) — the same opcode logic as a total `Except`
  function, factored into the per-group helpers. `popN`/`popN_correct` recover
  list witnesses (used by `log`); `chargeMem`/`chargeMem2` apply memory-expansion
  gas so a huge offset hits `OutOfGas` before any allocation.
- **`Equiv`** (`EVM/Equiv.lean`) — the bridge. 14 per-helper lemmas
  (`stopArith_sound`, …) each invert a helper's `match` and either apply the
  matching `Step` constructor or derive a contradiction from a `.ok` hypothesis
  on an `.error` path; the headline `stepF_sound` splits on
  halt/decode/gas/operation and dispatches to them. Also exports
  `Eval.halted_inv`.

## The conformance harness (`VMRunner.lean`)

The `vmtests` executable runs the legacy ethereum/tests **VMTests** corpus
against `stepF` via its `run` fuel loop (cap `2_000_000`):

1. **Parse** a test JSON → build the initial `State` (`buildStateWith` /
   `mkAccount`, hex helpers).
2. **Run** every test through `stepF` with the test's declared
   `exec.gas` budget — there is no pre-scan or skip filter. The four
   call-family opcodes (`CALL` / `CALLCODE` / `DELEGATECALL` /
   `STATICCALL`) are implemented in the evaluator; the separate
   `statetests` exe (`StateTestRunner.lean`) exercises them against the
   `stCall*` / `stCallCodes` BlockchainTests.
3. **Run** to a halt, then **compare** (`cmpAccounts`) storage, return-data,
   balance, and nonce against the expected post-state, producing an `Outcome`
   (`pass` / `fail` / `skip` / `incon` / `crash`).
4. **Aggregate** into a `Tally`. `runDir` fans the files out across in-process
   Lean `Task` workers (`IO.asTask`, `-j` / `VMTESTS_JOBS`, default 8) — there is
   **no subprocess isolation**, so a worker that throws is one `crash` but a hard
   panic aborts the whole run; `--file` mode runs a single test in its own
   process for manual isolation.

CI runs the full suite non-gating against `.github/vmtests-baseline.txt`. See
`VMTESTS.md` for results, gas-mode details, and the known evaluator gaps the
suite surfaces.
