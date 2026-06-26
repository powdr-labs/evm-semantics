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
        ExecEnv["State/ExecutionEnv.lean<br/>ExecutionEnv I<br/>(code · calldata · sender · header)"]
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
        Step["EVM/Step.lean<br/>Step relation (small-step Prop)<br/>90 constructors"]
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
  calldata, sender/source/owner, value, gas price, header, depth,
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
  decodes as `STOP` (Yellow-Paper zero-padding).
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
  - `Gas.allButOneSixtyFourth gas` — EIP-150 forwarding cap (`gas - gas/64`).
  Memory expansion gas is charged separately by `stepF.chargeMem` /
  `chargeMem2`. The only remaining dynamic costs we don't yet model are
  the EIP-2929 cold/warm split on `BALANCE` / `EXTCODESIZE` / `EXTCODECOPY` /
  `EXTCODEHASH` (these are stubbed at `1` / `100` with a `TODO` comment
  pending an `accessedAccounts` set in `Substate`) and the out-of-scope
  CALLCODE / DELEGATECALL / STATICCALL / CREATE / SELFDESTRUCT family.
  `VMRunner.gasComparableOpcode` is the actual gate for which tests can
  be gas-checked. See `VMTESTS.md` for the breakdown.
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

`CALL` is the only inter-contract opcode currently implemented; it lives in
`stepF.system`'s `.CALL` arm with a matching `Step.call` / `Step.callFail` /
`Step.callStatic` triple. Call-frame state is kept on a per-`State`
`callStack : List Frame` (defined in `State.lean`): each `Frame` snapshots
the caller's `pc`, `stack`, `gasAvailable`, `activeWords`, `memory`,
`returnData`, `executionEnv`, the `retOffset`/`retSize` window the caller
asked for, and the world snapshot (`snapAccountMap`, `snapSubstate`) used to
roll back on revert / exception.

The `CALL` arm fires in this order:

1. **Static-mode check** — if `¬ permitStateMutation ∧ value ≠ 0`, halt with
   `.StaticModeViolation` (mirrored by `Step.callStatic`). Zero-value CALLs
   remain permitted in static frames.
2. **Memory expansion** — `chargeMem2` for the union of the args range and
   the return range.
3. **Surcharge** — `Gas.callSurcharge` (9000 if value ≠ 0; +25000 if calling
   an empty account).
4. **Depth/balance pre-check** — if `depth ≥ 1024 ∨ caller.balance < value`,
   the call is *not taken*: push `0`, clear `returnData`, advance PC, keep
   the unspent forwarded gas. (`Step.callFail`.)
5. **63/64 forwarding** — `Gas.allButOneSixtyFourth` caps the gas the callee
   receives; the value stipend is added for non-zero-value calls.
6. **Enter callee** — `State.enterCall` snapshots the caller frame onto
   `callStack`, transfers `value`, installs the callee env, and clears
   `memory` / `returnData` / `hReturn`.

When the callee halts the *active frame's* `halt` becomes non-`Running` but
`callStack` is still non-empty — `stepF`'s halt arm calls `State.resumeByHalt`
to dispatch on the callee's halt kind:

| callee `halt` | rule              | flag | return data        | world         |
|---------------|-------------------|:----:|--------------------|---------------|
| `.Success`    | `resumeSuccess`   | `1`  | `child.hReturn`    | keep child's  |
| `.Returned`   | `resumeSuccess`   | `1`  | `child.hReturn`    | keep child's  |
| `.Reverted`   | `resumeRevert`    | `0`  | `child.hReturn`    | snapshot      |
| `.Exception _`| `resumeException` | `0`  | `∅`                | snapshot      |

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

- **`Step`** (`EVM/Step.lean`) — each success constructor names its premises
  explicitly. The typical shape is `h_op` (decoded operation), `h_running`,
  `h_gas` (`Gas.baseCost s.fork op ≤ s.gasAvailable`, a `Nat` `≤`), and an `h_stack` shape,
  but it varies: `Step.stop` carries no `h_gas`/`h_stack` (while
  `RETURN`/`REVERT` keep `h_gas`/`h_stack`/`h_mem`) and stackless reads omit
  `h_stack`. `consumeGas` takes the gas-sufficiency proof
  as an argument so the saturating subtraction is provably safe. `keccak256`
  is declared `opaque` in `Crypto/Keccak256.lean` (so the relational rules
  are independent of any particular hash); the executable evaluator runs
  the real Keccak-256 thanks to a sibling `@[implemented_by keccak256Impl]`
  attribute that points at the self-contained implementation in
  `Crypto/Keccak256.lean`. Halted states have no successors
  (`Step.not_from_halted`).
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
2. **Pre-scan the bytecode** (`scanCode` + `gasComparableOpcode` /
   `skipReasonOf`) to pick a gas mode and decide skips: *gas-checked* (run with
   the real `exec.gas` budget and compare the remaining `gas`) when every opcode
   has a faithful gas cost in our schedule; otherwise *gas-ignored* (inject
   `hugeGas = 2^63`, never compare gas). The CALL family / CREATE family /
   SELFDESTRUCT are skipped outright by `skipReasonOf`; KECCAK256 /
   EXTCODEHASH now run (real Keccak-256 is wired in via
   `Crypto/Keccak256.lean`). Plain `CALL` is implemented in the evaluator
   but the VMTests harness still skips it here pending gas-comparison
   support; the separate `statetests` exe (`StateTestRunner.lean`) is the
   one that exercises `CALL` against the `stCall*` BlockchainTests.
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
