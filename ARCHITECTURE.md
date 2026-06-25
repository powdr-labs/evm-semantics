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
`sorry`, so any concrete run of `stepF` is backed by a derivation in the
relational spec.

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
        Gas["EVM/Gas.lean<br/>Gas.cost : Operation → Nat"]
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
- **`Gas.lean`** — `Gas.cost : Operation → Nat`. Fixed-cost opcodes are faithful
  to the fee schedule; dynamic ones are stubbed at a base cost with a
  `TODO(dynamic)` marker (see `AGENTS.md` / `VMTESTS.md` for which).
- **`Halted.lean`** — `ExecutionResult` and `State.toResult`, projecting a
  halted `State` into the flat success/returned/reverted/exception sum.

**Semantics** — see the next two sections.

**Executables**
- **`Main.lean`** — `initState` + a `partial def run` fuel loop over `stepF`;
  the demo runs `PUSH1 5; PUSH1 3; ADD; STOP`.
- **`VMRunner.lean`** (exe `vmtests`) — the conformance harness; see below.

## Data flow of one execution step

`stepF` (and the relation `Step` it shadows) turn one running `State` into the
next. The flow:

```mermaid
flowchart TD
    Start([State s]) --> Halt{s.halt = Running?}
    Halt -->|no| Done([return s unchanged])
    Halt -->|yes| Dec["decodeAt code pc<br/>(Decode.lean)"]
    Dec -->|none / past end| Stop["halt = Success<br/>(implicit STOP)"]
    Dec -->|"some (op, imm)"| GasChk{"Gas.cost op<br/>≤ gasAvailable?"}
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
the soundness lemmas in `Equiv.lean`. Neither `stepF` nor `Step` loops on its
own; iteration to a halt is the `run` fuel loop in each executable.

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
  explicitly: `h_op` (decoded operation), `h_running`, `h_gas`
  (`Gas.cost op ≤ gasAvailable.toNat`), and the `h_stack` shape. `consumeGas`
  takes the gas-sufficiency proof as an argument so the saturating subtraction
  is provably safe. `keccak256` is an `opaque` function here. Halted states have
  no successors (`Step.not_from_halted`).
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
   has a faithful fixed cost; otherwise *gas-ignored* (inject `hugeGas = 2^63`,
   never compare gas). Unsupported opcodes (CALL/CREATE family, SELFDESTRUCT)
   and keccak-dependent tests are skipped here.
3. **Run** to a halt, then **compare** (`cmpAccounts`) storage, return-data,
   balance, and nonce against the expected post-state, producing an `Outcome`
   (`pass` / `fail` / `skip` / `incon` / `crash`).
4. **Aggregate** into a `Tally`. The parent process fans tests out across child
   processes (`--file` mode, `parentMain`/`runDir`) so a single panic or timeout
   loses only that test.

CI runs the full suite non-gating against `.github/vmtests-baseline.txt`. See
`VMTESTS.md` for results, gas-mode details, and the known evaluator gaps the
suite surfaces.
