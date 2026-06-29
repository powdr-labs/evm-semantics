# AGENTS.md

Agent-oriented guide to **EvmSemantics** — a relational small-step / big-step
semantics of the EVM in Lean 4, expressed as `Prop`-valued inductive relations
(not executable functions) with an executable shadow proven sound against them.

This file is the shared context for the project skills under
`.claude/skills/`. For prose depth, see `README.md` (design overview),
`ARCHITECTURE.md` (module layers + data-flow diagrams), and `VMTESTS.md` (the
conformance harness). This file stays terse and operational.

## Commands

```sh
lake build                          # build the default target only (evm_semantics exe + lib)
lake build evm_semantics vmtests    # build both binaries — what CI builds; use this after touching VMRunner
lake exe cache get                  # fetch Mathlib prebuilt oleans (after `lake update`)
lake lint                           # Batteries runLinter over the EvmSemantics namespace
.lake/build/bin/evm_semantics       # run the demo (PUSH1 5; PUSH1 3; ADD; STOP -> [8])
.lake/build/bin/vmtests <corpus>    # run the VMTests conformance suite
```

- Cold build is ~10 min (compiles Mathlib); cached, ~30 s. Always `lake exe
  cache get` before a cold build.
- Toolchain is pinned in `lean-toolchain` (Lean 4.31.0 + Mathlib v4.31.0).

## Non-negotiable conventions

1. **No `sorry`.** The soundness proofs in `EVM/Equiv.lean` are fully closed.
   Do not introduce `sorry` to make the build pass.
2. **Build must be warning-clean.** CI rebuilds and fails on *any* `warning:`
   line. The most common offender is the **100-column line limit** (enforced by
   Mathlib's `linter.style.longLine`, comments and docstrings included). Wrap
   long lines.
3. **`lake lint` must pass.** There is intentionally **no `scripts/nolints.json`
   allow-list** — every Batteries finding (missing docstrings, `simpNF`, unused
   arguments, dangerous instances) is addressed in source. New declarations need
   a docstring; intentional exceptions get an explicit `@[nolint ...]`.
4. **`Step` and `stepF` must stay in lockstep.** Any opcode change touches both
   the relation and the executable shadow, and the soundness lemma must still
   close. See "Adding/changing an opcode" below.
5. **Fix at the right altitude — respect the architecture.** Before changing
   code, understand how it fits the layered design (`Step` as source of truth,
   `stepF` as its executable shadow, the big-step closure, the conformance
   harness — see `ARCHITECTURE.md`). Don't patch a symptom locally when the
   cause belongs in a shared helper, a different layer, or the relation itself.
   A change that papers over a problem in one handler while leaving the same
   gap elsewhere (or that diverges `Step` from `stepF`) is not acceptable.
   When a local fix and an architecturally-correct fix disagree, prefer the
   latter — or surface the trade-off explicitly rather than silently taking
   the shortcut.
6. **Add tests when applicable.** A behavioural change should come with
   coverage that would have caught the bug or that exercises the new path —
   a unit test, a soundness lemma, or a VMTests/StateTest corpus case as
   appropriate (see `VMTESTS.md`). If a change genuinely can't be tested
   (e.g. a pure refactor or a doc edit), say so rather than skipping silently.

## Architecture

Three views of the same semantics, with `Step` as the source of truth:

- **`Step : State → State → Prop`** (`EVM/Step.lean`) — small-step
  relation, split for readability into three inductives:
  - **`StepRunning`** carries the per-opcode logic: 90 constructors (81
    success + 9 generic exception). Constructors **do not** carry an
    `h_running : s.halt = .Running` premise — the running guard lives
    on the `Step.running` wrapper (consumed once).
  - **`StepReturn`** carries the three `callReturn*` resume rules. Each
    pins `h_halt : s.halt = …` and `h_stack : s.callStack = _ :: _`, so
    `StepReturn s s'` alone implies the frame is halted and has
    callers.
  - **`Step`** is the two-constructor wrapper: `running` (guards a
    `StepRunning` with `s.halt = .Running`) and `returning` (wraps a
    `StepReturn`).

  Each `StepRunning` success constructor carries `h_op : s.decodedOp =
  some .X` (the op-only projection of `s.decoded`); most also carry
  `h_gas : Gas.baseCost s.fork op ≤ s.gasAvailable` (`gasAvailable : Nat`)
  and an `h_stack` shape, but the exact premises vary —
  `StepRunning.stop` has no `h_gas`/`h_stack` (whereas
  `return_`/`revert` carry `h_gas`,
  `h_stack`, and `h_mem`), and stackless reads (`address`, `coinbase`,
  `pc`, …) have no `h_stack`. **Exception:** `StepRunning.pushN` is the
  one success rule that uses the full `s.decoded` premise, because it
  consumes the PUSH immediate. Read the actual constructor; `consumeGas`
  takes the gas-sufficiency proof explicitly so the saturating Nat
  subtraction is provably safe.
- **`Eval : State → ExecutionResult → Prop`** (`EVM/BigStep.lean`) — big-step,
  the reflexive-transitive closure `Steps` ending in a halted state, projected
  by `State.toResult` to `success | returned _ | reverted _ | exception _`.
- **`stepF : State → Except ExecutionException State`** (`EVM/StepF.lean`) —
  executable shadow, mirroring `Step` opcode-by-opcode. Split into per-group
  helpers (`stepF.stopArith`, `stepF.compBit`, …) so each is small.
- **`EVM/Equiv.lean`** — `stepF_sound : stepF s = .ok s' → Step s s'`, closed.
  Layered as 14 per-helper soundness lemmas dispatched from the headline
  theorem.

### File layout (`EvmSemantics/`)

```
Data/UInt256.lean                           -- 256-bit modular words (stack is plain List UInt256)
State/{Account,BlockHeader,ExecutionEnv,Substate}.lean  -- world + per-frame env + substate
Machine/{MachineState,SharedState}.lean     -- μ (gas, memory, returnData); world+machine bundle
EVM/Operation.lean                          -- Operation ADT (+ EIP-8024 DUPN/SWAPN/EXCHANGE)
EVM/Decode.lean                             -- byte -> Operation + immediate
EVM/Fork.lean                               -- inductive Fork = Constantinople | Cancun
EVM/Gas.lean                                -- Gas.baseCost (per fork) + dynamic cost helpers
Crypto/Keccak256.lean                       -- self-contained Keccak-f[1600] + opaque keccak256 + @[implemented_by]
EVM/Exception.lean  EVM/State.lean  EVM/Halted.lean
EVM/Step.lean  EVM/BigStep.lean  EVM/StepF.lean  EVM/Equiv.lean
```

## Scope

Multi-frame EVM: arithmetic, comparison/bitwise, KECCAK256, env/block reads,
memory, storage (incl. transient), stack ops, control flow, halts, LOG0–4,
EIP-8024, and the four call-family opcodes **`CALL` / `CALLCODE` /
`DELEGATECALL` / `STATICCALL`** (with a list-backed call-frame stack,
EIP-150 63/64 gas forwarding, value stipend for CALL/CALLCODE,
depth/balance pre-check, and `returnData` clearing on the pre-execution
failure path). Per-kind differences are isolated to the `CallKind` enum
in `State.lean`: `CALL` adds a static-mode value-transfer rejection and
may include the new-account surcharge; `CALLCODE` borrows code and runs
in the caller's context with a self-transfer no-op; `DELEGATECALL`
inherits the caller's `caller` and `weiValue` (no transfer); `STATICCALL`
forces `permitStateMutation = false` in the callee frame. The three
relational `callReturn*` rules cover the success/revert/exception resume
paths and are shared by all four opcodes; `Main.run` /
`StateTestRunner.run` / `VMRunner.run` all convert a subcall
`Except.error` into `resumeException` rather than propagating it as a
top-level abort. `SELFDESTRUCT` is also implemented (base 5000 +
new-account surcharge, balance burn on self-beneficiary, scheduled
deletion via `Substate.selfDestructSet`). **Not yet implemented:** CREATE
/ CREATE2, transaction processing, block validation, precompiles, RLP.

**Known gaps** (tracked in `VMTESTS.md`):
- **Stack 1024 cap is not enforced anywhere** — `stepF` has no cap, and while
  `Step` has a `stackOverflow` constructor, its *success* rules (e.g. `push0`,
  `pushN`) carry no stack-length guard, so a near-full stack admits both a
  successful push and the `stackOverflow` successor. Closing this needs guards
  on the `Step` success rules *and* a check in `stepF`.
- **Dynamic gas.** `Gas.baseCost fork op` charges the static Yellow-Paper fee
  per fork; dynamic costs are modelled via `Gas.sstoreCost`, `Gas.copyWordCost`,
  `Gas.keccakWordCost`, `Gas.logDataCost`, `Gas.expByteCost`, the CALL
  value/new-account surcharge (`Gas.callSurcharge`; CALLCODE passes
  `targetEmpty = false` since it never creates an account) plus 63/64
  forwarding (`Gas.allButOneSixtyFourth`), and memory expansion via
  `chargeMem`/`chargeMem2`. The only *unmodelled* dynamic costs are the
  EIP-2929 cold/warm split on `BALANCE` / `EXTCODESIZE` / `EXTCODECOPY` /
  `EXTCODEHASH` (stubbed at `1`/`100`, needs `accessedAccounts` in `Substate`)
  and the out-of-scope CREATE / CREATE2 family. SELFDESTRUCT is
  modelled (base 5000, `Gas.selfDestructSurcharge`) but marked
  non-gas-comparable pending refund-counter accounting.
  `VMRunner.gasComparableOpcode` is the gate for which tests can be gas-checked.

## Adding or changing an opcode

Touch these in order, then rebuild + lint + run vmtests:

1. `EVM/Operation.lean` — the `Operation` constructor (if new).
2. `EVM/Decode.lean` — byte → operation + immediate width.
3. `EVM/Gas.lean` — `Gas.baseCost`. Charge the real static base fee per fork.
   For a *dynamic* cost, follow the established pattern: a fork-aware helper
   (`Gas.copyWordCost`, `Gas.keccakWordCost`, `Gas.logDataCost`, `Gas.expByteCost`,
   `Gas.sstoreCost`) that gets charged in the handler after the dispatcher's
   `consumeGas baseCost`. If the new dynamic cost touches state the harness
   can't reproduce (e.g. EIP-2929 cold/warm), leave it stubbed at the
   warm-access value and mark it `false` in step 7's `gasComparableOpcode`.
4. `EVM/Step.lean` — the success constructor (in `StepRunning`; follow
   the `add` anatomy: `h_op : s.decodedOp = some .X`, `h_gas`, `h_stack`
   premises — but adjust for the constructor's kind; halts/stackless
   reads omit some, see the `Step` note above. Only `pushN` keeps the
   full `s.decoded`-shaped premise to bind the immediate. Do **not**
   add a `h_running` premise — the running guard lives on `Step.running`).
5. `EVM/StepF.lean` — the matching arm in the relevant `stepF.*` helper.
6. `EVM/Equiv.lean` — extend the helper's soundness lemma so it still
   closes. The helpers produce `StepRunning`; the headline `stepF_sound`
   wraps with `Step.running h_running`.
7. `VMRunner.lean` — update the conformance pre-scan if the opcode's support or
   gas status changed: `skipReasonOf` (skip unsupported opcodes) and
   `gasComparableOpcode`. The latter has a catch-all `| _ => true`, so a new
   opcode with a *dynamic* cost is silently treated as gas-comparable unless you
   add it — and gas-checked runs would then compare bogus `gas`.

## CI gates (`.github/workflows/ci.yml`)

1. Build `evm_semantics vmtests`, fail on any `warning:`.
2. `lake lint`.
3. VMTests on the full corpus — **non-gating**: compares against
   `.github/vmtests-baseline.txt` (pinned to `CORPUS_REV`) and surfaces
   regressions as warnings without blocking the merge.
