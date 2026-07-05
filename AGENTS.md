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
lake build evm_semantics vmtests statetests gstatetests txtests blockchaintests blockchaintests_engine rlptests trietests  # all runner binaries — what CI builds
lake exe cache get                  # fetch Mathlib prebuilt oleans (after `lake update`)
lake lint                           # Batteries runLinter over the EvmSemantics namespace
.lake/build/bin/evm_semantics       # run the demo (PUSH1 5; PUSH1 3; ADD; STOP -> [8])
.lake/build/bin/vmtests <corpus>    # legacy VMTests conformance suite
.lake/build/bin/statetests <dir>    # legacy BlockchainTests/GeneralStateTests
.lake/build/bin/gstatetests <dir>   # MODERN ethereum/tests GeneralStateTests (state_test fixtures; also EEST Osaka)
.lake/build/bin/txtests <dir>       # TransactionTests + EEST transaction_tests (decode/validate only)
.lake/build/bin/blockchaintests <dir> # EEST blockchain_tests (full chain execution + consensus)
.lake/build/bin/blockchaintests_engine <dir> # EEST blockchain_tests_engine (same chains via Engine-API newPayload; RLP tx decode + sender recovery)
.lake/build/bin/rlptests <dir>      # ethereum/tests RLPTests (RLP codec conformance)
.lake/build/bin/trietests <dir>     # ethereum/tests TrieTests (MPT root conformance)
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
  `StepRunning.stop` has no `h_gas`/`h_stack`, and stackless reads
  (`address`, `coinbase`, `pc`, …) have no `h_stack`. **Exception:**
  `StepRunning.pushN` is the one success rule that uses the full
  `s.decoded` premise, because it consumes the PUSH immediate. The
  gas premise on each rule is a **bundled** `Nat`-valued total
  (`Gas.<op>Total s ...` for opcodes with dynamic costs, plain
  `Gas.baseCost s.fork op` for opcodes that have only the static fee),
  and the post-state is a flat `{ s with ... }` record update that uses
  the same total as `gasAvailable := s.gasAvailable - Gas.<op>Total ...`.
- **`Eval : State → ExecutionResult → Prop`** (`EVM/BigStep.lean`) — big-step,
  the reflexive-transitive closure `Steps` ending in a halted state, projected
  by `State.toResult` to `success | returned _ | reverted _ | exception _`.
- **`stepF : State → Except ExecutionException State`** (`EVM/StepF.lean`) —
  executable shadow, mirroring `Step` opcode-by-opcode. Split into per-group
  helpers (`stepF.stopArith`, `stepF.compBit`, …) so each is small.
- **`EVM/Equiv.lean`** — `stepF_sound : ¬ s.isDone → Step s (stepF s)`,
  closed. `stepF` is total (exceptions fold into `halt := .Exception e`);
  soundness covers both the success and exception directions, layered as
  14 per-helper soundness lemmas (+ `*_sound_error` mirrors) dispatched
  from the headline theorem. Every `OutOfGas` derivation is bounded by the
  exact per-op `Gas.totalCost`.

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
top-level abort. `SELFDESTRUCT`, `CREATE`, and `CREATE2` are also
implemented: SELFDESTRUCT does balance burn-on-self + scheduled deletion
via `Substate.selfDestructSet`; CREATE/CREATE2 enter an init-code frame
marked by `Frame.createAddr := some newAddr`, with a dedicated
`resumeCreateSuccess` rule that installs `hReturn` as the new code
(charged at `G_codedeposit = 200` per byte). Address derivation uses a
minimal RLP encoder (`EvmSemantics.Rlp`) for CREATE and a raw keccak
preimage for CREATE2. Transaction processing (YP `Υ`) lives in
`EvmSemantics.Tx`. The YP §9 precompile dispatcher lives in
`EvmSemantics.EVM.Precompile`; **0x04 `identity`** is implemented.
Dispatch happens at the *frame entry* layer — every `ExecutionEnv`
carries a `codeAddr` (the borrowed-from address, distinct from
`address` for `CALLCODE` / `DELEGATECALL`), and a single arm at the
top of `stepF`'s running branch fires the precompile whenever
`Precompile.isPrecompile fork codeAddr` is `true`. The same arm
covers tx-to-precompile transactions (where `Tx.buildInitState`
sets `codeAddr := tx.recipient`) without any special case in
`Tx.execute`. The spec side mirrors this with two generic Step
rules (`Step.precompileSuccess` / `precompileOog`) plus an
exclusivity gate on `Step.running` (`isPrecompile fork codeAddr =
false`) so the bytecode rules and precompile rules are mutually
exclusive at the relation level. `Precompile.run` takes the
`isPrecompile` proof as a precondition, so its `Result` only has
`.success` / `.outOfGas` — no `.notAPrecompile` arm. The full precompile
set is implemented (`0x01`–`0x09`, plus `0x0A` KZG point evaluation and
the `0x0B`+ BLS12-381 set). Block validation is covered by the EEST
`blockchain_tests` job (chain execution + consensus); the
`blockchain_tests_engine` job additionally decodes raw-RLP txs from
Engine-API `newPayload` envelopes and ECDSA-recovers the sender (and each
EIP-7702 authority).

**Known gaps** (tracked in `VMTESTS.md`):
- **Dynamic gas.** `Gas.baseCost fork op` charges the static Yellow-Paper fee
  per fork; dynamic costs are modelled via `Gas.sstoreCost`, `Gas.copyWordCost`,
  `Gas.keccakWordCost`, `Gas.logDataCost`, `Gas.expByteCost`, the CALL
  value/new-account surcharge (`Gas.callSurcharge`; CALLCODE passes
  `targetEmpty = false` since it never creates an account) plus 63/64
  forwarding (`Gas.allButOneSixtyFourth`), and memory expansion via
  `chargeMem`/`chargeMem2`. **EIP-2929 cold/warm** is modelled from Berlin:
  the `Substate` accessed-account / accessed-storage-key sets drive
  `Gas.{sload,sstore,account}ColdSurcharge`, charged on SLOAD/SSTORE, the
  account-read opcodes (`BALANCE`/`EXTCODESIZE`/`EXTCODEHASH`/`EXTCODECOPY`)
  and the CALL family; `Tx.buildInitState` pre-warms sender/recipient/
  precompiles/coinbase, and `enterCall`/`enterCallFor`/`enterCreate` warm the
  call/create target. Remaining *unmodelled* dynamic costs: EIP-1559 base-fee
  burn, SSTORE gas refunds (EIP-3529), and `Gas.create2HashCost` for
  CREATE2's address-derivation hash. The VMRunner no longer maintains a
  gas-comparable filter — every test runs with its declared
  `exec.gas` budget and (when it has a `post` block) compares the
  remaining-`gas` value against the corpus.

## Adding or changing an opcode

Touch these in order, then rebuild + lint + run vmtests:

1. `EVM/Operation.lean` — the `Operation` constructor (if new).
2. `EVM/Decode.lean` — byte → operation + immediate width.
3. `EVM/Gas.lean` — `Gas.baseCost`. Charge the real static base fee per fork.
   For a *dynamic* cost, follow the established pattern: a fork-aware helper
   (`Gas.copyWordCost`, `Gas.keccakWordCost`, `Gas.logDataCost`, `Gas.expByteCost`,
   `Gas.sstoreCost`) that gets charged in `stepF` via `consumeGas` after
   `chargeMem`. Then define a `Gas.<op>Total` (or `Gas.<op>Committed` for the
   CALL/CREATE families) that bundles `baseCost + memExpansionDelta + dyn`
   into a single `Nat`-valued total — this is what the `StepRunning` rule
   uses on both sides (pre-condition `Gas.<op>Total ≤ s.gasAvailable` and
   post-state `gasAvailable := s.gasAvailable - Gas.<op>Total`). Every
   opcode's gas is now compared against the corpus's expected
   remaining-`gas` value on any with-`post` test; if your dynamic cost
   touches state the harness can't reproduce (e.g. EIP-2929 cold/warm),
   stub it at the value that matches the target corpus — gas-mismatch
   failures will surface immediately if you pick wrong.
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
7. `tests/VMRunner.lean` — usually nothing. Every test goes through the
   evaluator with its real `exec.gas` budget; there is no skip filter
   left to update.

## CI gates (`.github/workflows/ci.yml`)

Gating policy: build/lint failures and the curated CALL suite gate every
tier regression; every other suite gates *correctness* regressions — any
test whose new tier is FAIL or CRASH vs its committed baseline fails the
shard — while INCON-tier regressions (walltimeout perf incons flapping
under CPU load) stay warnings-only. A run with no parseable summary also
fails its shard.

1. Build `evm_semantics vmtests statetests gstatetests txtests blockchaintests blockchaintests_engine rlptests trietests`,
   fail on any `warning:`.
2. `lake lint`.
3. VMTests on the full corpus — compares against
   `.github/vmtests-expected-failures.txt` (pinned to `CORPUS_REV`); a
   regression to FAIL/CRASH fails the shard, other regressions surface as
   warnings.
4. StateTests (legacy BlockchainTests/GeneralStateTests, curated subset from
   `ethereum/legacytests`) — compares against
   `.github/statetests-expected-failures.txt`; the CALL-test gate fails the
   build on any tier regression (pass → INCON/FAIL/CRASH, INCON → FAIL/CRASH,
   FAIL → CRASH).
5. Modern GeneralStateTests (`gstatetests`, ~whole corpus from the maintained
   `ethereum/tests` `fixtures_general_state_tests.tgz`, pinned to `TESTS_REV`,
   minus `stTimeConsuming` + internal `VMTests`) — gates FAIL/CRASH
   regressions (INCON-tier stays warnings): driven by the
   per-file subprocess-isolation wrapper `.github/scripts/gstatetests_run.sh` (so
   an OOM/panic in one file is a contained `crash`, not a batch abort) and
   compared against `.github/gstatetests-expected-failures.txt`. Only legacy
   `gasPrice` txs run; typed txs are `INCON`. See `VMTESTS.md`.
6. EEST Osaka `state_tests` (`gstatetests` binary) + EEST `transaction_tests`
   (`txtests` binary), extracted from the `fixtures_develop.tar.gz` release
   pinned by `EEST_REV` — gate FAIL/CRASH regressions; baselines
   `.github/eest-osaka-expected-failures.txt` and
   `.github/eest-txtests-expected-failures.txt`.
7. TransactionTests (`txtests`, `ethereum/tests` sparse checkout, decode+validate
   only) — gates FAIL/CRASH regressions; `.github/txtests-expected-failures.txt`.
8. EEST `blockchain_tests` (`blockchaintests`, full chain execution + consensus,
   pinned by `EEST_REV`) — gates FAIL/CRASH regressions (the walltimeout
   INCON flapping stays warnings-only);
   `.github/blockchaintests-expected-failures.txt`.
9. EEST `blockchain_tests_engine` (`blockchaintests_engine`, the same chains fed
   as Engine-API `newPayload` envelopes — raw-RLP txs decoded with ECDSA sender
   + EIP-7702 authority recovery, pinned by `EEST_REV`) — gates FAIL/CRASH
   regressions; reuses
   the `blockchaintests_{run,summary,check}.sh` scripts via `BLOCKCHAINTESTS_BIN`;
   `.github/blockchaintests-engine-expected-failures.txt`.
10. EEST static + historical `state_tests` (`gstatetests` binary; the maintained
    ports of the full legacy corpus, filled through Osaka, minus `osaka/` —
    covered by job 6 — and minus `static/state_tests/{stTimeConsuming,VMTests}`,
    pinned by `EEST_REV`) — gates FAIL/CRASH regressions;
    `.github/eest-static-expected-failures.txt`.
11. `ethereum/tests` RLPTests (`rlptests`) + TrieTests (`trietests`) — direct
    RLP-codec and MPT-root conformance, sparse checkout pinned by `TESTS_REV` —
    gate FAIL/CRASH regressions; reuse `txtests_{run,summary}.sh` via `TXTESTS_BIN` with
    per-suite check scripts; `.github/rlptests-expected-failures.txt` and
    `.github/trietests-expected-failures.txt`.

Current state of all baselines: **zero correctness fails and zero crashes**
across every suite. The only committed non-passing entries are 7 report-only
VMTests incons (single-frame evaluator gaps), 2 `*_walltimeout` perf incons in
each of the two blockchain suites and the EEST static suite (same two tests),
and 1 out-of-scope trie-iterator incon (`trietestnextprev`). See `VMTESTS.md`
for the status table.

The expected-failures files list one entry per non-passing test in the form
`<test_id>: <FAIL|INCON|CRASH>` sorted alphabetically, with no aggregate counts.
Merges stay conflict-free because fixing a test removes exactly one line at a
known sorted position and adding a new failure inserts one, with no shared
"counter" lines that different branches both touch.
