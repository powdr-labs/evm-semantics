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

## Architecture

Three views of the same semantics, with `Step` as the source of truth:

- **`Step : State → State → Prop`** (`EVM/Step.lean`) — small-step relation,
  90 constructors (81 success, one per opcode, + 9 generic exception
  constructors parametric over the operation). Every success constructor carries
  `h_running : s.halt = .Running`; most also carry `h_gas : Gas.cost op ≤
  s.gasAvailable` (`gasAvailable : Nat`) and an `h_stack` shape, but the exact
  premises vary — `Step.stop` has no `h_gas`/`h_stack` (whereas
  `Step.return_`/`Step.revert` carry `h_gas`, `h_stack`, and `h_mem`), and
  stackless reads (`address`, `coinbase`, `pc`, …) have no `h_stack`. Read the
  actual constructor; `consumeGas` takes the gas-sufficiency proof
  explicitly so the saturating Nat subtraction is provably safe.
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
EVM/Gas.lean                                -- gas cost (fixed-cost opcodes faithful; dynamic = TODO)
EVM/Exception.lean  EVM/State.lean  EVM/Halted.lean
EVM/Step.lean  EVM/BigStep.lean  EVM/StepF.lean  EVM/Equiv.lean
```

## Scope (v1)

Single-frame EVM: arithmetic, comparison/bitwise, KECCAK256, env/block reads,
memory, storage (incl. transient), stack ops, control flow, halts, LOG0–4,
EIP-8024. **Excluded:** CALL family, CREATE/CREATE2, SELFDESTRUCT, transaction
processing, block validation, precompiles, RLP.

**Known gaps** (tracked in `VMTESTS.md`):
- **Push-data-aware jumpdest validation** — JUMP/JUMPI don't reject a target
  inside PUSH immediate data.
- **Stack 1024 cap is not enforced anywhere** — `stepF` has no cap, and while
  `Step` has a `stackOverflow` constructor, its *success* rules (e.g. `push0`,
  `pushN`) carry no stack-length guard, so a near-full stack admits both a
  successful push and the `stackOverflow` successor. Closing this needs guards
  on the `Step` success rules *and* a check in `stepF`.
- **Concrete Keccak** — `keccak256` is `opaque` and returns 0.
- **Dynamic gas.** `Gas.cost` charges the real base fee for every opcode. Two
  unmodelled kinds: (a) *state-dependent* opcodes (SSTORE/SLOAD, EIP-2929
  cold/warm reads, CALL/CREATE/SELFDESTRUCT) are stubbed at cost `1` with a
  `TODO(dynamic)` comment; (b) *per-word/byte/topic* ops (EXP, `*COPY`, LOG,
  KECCAK256) keep their correct static base with **no** marker. Don't use
  `TODO(dynamic)` as the full list — `VMRunner.gasComparableOpcode` is the gate.

## Adding or changing an opcode

Touch these in order, then rebuild + lint + run vmtests:

1. `EVM/Operation.lean` — the `Operation` constructor (if new).
2. `EVM/Decode.lean` — byte → operation + immediate width.
3. `EVM/Gas.lean` — `Gas.cost`. Use the real fixed cost; if dynamic, leave
   cost and mark `TODO(dynamic)`.
4. `EVM/Step.lean` — the success constructor (follow the `add` anatomy: `h_op`,
   `h_running`, `h_gas`, `h_stack` premises).
5. `EVM/StepF.lean` — the matching arm in the relevant `stepF.*` helper.
6. `EVM/Equiv.lean` — extend the helper's soundness lemma so it still closes.
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
