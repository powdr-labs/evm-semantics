# AGENTS.md

Agent-oriented guide to **EvmSemantics** — a relational small-step / big-step
semantics of the EVM in Lean 4, expressed as `Prop`-valued inductive relations
(not executable functions) with an executable shadow proven sound against them.

This file is the shared context for the project skills under
`.claude/skills/`. For prose depth, see `README.md` (design overview) and
`VMTESTS.md` (the conformance harness). This file stays terse and operational.

## Commands

```sh
lake build                          # build library + all executables
lake build evm_semantics vmtests    # build just the two binaries CI builds
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
  ~89 constructors: one success constructor per opcode plus generic exception
  constructors. Every success constructor carries `h_running : s.halt =
  .Running` and `h_gas : Gas.cost op ≤ s.gasAvailable.toNat` premises;
  `consumeGas` takes the gas-sufficiency proof explicitly so Nat subtraction is
  provably safe.
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
Data/Stack.lean Data/UInt256.lean          -- list stack (popₙ/exchange); 256-bit modular words
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

**Known gaps** (tracked in `VMTESTS.md`): push-data-aware jumpdest validation,
executable `StackOverflow` (only the relation enforces the 1024 cap), concrete
Keccak (`keccak256` is `opaque`, returns 0), and dynamic gas costs (SSTORE/cold-
warm/per-word add-ons are stubbed at cost 1 with `TODO(dynamic)` in `Gas.lean`).

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

## CI gates (`.github/workflows/ci.yml`)

1. Build `evm_semantics vmtests`, fail on any `warning:`.
2. `lake lint`.
3. VMTests on the full corpus — **non-gating**: compares against
   `.github/vmtests-baseline.txt` (pinned to `CORPUS_REV`) and surfaces
   regressions as warnings without blocking the merge.
