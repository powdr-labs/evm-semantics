# Summary of changes for run 9ed53cf3-3975-4208-8524-1d5a93dcb2a3
Determined that the small-step relation `EvmSemantics.EVM.Step` (the `Step.running`/`Step.returning` wrapper around `StepRunning`/`StepReturn`) is **not deterministic**, and delivered a machine-checked Lean proof.

What was added:
- New file `EvmSemantics/EVM/StepDeterminism.lean` (namespace `EvmSemantics.EVM`) containing:
  - `underdeterminedState`, a fully concrete `State`: the default state with its bytecode overridden to the single byte `0x01` (the `ADD` opcode). All other fields keep their defaults — `halt = .Running`, `stack = []`, `gasAvailable = 0`, and the zero `codeAddr` (not a precompile).
  - `theorem step_not_deterministic : ∃ (s s₁ s₂ : State), Step s s₁ ∧ Step s s₂ ∧ s₁ ≠ s₂`, proved with this explicit witness.
  - A doc-comment explaining the overlap in plain English: on this running, non-precompile frame both `StepRunning.stackUnderflow` (ADD has `popArity = 2` > stack length `0`, giving `halt := .Exception .StackUnderflow`) and `StepRunning.outOfGas` (cost witness `1`, with `gasAvailable = 0 < 1`, giving `halt := .Exception .OutOfGas`) fire. Both lift through `Step.running` (whose `s.halt = .Running` and `isPrecompile … = false` premises hold), and the two successors differ in their `halt` field, so they are unequal.
  - A trailing `#print axioms EvmSemantics.EVM.step_not_deterministic`, whose footprint is only `[propext, Classical.choice, Quot.sound]`.
- Registered the file in the library root `EvmSemantics.lean` by adding one `public import` line.

Verification:
- `lake build` completes cleanly (full default target, 1084 jobs), with no new warnings and no lines over the 100-column style limit.
- The file contains no `sorry`, `admit`, or new `axiom`; the theorem depends only on the three standard allowed axioms.
- No existing definitions, relations, or proofs were modified; the only touched existing source file is `EvmSemantics.lean` (import line).

Environment note: the sandbox shipped with stale vendored dependencies inconsistent with the project's declared toolchain, so the project would not build as delivered. I restored the dependency resolution recorded in `lake-manifest.json` to match `lakefile.toml`/`lean-toolchain`, which is what makes the whole project (and the new file) build. This lockfile update is the only non-source change.

The optional restricted-determinism salvage lemma was intentionally not included, per the guidance to keep the sorry-free main deliverable safe.