module

import EvmSemantics.EVM.Step

/-!
# Determinism of the small-step relation `Step`

This module settles whether the combined small-step relation
`EvmSemantics.EVM.Step` (the two-constructor wrapper around `StepRunning`
and `StepReturn` defined in `EvmSemantics/EVM/Step.lean`) is deterministic.

**Result: `Step` is *not* deterministic.**

The `StepRunning` inductive collects several *exception* rules at the bottom
(out-of-gas, stack-underflow, bad-jump, …). These rules are written
parametrically over the decoded operation and their premises are *not*
mutually exclusive: a single running frame can satisfy the premises of more
than one exception rule at once. When that happens, `Step` relates the same
pre-state to two different post-states — one per exception kind — so it fails
to be a partial function.

`step_not_deterministic` below exhibits a fully concrete witness of exactly
this shape. Take a running, non-precompile frame whose bytecode is the single
byte `0x01` (`ADD`), with an empty operand stack and zero gas available. On
this state:

* `StepRunning.stackUnderflow` fires, because `ADD` has `popArity = 2` while
  the stack has length `0 < 2`, producing
  `{ s with halt := .Exception .StackUnderflow }`; and
* `StepRunning.outOfGas` fires (with cost witness `1`), because `ADD`'s total
  cost is at least `1` while `gasAvailable = 0 < 1`, producing
  `{ s with halt := .Exception .OutOfGas }`.

Both are lifted to `Step` through the `Step.running` wrapper, whose extra
premises `s.halt = .Running` and
`Precompile.isPrecompile … s.executionEnv.codeAddr = false` hold on the
witness (the default `codeAddr` is the zero address, which is not a
precompile). The two successors disagree on their `halt` field
(`StackUnderflow` vs `OutOfGas`), so they are distinct — witnessing
non-determinism.
-/

namespace EvmSemantics.EVM

/-- A concrete running frame that triggers two distinct exception rules.

    It is the default `State` with its bytecode overridden to the single byte
    `0x01` (the `ADD` opcode). Every other field keeps its default value:
    `halt = .Running`, `stack = []`, `gasAvailable = 0`, `pc = 0`, and the
    `codeAddr` is the zero address (not a precompile). -/
def underdeterminedState : State :=
  { (default : State) with
    executionEnv :=
      { (default : State).executionEnv with
        code := ByteArray.mk #[0x01] } }

/-- The small-step relation `Step` is **not** deterministic: there is a state
    from which it relates two distinct successor states.

    See the module doc-comment for the plain-English explanation — the
    `stackUnderflow` and `outOfGas` exception rules both fire on
    `underdeterminedState`, yielding successors that differ in their `halt`
    field. -/
theorem step_not_deterministic :
    ∃ (s s₁ s₂ : State), Step s s₁ ∧ Step s s₂ ∧ s₁ ≠ s₂ := by
  refine ⟨underdeterminedState,
          { underdeterminedState with halt := .Exception .StackUnderflow },
          { underdeterminedState with halt := .Exception .OutOfGas },
          ?_, ?_, ?_⟩
  · -- `stackUnderflow` on `ADD` (popArity 2) with the empty stack.
    exact Step.running (by rfl) (by decide)
      (StepRunning.stackUnderflow underdeterminedState Operation.ADD
        (by decide) (by decide))
  · -- `outOfGas` on `ADD` with cost witness `1` and `gasAvailable = 0`.
    exact Step.running (by rfl) (by decide)
      (StepRunning.outOfGas underdeterminedState Operation.ADD 1
        (by decide) (by decide) (by decide))
  · -- The two successors differ in their `halt` field.
    intro h
    have h2 : HaltKind.Exception ExecutionException.StackUnderflow
                = HaltKind.Exception ExecutionException.OutOfGas :=
      congrArg State.halt h
    exact absurd (HaltKind.Exception.inj h2) (by decide)

end EvmSemantics.EVM

#print axioms EvmSemantics.EVM.step_not_deterministic
