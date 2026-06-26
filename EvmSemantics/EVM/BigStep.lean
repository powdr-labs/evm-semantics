module

public import EvmSemantics.EVM.Step
public import EvmSemantics.EVM.Halted

/-!
`Eval` — the big-step relation `Eval : EVM.State → ExecutionResult → Prop`.

`Eval s r` means: starting from `s`, executing zero or more `Step`s
reaches a *halted* state, and projecting that halted state via
`State.toResult` yields `r`.

We define it as a small inductive with two constructors — `halted`
(zero steps; the state is already terminal) and `stepThen` (one Step
followed by a recursive Eval). This is just the natural-deduction
presentation of "reflexive-transitive closure of `Step` ending in a
halted state".

`Steps s s'` is provided too as a separate reflexive-transitive
closure of `Step`, useful for stating properties that don't care about
the final result.
-/

@[expose] public section

namespace EvmSemantics
namespace EVM

/-- Reflexive-transitive closure of `Step`. -/
inductive Steps : State → State → Prop
  | refl  : ∀ s, Steps s s
  | trans : ∀ {s s' s''}, Step s s' → Steps s' s'' → Steps s s''

/-- Big-step evaluation: zero or more `Step`s ending in a *done* state (the
    active frame has halted **and** no suspended callers remain), projected to
    an `ExecutionResult`. -/
inductive Eval : State → ExecutionResult → Prop
  /-- Zero-step case: the state is already done — halted with an empty call
      stack. (A halted frame with callers still on the stack is *not* done; it
      has a `Step.callReturn*` successor.) -/
  | halted   : ∀ {s}, s.halt ≠ .Running → s.callStack = [] → Eval s s.toResult
  /-- Take one step, then evaluate the rest. -/
  | stepThen : ∀ {s s' r}, Step s s' → Eval s' r → Eval s r

namespace Steps

/-- Append: if `s →* s'` and `s' →* s''` then `s →* s''`. -/
theorem append {s s' s'' : State} (h₁ : Steps s s') (h₂ : Steps s' s'') :
    Steps s s'' := by
  induction h₁ with
  | refl _ => exact h₂
  | trans st rest ih => exact .trans st (ih h₂)

/-- Snoc: extend by a final `Step` at the end. -/
theorem snoc {s s' s'' : State} (h₁ : Steps s s') (h₂ : Step s' s'') :
    Steps s s'' :=
  h₁.append (.trans h₂ (.refl _))

end Steps

namespace Eval

/-- The big-step relation is just the small-step closure plus a *done* state:
    `Eval s r ↔ ∃ s', Steps s s' ∧ s'.halt ≠ Running ∧ s'.callStack = [] ∧ s'.toResult = r`. -/
theorem iff_steps_halted {s : State} {r : ExecutionResult} :
    Eval s r ↔
      ∃ s', Steps s s' ∧ s'.halt ≠ .Running ∧ s'.callStack = [] ∧ s'.toResult = r := by
  constructor
  · intro h
    induction h with
    | halted h_h h_cs => exact ⟨_, .refl _, h_h, h_cs, rfl⟩
    | stepThen st _ ih =>
      obtain ⟨s'', steps, h_h, h_cs, h_r⟩ := ih
      exact ⟨s'', .trans st steps, h_h, h_cs, h_r⟩
  · rintro ⟨s', steps, h_h, h_cs, h_r⟩
    induction steps with
    | refl _ => subst h_r; exact .halted h_h h_cs
    | trans st _ ih => exact .stepThen st (ih h_h h_cs h_r)

/-- A done state (halted with an empty call stack) evaluates only to its
    `toResult`. -/
theorem of_halted {s : State} (h : s.halt ≠ .Running) (h_cs : s.callStack = []) :
    Eval s s.toResult :=
  .halted h h_cs

end Eval

/-! ### A *done* state has no successor

`Step` has two constructors: `running` (which carries `s.halt = .Running` as
its explicit precondition) and `returning` (which wraps a `StepReturn`, each
of whose constructors carries `h_stack : s.callStack = _ :: _`). So a state
that is halted (`halt ≠ .Running`) *and* has an empty call stack
(`callStack = []`) has no successor under `Step`. -/

theorem Step.not_from_done {s s' : State}
    (h : Step s s') (h_h : s.halt ≠ .Running) (h_cs : s.callStack = []) : False := by
  -- `running` contradicts `h_h` via its `s.halt = .Running` precondition;
  -- `returning` contradicts `h_cs` via the inner `h_stack : callStack = _ :: _`.
  cases h with
  | running hr _ => exact h_h hr
  | returning sr => cases sr <;> simp_all

end EVM
end EvmSemantics
