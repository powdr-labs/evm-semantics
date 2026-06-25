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

/-- Big-step evaluation: zero or more `Step`s ending in a halted state,
    projected to an `ExecutionResult`. -/
inductive Eval : State → ExecutionResult → Prop
  /-- Zero-step case: the state is already halted. -/
  | halted   : ∀ {s}, s.halt ≠ .Running → Eval s s.toResult
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

/-- The big-step relation is just the small-step closure plus a halt:
    `Eval s r ↔ ∃ s', Steps s s' ∧ s'.halt ≠ Running ∧ s'.toResult = r`. -/
theorem iff_steps_halted {s : State} {r : ExecutionResult} :
    Eval s r ↔ ∃ s', Steps s s' ∧ s'.halt ≠ .Running ∧ s'.toResult = r := by
  constructor
  · intro h
    induction h with
    | halted h_h => exact ⟨_, .refl _, h_h, rfl⟩
    | stepThen st _ ih =>
      obtain ⟨s'', steps, h_h, h_r⟩ := ih
      exact ⟨s'', .trans st steps, h_h, h_r⟩
  · rintro ⟨s', steps, h_h, h_r⟩
    induction steps with
    | refl _ => subst h_r; exact .halted h_h
    | trans st _ ih => exact .stepThen st (ih h_h h_r)

/-- A halted state evaluates only to its `toResult`. -/
theorem of_halted {s : State} (h : s.halt ≠ .Running) : Eval s s.toResult :=
  .halted h

end Eval

/-! ### Determinism of halting

Every constructor of `Step` carries the hypothesis `h_running : s.halt = .Running`.
So a halted state has no successor under `Step`. -/

theorem Step.not_from_halted {s s' : State} (h : Step s s') (h_h : s.halt ≠ .Running) :
    False := by
  -- Each Step constructor exposes h_running : s.halt = .Running, which
  -- contradicts h_h. The discharge is `cases h` followed by chaining the
  -- hypothesis. For brevity we use a single tactic block.
  cases h <;> simp_all

end EVM
end EvmSemantics
