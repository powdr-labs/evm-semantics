module

public import EvmSemantics.GasFreeEVM.Step
public import EvmSemantics.EVM.Halted

/-!
`EvmSemantics.GasFreeEVM.Eval` — the **gas-free** big-step relation,
parallel to `EvmSemantics.EVM.Eval` in `EVM/BigStep.lean`. `Eval s r`
means: starting from `s`, zero or more gas-free `Step` transitions reach
a *done* state (halted with no suspended callers), whose `toResult`
projection is `r`.

This is the relation users prove against when reasoning about smart
contracts without gas. The bridge to the gas-aware `EVM.Eval` (and
hence to the verified executable `stepF`) is in `GasFreeEVM/Equiv.lean`.
-/

@[expose] public section

open EvmSemantics.EVM

namespace EvmSemantics.GasFreeEVM

/-- Reflexive-transitive closure of `Step`. -/
inductive Steps : State → State → Prop
  | refl  : ∀ s, Steps s s
  | trans : ∀ {s s' s''}, Step s s' → Steps s' s'' → Steps s s''

/-- Big-step gas-free evaluation: zero or more `Step`s ending in a *done*
    state, projected to an `ExecutionResult`. Compare `Eval` in
    `EVM/BigStep.lean`. -/
inductive Eval : State → ExecutionResult → Prop
  /-- Zero-step case: the state is already done — halted with an empty call
      stack. -/
  | halted   : ∀ {s}, s.halt ≠ .Running → s.callStack = [] → Eval s s.toResult
  /-- Take one gas-free step, then evaluate the rest. -/
  | stepThen : ∀ {s s' r}, Step s s' → Eval s' r → Eval s r

namespace Steps

/-- Append: if `s →*ᴺᴳ s'` and `s' →*ᴺᴳ s''` then `s →*ᴺᴳ s''`. -/
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

/-- The big-step gas-free relation is just the small-step gas-free closure plus
    a *done* state. Mirrors `Eval.iff_steps_halted`. -/
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
    `toResult` under `Eval`. -/
theorem of_halted {s : State} (h : s.halt ≠ .Running) (h_cs : s.callStack = []) :
    Eval s s.toResult :=
  .halted h h_cs

end Eval

/-! ### A *done* state has no successor under `Step`

`Step` has two constructors: `running` (which carries `s.halt = .Running` as
its explicit precondition) and `returning` (which wraps a `StepReturn`, each
of whose constructors carries `h_stack : s.callStack = _ :: _`). So a state
that is halted (`halt ≠ .Running`) *and* has an empty call stack
(`callStack = []`) has no successor under `Step`. -/

theorem Step.not_from_done {s s' : State}
    (h : Step s s') (h_h : s.halt ≠ .Running) (h_cs : s.callStack = []) : False := by
  cases h with
  | running hr _ => exact h_h hr
  | returning sr => cases sr <;> simp_all

end EvmSemantics.GasFreeEVM
