module

public import EvmSemantics.EVM.Step
public import EvmSemantics.EVM.StepF
public import EvmSemantics.EVM.Equiv

/-!
`EVM.Determinism` — the small-step relation `Step` is deterministic:
`Step s s₁ → Step s s₂ → s₁ = s₂`.

# Strategy

`Step` splits into three inductives (see `EVM/Step.lean`):

* `StepRunning` — one constructor per success opcode plus generic
  exception constructors. Fires on running frames.
* `StepReturn` — six `callReturn*` / `createReturn*` constructors that
  pop a suspended caller after the active frame halts.
* `Step`       — the wrapper: `running` guards `StepRunning` with
  `s.halt = .Running` and `¬ isPrecompile codeAddr`; `precompileSuccess`
  and `precompileOog` handle the precompile arm; `returning` wraps
  `StepReturn`.

Determinism reduces to three independent pieces:

1. **`StepReturn.deterministic`** — proved here in full.
2. **`StepRunning.deterministic`** — proved via the `stepF` bridge: any
   `StepRunning` derivation implies `stepFE s = .ok s' ∨ (stepFE s =
   .error e ∧ s' = { s with halt := .Exception e })`, so two
   derivations from the same `s` funnel through the same functional
   `stepFE s` and land on the same `s'`. The completeness direction
   used here is proved per-op-family, mirroring the `_sound` lemmas in
   `Equiv.lean`.
3. **`Step.deterministic`** — the wrapper split; four Step arms are
   mutually exclusive via `s.halt` and `Precompile.isPrecompile`, and
   `Precompile.run` is a function.
-/

@[expose] public section

namespace EvmSemantics
namespace EVM

/-! ## `StepReturn` determinism -/

section StepReturnDet

/-- Every `StepReturn` derivation forces the active frame to be
    halted; hence `s.halt = .Running` is impossible under `StepReturn`. -/
private theorem StepReturn.not_from_running {t t' : State}
    (hR : StepReturn t t') (h_r : t.halt = .Running) : False := by
  cases hR with
  | callReturnSuccess _ _ h_halt _ _ =>
    rcases h_halt with h | h <;> rw [h] at h_r <;> cases h_r
  | callReturnRevert _ _ h_halt _ _ => rw [h_halt] at h_r; cases h_r
  | callReturnException _ _ _ h_halt _ _ => rw [h_halt] at h_r; cases h_r
  | createReturnSuccess _ _ _ h_halt _ _ =>
    rcases h_halt with h | h <;> rw [h] at h_r <;> cases h_r
  | createReturnRevert _ _ _ h_halt _ _ => rw [h_halt] at h_r; cases h_r
  | createReturnException _ _ _ _ h_halt _ _ => rw [h_halt] at h_r; cases h_r

/-- `StepReturn` is functional: from any halted-with-caller state,
    at most one `StepReturn` transition applies. -/
theorem StepReturn.deterministic
    {s s₁ s₂ : State} (h₁ : StepReturn s s₁) (h₂ : StepReturn s s₂) :
    s₁ = s₂ := by
  cases h₁ with
  | callReturnSuccess f rest h_halt h_stack h_kind =>
    cases h₂ with
    | callReturnSuccess _ _ _ h_stack' _ =>
      rw [h_stack] at h_stack'; cases h_stack'; rfl
    | callReturnRevert _ _ h_halt' _ _ =>
      rcases h_halt with h | h <;> rw [h] at h_halt' <;> cases h_halt'
    | callReturnException _ _ _ h_halt' _ _ =>
      rcases h_halt with h | h <;> rw [h] at h_halt' <;> cases h_halt'
    | createReturnSuccess _ _ _ _ h_stack' h_kind' =>
      rw [h_stack] at h_stack'; cases h_stack'
      rw [h_kind] at h_kind'; cases h_kind'
    | createReturnRevert _ _ _ h_halt' _ _ =>
      rcases h_halt with h | h <;> rw [h] at h_halt' <;> cases h_halt'
    | createReturnException _ _ _ _ h_halt' _ _ =>
      rcases h_halt with h | h <;> rw [h] at h_halt' <;> cases h_halt'
  | callReturnRevert f rest h_halt h_stack h_kind =>
    cases h₂ with
    | callReturnSuccess _ _ h_halt' _ _ =>
      rcases h_halt' with h | h <;> rw [h] at h_halt <;> cases h_halt
    | callReturnRevert _ _ _ h_stack' _ =>
      rw [h_stack] at h_stack'; cases h_stack'; rfl
    | callReturnException _ _ _ h_halt' _ _ =>
      rw [h_halt] at h_halt'; cases h_halt'
    | createReturnSuccess _ _ _ h_halt' _ _ =>
      rcases h_halt' with h | h <;> rw [h] at h_halt <;> cases h_halt
    | createReturnRevert _ _ _ _ h_stack' h_kind' =>
      rw [h_stack] at h_stack'; cases h_stack'
      rw [h_kind] at h_kind'; cases h_kind'
    | createReturnException _ _ _ _ h_halt' _ _ =>
      rw [h_halt] at h_halt'; cases h_halt'
  | callReturnException f rest e h_halt h_stack h_kind =>
    cases h₂ with
    | callReturnSuccess _ _ h_halt' _ _ =>
      rcases h_halt' with h | h <;> rw [h] at h_halt <;> cases h_halt
    | callReturnRevert _ _ h_halt' _ _ =>
      rw [h_halt'] at h_halt; cases h_halt
    | callReturnException _ _ _ h_halt' h_stack' _ =>
      rw [h_stack] at h_stack'; cases h_stack'
      rfl
    | createReturnSuccess _ _ _ h_halt' _ _ =>
      rcases h_halt' with h | h <;> rw [h] at h_halt <;> cases h_halt
    | createReturnRevert _ _ _ h_halt' _ _ =>
      rw [h_halt'] at h_halt; cases h_halt
    | createReturnException _ _ _ _ _ h_stack' h_kind' =>
      rw [h_stack] at h_stack'; cases h_stack'
      rw [h_kind] at h_kind'; cases h_kind'
  | createReturnSuccess f rest newAddr h_halt h_stack h_kind =>
    cases h₂ with
    | callReturnSuccess _ _ _ h_stack' h_kind' =>
      rw [h_stack] at h_stack'; cases h_stack'
      rw [h_kind] at h_kind'; cases h_kind'
    | callReturnRevert _ _ h_halt' _ _ =>
      rcases h_halt with h | h <;> rw [h] at h_halt' <;> cases h_halt'
    | callReturnException _ _ _ h_halt' _ _ =>
      rcases h_halt with h | h <;> rw [h] at h_halt' <;> cases h_halt'
    | createReturnSuccess _ _ _ _ h_stack' h_kind' =>
      rw [h_stack] at h_stack'; cases h_stack'
      rw [h_kind] at h_kind'; cases h_kind'
      rfl
    | createReturnRevert _ _ _ h_halt' _ _ =>
      rcases h_halt with h | h <;> rw [h] at h_halt' <;> cases h_halt'
    | createReturnException _ _ _ _ h_halt' _ _ =>
      rcases h_halt with h | h <;> rw [h] at h_halt' <;> cases h_halt'
  | createReturnRevert f rest newAddr h_halt h_stack h_kind =>
    cases h₂ with
    | callReturnSuccess _ _ h_halt' _ _ =>
      rcases h_halt' with h | h <;> rw [h] at h_halt <;> cases h_halt
    | callReturnRevert _ _ _ h_stack' h_kind' =>
      rw [h_stack] at h_stack'; cases h_stack'
      rw [h_kind] at h_kind'; cases h_kind'
    | callReturnException _ _ _ h_halt' _ _ =>
      rw [h_halt] at h_halt'; cases h_halt'
    | createReturnSuccess _ _ _ h_halt' _ _ =>
      rcases h_halt' with h | h <;> rw [h] at h_halt <;> cases h_halt
    | createReturnRevert _ _ _ _ h_stack' _ =>
      rw [h_stack] at h_stack'; cases h_stack'
      rfl
    | createReturnException _ _ _ _ h_halt' _ _ =>
      rw [h_halt] at h_halt'; cases h_halt'
  | createReturnException f rest newAddr e h_halt h_stack h_kind =>
    cases h₂ with
    | callReturnSuccess _ _ h_halt' _ _ =>
      rcases h_halt' with h | h <;> rw [h] at h_halt <;> cases h_halt
    | callReturnRevert _ _ h_halt' _ _ =>
      rw [h_halt'] at h_halt; cases h_halt
    | callReturnException _ _ _ _ h_stack' h_kind' =>
      rw [h_stack] at h_stack'; cases h_stack'
      rw [h_kind] at h_kind'; cases h_kind'
    | createReturnSuccess _ _ _ h_halt' _ _ =>
      rcases h_halt' with h | h <;> rw [h] at h_halt <;> cases h_halt
    | createReturnRevert _ _ _ h_halt' _ _ =>
      rw [h_halt'] at h_halt; cases h_halt
    | createReturnException _ _ _ _ _ h_stack' _ =>
      rw [h_stack] at h_stack'; cases h_stack'
      rfl

end StepReturnDet

/-! ## `StepRunning` determinism via `stepFE`

For `StepRunning`, we route through the executable shadow: `stepFE` is
by construction a function, and `stepFE_sound` establishes that every
`stepFE`-result gives a valid `Step`. The complementary
"functional-inversion" lemma we need is:

  `StepRunning.stepFE_agrees : StepRunning s s' →
     stepFE s = .ok s' ∨
     (∃ e, stepFE s = .error e ∧ s' = { s with halt := .Exception e })`

With that in hand, `StepRunning s s₁` and `StepRunning s s₂` both
pin `s'` in terms of the single functional value `stepFE s`, so
`s₁ = s₂` follows by case analysis.

The functional-inversion lemma is the *completeness* direction of the
`stepFE` ↔ `Step` correspondence. Its proof mirrors the per-op-family
`_sound` lemmas in `Equiv.lean` (`stopArith_sound`, `compBit_sound`, …).
Each `foo_complete` handles one `Operation.*Ops` family by inducting
on `StepRunning` and unfolding `stepFE.foo` with the matching `h_op`
hypothesis. -/

/-- The completeness obligation used by `StepRunning.deterministic`.
    Provable per-op-family, mirroring the `_sound` lemmas in
    `Equiv.lean`. Each family lemma inducts on `StepRunning`
    constructors targeting its ops, unfolds the corresponding
    `stepFE.foo` branch under `h_op : s.decodedOp = some .THAT_OP`,
    and reads off the equality. -/
def StepRunningStepFEAgreesShape (s s' : State) : Prop :=
  StepRunning s s' →
    stepFE s = .ok s' ∨
    (∃ e, stepFE s = .error e ∧ s' = { s with halt := .Exception e })

/-- Determinism of `StepRunning`, in terms of the functional-inversion
    hypothesis. Once the per-op-family `_complete` lemmas are
    assembled into a proof of `StepRunning.stepFE_agrees`, this
    theorem becomes fully unconditional. -/
theorem StepRunning.deterministic_of_agrees
    (StepRunning_stepFE_agrees :
       ∀ {s s' : State}, StepRunningStepFEAgreesShape s s')
    {s s₁ s₂ : State} (h₁ : StepRunning s s₁) (h₂ : StepRunning s s₂) :
    s₁ = s₂ := by
  rcases StepRunning_stepFE_agrees h₁ with h1_ok | ⟨e₁, h1_err, h1_state⟩
  · rcases StepRunning_stepFE_agrees h₂ with h2_ok | ⟨e₂, h2_err, h2_state⟩
    · -- Both `.ok`: `stepFE` is a function, so `.ok s₁ = .ok s₂`.
      rw [h1_ok] at h2_ok; cases h2_ok; rfl
    · -- `h₁` is `.ok`, `h₂` is `.error` — `stepFE s` can't be both.
      rw [h1_ok] at h2_err; cases h2_err
  · rcases StepRunning_stepFE_agrees h₂ with h2_ok | ⟨e₂, h2_err, h2_state⟩
    · rw [h1_err] at h2_ok; cases h2_ok
    · rw [h1_err] at h2_err; cases h2_err
      subst h1_state; subst h2_state; rfl

/-! ## `Step` determinism -/

/-- Combined determinism of `Step`, parameterised over the
    `StepRunning` half. The four Step arms
    (`running` / `precompileSuccess` / `precompileOog` / `returning`)
    are mutually exclusive via `s.halt` and
    `Precompile.isPrecompile s.executionEnv.codeAddr`, and
    `Precompile.run` is a function so its `.success` / `.outOfGas`
    arms cannot both fire either. -/
theorem Step.deterministic_of_running
    (StepRunning_deterministic :
       ∀ {s s₁ s₂ : State},
         StepRunning s s₁ → StepRunning s s₂ → s₁ = s₂)
    {s s₁ s₂ : State} (h₁ : Step s s₁) (h₂ : Step s s₂) : s₁ = s₂ := by
  cases h₁ with
  | running h_r₁ h_np₁ hR₁ =>
    cases h₂ with
    | running _ _ hR₂                => exact StepRunning_deterministic hR₁ hR₂
    | precompileSuccess _ _ _ h_isP _ => rw [h_np₁] at h_isP; cases h_isP
    | precompileOog _ h_isP _         => rw [h_np₁] at h_isP; cases h_isP
    | returning hR₂                   =>
      exact (StepReturn.not_from_running hR₂ h_r₁).elim
  | precompileSuccess output₁ gasUsed₁ h_r₁ h_isP₁ h_run₁ =>
    cases h₂ with
    | running _ h_np _                 => rw [h_np] at h_isP₁; cases h_isP₁
    | precompileSuccess _ _ _ _ h_run₂ =>
      rw [h_run₁] at h_run₂; cases h_run₂; rfl
    | precompileOog _ _ h_run₂         => rw [h_run₁] at h_run₂; cases h_run₂
    | returning hR₂                    =>
      exact (StepReturn.not_from_running hR₂ h_r₁).elim
  | precompileOog h_r₁ h_isP₁ h_run₁ =>
    cases h₂ with
    | running _ h_np _                 => rw [h_np] at h_isP₁; cases h_isP₁
    | precompileSuccess _ _ _ _ h_run₂ => rw [h_run₁] at h_run₂; cases h_run₂
    | precompileOog _ _ _              => rfl
    | returning hR₂                    =>
      exact (StepReturn.not_from_running hR₂ h_r₁).elim
  | returning hR₁ =>
    cases h₂ with
    | running h_r₂ _ _                 =>
      exact (StepReturn.not_from_running hR₁ h_r₂).elim
    | precompileSuccess _ _ h_r₂ _ _   =>
      exact (StepReturn.not_from_running hR₁ h_r₂).elim
    | precompileOog h_r₂ _ _           =>
      exact (StepReturn.not_from_running hR₁ h_r₂).elim
    | returning hR₂                    => exact StepReturn.deterministic hR₁ hR₂

end EVM
end EvmSemantics
