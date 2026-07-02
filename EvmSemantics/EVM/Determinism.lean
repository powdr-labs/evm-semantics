module

public import EvmSemantics.EVM.Step
public import EvmSemantics.EVM.StepF
public import EvmSemantics.EVM.Equiv

/-!
`EVM.Determinism` — the small-step relation `Step` is (up to
overlapping exception-rule firings) deterministic:
`Step s s₁ → Step s s₂ → s₁ = s₂`.

# Semantic finding

`StepRunning` is intentionally **non-deterministic on exceptions** (see
`Step.lean:1766`):

> "Several exception rules may fire simultaneously from the same state
> (e.g. underflow AND out-of-gas). The relational semantics is
> *non-deterministic* about which exception is reported. A
> deterministic check order can be layered on top later if desired."

Concretely, `StepRunning.outOfGas` is parameterised over an arbitrary
`cost : Nat` satisfying only `Gas.baseCost s.fork op ≤ cost` and
`s.gasAvailable < cost`. Pick `cost := s.gasAvailable + 1` and the
rule fires from *any* decoded state — including states where the
"successful" rule for the same op would also fire. The two successors
disagree (`{ … stack := (a+b) :: rest }` vs
`{ s with halt := .Exception .OutOfGas }`), so
`Step s s₁ → Step s s₂ → s₁ = s₂` is literally false in general.

# Strategy for the deterministic result

Three viable routes are documented here; the file makes concrete
progress on each:

1. **`StepReturn.deterministic`** — the six `callReturn*` /
   `createReturn*` constructors are already mutually exclusive (via
   `s.halt` and `f.createAddr`). Proved here in full.

2. **`Step.deterministic_of_running`** — the four-arm split for the
   top-level `Step` wrapper is exclusive (via `s.halt` and
   `Precompile.isPrecompile`). Proved here, parameterised over
   `StepRunning`'s determinism.

3. **`StepRunning.deterministic`** — the hard half, blocked by the
   semantic non-determinism above. Three tractable paths:

   * **Tighten the semantics.** Replace the parametric `cost` in
     `outOfGas` with either (a) a strict base-only rule
     (`s.gasAvailable < Gas.baseCost s.fork op`) plus per-op
     dynamic-OOG rules, or (b) an `h_cost_exact : cost = someTotalOp`
     hypothesis that pins cost to the op's actual total. Both
     approaches touch ~20 call sites in `Equiv.lean` and every
     dynamic-gas opcode. Multi-PR effort.

   * **Prove the weaker theorem**
     `Step.non_exception_deterministic`: two derivations that both
     land on a non-Exception halt must agree. Achievable without
     changing semantics, but still requires case analysis over all 81
     success `StepRunning` constructors (one lemma per op-family,
     mirroring the `_sound` lemmas in `Equiv.lean`).

   * **Use `stepFE` as the canonical successor.** `stepFE : State →
     Except _ State` is a function by construction, and
     `stepFE_sound` establishes `Step s (stepF s)`. Determinism-via-
     completeness reduces to proving the converse
     `Step s s' → stepFE s = .ok s' ∨ …`, which is the same 81-case
     job as above but yields a stronger statement (Step ↔ stepFE
     bijection modulo exception non-determinism).

The stub `StepRunning.deterministic_of_agrees` below implements route
(3): parameterised over the completeness obligation, it derives the
running-half determinism uniformly. Its parameter statement,
`StepRunningStepFEAgreesShape`, is what a follow-up PR (per-op-family,
mirroring `stopArith_sound` etc.) would prove.
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

Reduces the running-half of determinism to a per-op-family
completeness obligation, in the same shape as the `_sound` lemmas in
`Equiv.lean`. Once every op family has its `_complete` lemma, the
combined `StepRunning_stepFE_agrees` closes this hypothesis and
`StepRunning.deterministic_of_agrees` becomes unconditional. -/

/-- The completeness obligation used by `StepRunning.deterministic`.

    Reads: any `StepRunning s s'` derivation is *reproducible* by the
    executable shadow — either `stepFE s = .ok s'` (the interesting
    running-post-state case), or `stepFE s = .error e` and `s'` is the
    exception-folded halt state (the case where `StepRunning`'s
    exception rules fire).

    Proof approach — per op-family, mirroring `stopArith_sound`,
    `compBit_sound`, etc.:

    1. `cases h : StepRunning s s'` — one branch per `StepRunning`
       constructor.
    2. On a success arm (`.add`, `.mul`, …), the `h_op` hypothesis
       pins `s.decodedOp` to the specific opcode, so `stepFE` unfolds
       to the same case; then read off `.ok s'` by `rfl`.
    3. On an exception arm (`.outOfGas`, `.stackUnderflow`, …), a
       matching `.error` witness is produced by discharging the
       `stepFE` guards that gate on the very hypotheses the arm
       carries. -/
def StepRunningStepFEAgreesShape (s s' : State) : Prop :=
  StepRunning s s' →
    stepFE s = .ok s' ∨
    (∃ e, stepFE s = .error e ∧ s' = { s with halt := .Exception e })

/-- Determinism of `StepRunning`, modulo the functional-inversion
    hypothesis. As-stated this is **conditionally provable** but the
    hypothesis is unprovable for the current semantics — see the
    module docstring, "Semantic finding". The hypothesis becomes
    provable after tightening `outOfGas` (and the other parametric
    exception rules) so that at most one exception rule fires from
    each state. -/
theorem StepRunning.deterministic_of_agrees
    (StepRunning_stepFE_agrees :
       ∀ {s s' : State}, StepRunningStepFEAgreesShape s s')
    {s s₁ s₂ : State} (h₁ : StepRunning s s₁) (h₂ : StepRunning s s₂) :
    s₁ = s₂ := by
  rcases StepRunning_stepFE_agrees h₁ with h1_ok | ⟨e₁, h1_err, h1_state⟩
  · rcases StepRunning_stepFE_agrees h₂ with h2_ok | ⟨e₂, h2_err, h2_state⟩
    · rw [h1_ok] at h2_ok; cases h2_ok; rfl
    · rw [h1_ok] at h2_err; cases h2_err
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

/-! ## A concrete counter-example to full determinism, and the next
    step to eliminate it.

    Below is a witness that the current `StepRunning` semantics is
    genuinely non-deterministic; keeping it in the file makes the
    obligation on the semantics tightening explicit. -/

/-- Instantiating `outOfGas` with `cost = s.gasAvailable + 1` always
    fires, from any decoded, non-halted state. This is what makes the
    unconditional `StepRunning.deterministic` unprovable today —
    a state with a successful `.add` derivation ALSO admits this
    `outOfGas` derivation, with a distinct successor. -/
theorem StepRunning.outOfGas_always_fires
    {s : State} {op : Operation}
    (h_op : s.decodedOp = some op) :
    StepRunning s ({ s with halt := .Exception .OutOfGas }) := by
  let cost := Nat.max (Gas.baseCost s.fork op) (s.gasAvailable + 1)
  refine StepRunning.outOfGas s op cost h_op (Nat.le_max_left _ _) ?_
  show s.gasAvailable < cost
  have : s.gasAvailable + 1 ≤ cost := Nat.le_max_right _ _
  omega

end EVM
end EvmSemantics
