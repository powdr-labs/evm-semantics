module

public import EvmSemantics.EVM.BigStep

/-!
# Relational execution contracts

`StepsContract pre post` is a proof-facing boundary over the authoritative
small-step relation.  A contract exposes only a relational postcondition over
the initial and final states; its witness remains an ordinary `Steps` trace.

The combinators in this module do not replace `State`, `Step`, `Steps`, or
`Eval`.  They let downstream proofs compose selected observations and frame
conditions without equating complete state records at every boundary.
-/

@[expose] public section

namespace EvmSemantics
namespace EVM

/-- A Hoare-style contract over zero or more EVM steps. -/
def StepsContract (pre : State → Prop)
    (post : State → State → Prop) : Prop :=
  ∀ initial, pre initial →
    ∃ final, Steps initial final ∧ post initial final

/-- A relation on a projection of the initial and final states. -/
def Relates {α : Type} (view : State → α) (relation : α → α → Prop)
    (initial final : State) : Prop :=
  relation (view initial) (view final)

/-- A state projection is unchanged between two endpoints. -/
def Preserves {α : Type} (view : State → α) (initial final : State) : Prop :=
  view final = view initial

/-- A predicate on one selected projection of the final state. -/
@[nolint unusedArguments]
def FinalSatisfies {α : Type} (view : State → α) (predicate : α → Prop)
    (_initial final : State) : Prop :=
  predicate (view final)

namespace Observation

/-- The final frame has the selected halt kind. -/
@[nolint unusedArguments]
def HaltsAs (kind : HaltKind) (_initial final : State) : Prop :=
  final.halt = kind

/-- The final frame returned the selected bytes. -/
@[nolint unusedArguments]
def Returns (bytes : ByteArray) (_initial final : State) : Prop :=
  final.halt = .Returned ∧ final.hReturn = bytes

/-- The final state is done and projects to the selected execution result. -/
@[nolint unusedArguments]
def Result (result : ExecutionResult) (_initial final : State) : Prop :=
  final.isDone = true ∧ final.toResult = result

/-- The selected stack position contains a value in the final state. -/
@[nolint unusedArguments]
def StackAt (index : Nat) (value : UInt256) (_initial final : State) : Prop :=
  final.stack[index]? = some value

/-- A selected final-memory range contains exactly the given bytes. -/
@[nolint unusedArguments]
def MemoryRange (offset size : Nat) (bytes : ByteArray)
    (_initial final : State) : Prop :=
  MachineState.readPadded final.memory offset size = bytes

/-- The final state has no suspended caller frame. -/
@[nolint unusedArguments]
def NoCallers (_initial final : State) : Prop :=
  final.callStack = []

end Observation

namespace StepsContract

/-- The zero-step contract. -/
theorem refl (pre : State → Prop) :
    StepsContract pre (fun initial final => final = initial) := by
  intro initial hpre
  exact ⟨initial, .refl _, rfl⟩

/-- Strengthen a precondition and weaken a relational postcondition. -/
theorem consequence {pre pre' : State → Prop}
    {post post' : State → State → Prop}
    (hpre : ∀ state, pre' state → pre state)
    (contract : StepsContract pre post)
    (hpost : ∀ initial final, pre' initial → post initial final →
      post' initial final) :
    StepsContract pre' post' := by
  intro initial hinitial
  obtain ⟨final, hsteps, hfinal⟩ := contract initial (hpre initial hinitial)
  exact ⟨final, hsteps, hpost initial final hinitial hfinal⟩

/-- Sequentially compose contracts.  The intermediate relation becomes an
existentially hidden part of the resulting postcondition. -/
theorem trans {pre : State → Prop} {middle post : State → State → Prop}
    (first : StepsContract pre middle)
    (second : ∀ initial, pre initial →
      StepsContract (middle initial) post) :
    StepsContract pre (fun initial final =>
      ∃ state, middle initial state ∧ post state final) := by
  intro initial hinitial
  obtain ⟨state, hfirst, hmiddle⟩ := first initial hinitial
  obtain ⟨final, hsecond, hpost⟩ :=
    second initial hinitial state hmiddle
  exact ⟨final, hfirst.append hsecond, state, hmiddle, hpost⟩

/-- Compose contracts and immediately map their two postconditions to a
smaller relation, avoiding exposure of the intermediate state. -/
theorem transMapped {pre : State → Prop}
    {middle next post : State → State → Prop}
    (first : StepsContract pre middle)
    (second : ∀ initial, pre initial →
      StepsContract (middle initial) next)
    (mapPost : ∀ initial state final, pre initial →
      middle initial state → next state final → post initial final) :
    StepsContract pre post := by
  apply consequence (fun state hstate => hstate) (first.trans second)
  intro initial final hinitial hfinal
  obtain ⟨state, hmiddle, hnext⟩ := hfinal
  exact mapPost initial state final hinitial hmiddle hnext

/-- Retain a proved projection of the postcondition. -/
theorem project {pre : State → Prop} {post : State → State → Prop}
    {α : Type} (contract : StepsContract pre post)
    (view : State → α) (relation : α → α → Prop)
    (hproject : ∀ initial final, pre initial → post initial final →
      relation (view initial) (view final)) :
    StepsContract pre (Relates view relation) := by
  exact contract.consequence (fun state hstate => hstate)
    (fun initial final hinitial hfinal =>
      hproject initial final hinitial hfinal)

/-- Attach a frame fact for a projection known to be preserved. -/
theorem frame {pre : State → Prop} {post : State → State → Prop}
    {α : Type} (contract : StepsContract pre post) (view : State → α)
    (hframe : ∀ initial final, pre initial → post initial final →
      view final = view initial) :
    StepsContract pre (fun initial final =>
      post initial final ∧ Preserves view initial final) := by
  exact contract.consequence (fun state hstate => hstate)
    (fun initial final hinitial hfinal =>
      ⟨hfinal, hframe initial final hinitial hfinal⟩)

/-- A concrete `Steps` derivation as an exact singleton contract. -/
theorem ofSteps {initial final : State} (hsteps : Steps initial final) :
    StepsContract (fun state => state = initial)
      (fun _ state => state = final) := by
  intro state hstate
  subst state
  exact ⟨final, hsteps, rfl⟩

/-- Close a contract whose postcondition fixes a done execution result. -/
theorem toEval {pre : State → Prop} {result : ExecutionResult}
    (contract : StepsContract pre (Observation.Result result)) :
    ∀ initial, pre initial → Eval initial result := by
  intro initial hinitial
  obtain ⟨final, hsteps, hdone, hresult⟩ := contract initial hinitial
  apply Eval.iff_steps_halted.mpr
  refine ⟨final, hsteps, ?_, ?_, hresult⟩
  · intro hrunning
    simp [State.isDone, State.isHalted, State.isRunning, hrunning] at hdone
  · have h := hdone
    simp only [State.isDone, Bool.and_eq_true, List.isEmpty_iff] at h
    exact h.2

end StepsContract

/-- A relation-valued big-step endpoint. -/
def EvalContract (pre : State → Prop)
    (post : State → ExecutionResult → Prop) : Prop :=
  ∀ initial, pre initial →
    ∃ result, Eval initial result ∧ post initial result

namespace EvalContract

/-- Strengthen an evaluation precondition and weaken its result relation. -/
theorem consequence {pre pre' : State → Prop}
    {post post' : State → ExecutionResult → Prop}
    (hpre : ∀ state, pre' state → pre state)
    (contract : EvalContract pre post)
    (hpost : ∀ initial result, pre' initial → post initial result →
      post' initial result) :
    EvalContract pre' post' := by
  intro initial hinitial
  obtain ⟨result, heval, hresult⟩ := contract initial (hpre initial hinitial)
  exact ⟨result, heval, hpost initial result hinitial hresult⟩

/-- Turn a terminal `StepsContract` into a relation-valued evaluation
endpoint while retaining an arbitrary result observation. -/
theorem ofSteps {pre : State → Prop} {post : State → State → Prop}
    {resultPost : State → ExecutionResult → Prop}
    (contract : StepsContract pre post)
    (hdone : ∀ initial final, pre initial → post initial final →
      final.isDone = true)
    (hresult : ∀ initial final, pre initial → post initial final →
      resultPost initial final.toResult) :
    EvalContract pre resultPost := by
  intro initial hinitial
  obtain ⟨final, hsteps, hpost⟩ := contract initial hinitial
  refine ⟨final.toResult, ?_, hresult initial final hinitial hpost⟩
  apply Eval.iff_steps_halted.mpr
  refine ⟨final, hsteps, ?_, ?_, rfl⟩
  · intro hrunning
    have h := hdone initial final hinitial hpost
    simp [State.isDone, State.isHalted, State.isRunning, hrunning] at h
  · have h := hdone initial final hinitial hpost
    simp only [State.isDone, Bool.and_eq_true, List.isEmpty_iff] at h
    exact h.2

end EvalContract

end EVM
end EvmSemantics
