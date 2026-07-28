module

public meta import Lean

/-!
`EvmSemantics.Tactic.SplitIfs` — a self-contained `split_ifs` tactic.

The gas/memory-affordability proofs (`EVM.StepComplete.*`) case-split on the
nested `if`s inside `consumeGas`/`canExpandMemory`. Mathlib's `split_ifs` did
that; this is a faithful, Mathlib-free port of it.

Ported from `Mathlib.Tactic.SplitIfs` (Apache-2.0, authors Gabriel Ebner,
David Renshaw); reduced to depend only on Lean core. The one Mathlib helper it
used, `andThenOnSubgoals`, is inlined below.
-/

public meta section

namespace EvmSemantics.Tactic

open Lean Elab.Tactic Parser.Tactic Lean.Meta

/-- Run `tac1` on the main goal, then `tac2` on every goal it produces. -/
private def andThenOnSubgoals (tac1 tac2 : TacticM Unit) : TacticM Unit :=
  Lean.Elab.Tactic.focus do
    tac1
    let mut newGoals := #[]
    for g in ← getGoals do
      setGoals [g]
      tac2
      newGoals := newGoals ++ (← getGoals).toArray
    setGoals newGoals.toList

/-- A position where a split may apply. -/
private inductive SplitPosition
| target
| hyp (fvarId : FVarId)

/-- Collects a list of positions pointed to by `loc` and their types. -/
private def getSplitCandidates (loc : Location) : TacticM (List (SplitPosition × Expr)) :=
match loc with
| Location.wildcard => do
  let candidates ← (← getLCtx).getFVarIds.mapM
    (fun fvarId ↦ do
      let typ ← instantiateMVars (← inferType (mkFVar fvarId))
      return (SplitPosition.hyp fvarId, typ))
  pure ((SplitPosition.target, ← getMainTarget) :: candidates.toList)
| Location.targets hyps tgt => do
  let candidates ← (← hyps.mapM getFVarId).mapM
    (fun fvarId ↦ do
      let typ ← instantiateMVars (← inferType (mkFVar fvarId))
      return (SplitPosition.hyp fvarId, typ))
  if tgt
  then return (SplitPosition.target, ← getMainTarget) :: candidates.toList
  else return candidates.toList

/-- Return the condition and decidable instance of an `if` expression to case split. -/
private partial def findIfToSplit? (e : Expr) : Option (Expr × Expr) :=
  match e.find? fun e => (e.isIte || e.isDIte) && !(e.getArg! 1 5).hasLooseBVars with
  | some iteApp =>
    let cond := iteApp.getArg! 1 5
    let dec := iteApp.getArg! 2 5
    findIfToSplit? cond |>.getD (cond, dec)
  | none => none

/-- Finds an if condition to split. If successful, returns the position and the condition. -/
private def findIfCondAt (loc : Location) : TacticM (Option (SplitPosition × Expr)) := do
  for (pos, e) in (← getSplitCandidates loc) do
    if let some (cond, _) := findIfToSplit? e
    then return some (pos, cond)
  return none

/-- `Simp.Discharge` strategy for `reduceIfsAt`: delegates to `SplitIf.discharge?`
and additionally discharges `True`. -/
private def discharge? (e : Expr) : SimpM (Option Expr) := do
  let e ← instantiateMVars e
  if let some e1 ← (← SplitIf.mkDischarge? false) e
    then return some e1
  if e.isConstOf `True
    then return some (mkConst `True.intro)
  return none

/-- Simplifies if-then-else expressions after cases have been split out. -/
private def reduceIfsAt (loc : Location) : TacticM Unit := do
  let ctx ← SplitIf.getSimpContext
  let ctx := ctx.setFailIfUnchanged false
  let _ ← simpLocation ctx (← ({} : Simp.SimprocsArray).add `reduceCtorEq false) discharge? loc
  pure ()

/-- Splits a single if-then-else expression and then reduces the resulting goals. -/
private def splitIf1 (cond : Expr) (hName : Name) (loc : Location) : TacticM Unit := do
  let splitCases :=
    evalTactic (← `(tactic| by_cases $(mkIdent hName) : $(← Elab.Term.exprToSyntax cond)))
  andThenOnSubgoals splitCases (reduceIfsAt loc)

/-- Pops off the front of the list of names, or generates a fresh name if the list is empty. -/
private def getNextName (hNames : IO.Ref (List (TSyntax `Lean.binderIdent))) : MetaM Name := do
  match ← hNames.get with
  | [] => mkFreshUserName `h
  | n::ns => do hNames.set ns
                if let `(binderIdent| $x:ident) := n
                then pure x.getId
                else pure `_

/-- Returns `true` if the condition or its negation already appears as a hypothesis. -/
private def valueKnown (cond : Expr) : TacticM Bool := do
  let not_cond := mkApp (mkConst `Not) cond
  for h in ← getLocalHyps do
    let ty ← instantiateMVars (← inferType h)
    if cond == ty then return true
    if not_cond == ty then return true
  return false

/-- Main loop of `split_ifs`. Pulls names for new hypotheses from `hNames`.
Stops if it encounters a condition in the passed-in `List Expr`. -/
private partial def splitIfsCore
    (loc : Location)
    (hNames : IO.Ref (List (TSyntax `Lean.binderIdent))) :
    List Expr → TacticM Unit := fun done ↦ withMainContext do
  let some (_, cond) ← findIfCondAt loc
      | Meta.throwTacticEx `split_ifs (← getMainGoal) "no if-then-else conditions to split"
  let cond := if cond.isAppOf `Not then cond.getAppArgs[0]! else cond
  if done.contains cond then return ()
  let no_split ← valueKnown cond
  if no_split then
    andThenOnSubgoals (reduceIfsAt loc) (splitIfsCore loc hNames (cond::done) <|> pure ())
  else do
    let hName ← getNextName hNames
    andThenOnSubgoals (splitIf1 cond hName loc) ((splitIfsCore loc hNames (cond::done)) <|>
      pure ())

/-- `split_ifs` splits the goal into cases for every if-then-else expression it
contains, by applying excluded middle to each condition. `split_ifs with h₁ h₂`
names the introduced hypotheses; `split_ifs at l` splits at location(s) `l`. -/
syntax (name := splitIfs) "split_ifs" (location)? (" with" (ppSpace colGt binderIdent)+)? : tactic

elab_rules : tactic
| `(tactic| split_ifs $[$loc:location]? $[with $withArg*]?) =>
  let loc := match loc with
  | none => Location.targets #[] true
  | some loc => expandLocation loc
  let names := match withArg with
  | none => []
  | some args => args.toList
  withMainContext do
    let names ← IO.mkRef names
    splitIfsCore loc names []
    for name in ← names.get do
      logWarningAt name m!"unused name: {name}"

end EvmSemantics.Tactic
