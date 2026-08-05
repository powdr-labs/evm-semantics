module

public meta import Lean

/-!
`EvmSemantics.Tactic.Set` — a small, self-contained `set` tactic.

The relational-vs-executable soundness proofs (`EvmSemantics.EVM.Equiv`)
abstract recurring gas atoms (a base cost, a memory-expansion delta, …) to
short local names so that `omega` and `simp` see a single syntactic form
rather than several defeq spellings hidden behind fork/opcode abbreviations.
Mathlib's `set` tactic did that; this module is a faithful, Mathlib-free port
of the fragment those proofs use, so the semantics stays Mathlib-free while
the proofs are unchanged from their Mathlib-based form.

Ported from `Mathlib.Tactic.Set` (Apache-2.0, author Ian Benway); reduced to
depend only on Lean core. Behaviour matches Mathlib's `set`:

* `set a := t with h` introduces a local definition `a := t`, adds
  `h : a = t`, and replaces `t` with `a` everywhere it can (goal *and*
  hypotheses);
* `set a := t with ← h` records `h : t = a` instead;
* `set! a := t` skips the replacement.
-/

public meta section

namespace EvmSemantics.Tactic
open Lean Elab Elab.Tactic Meta

/-- Trailing arguments shared by `set` and `set!`: the new name, an optional
    type ascription, the defining term, and an optional `with [←] h` clause. -/
syntax setArgsRest := ppSpace binderIdent (" : " term)? " := " term
  (" with " "← "? binderIdent)?

/--
`set a := t with h` is a variant of `let a := t`. It adds the hypothesis
`h : a = t` to the local context and replaces `t` with `a` everywhere it can.

`set a := t with ← h` will add `h : t = a` instead.

`set! a := t with h` does not do any replacing.
-/
syntax (name := setTactic) "set" "!"? setArgsRest : tactic

/-- `set! a := t with h` is `set a := t with h` without the replacement step. -/
macro "set!" rest:setArgsRest : tactic => `(tactic| set ! $rest:setArgsRest)

elab_rules : tactic
| `(tactic| set%$tk $[!%$rw]? $a:binderIdent $[: $ty:term]? :=
    $val:term $[with $[←%$rev]? $h:binderIdent]?) =>
  withMainContext do
    let a ← match a with
      | `(binderIdent| $a:ident) => `(ident| $a)
      | _ => `(ident| a)
    let h ← h.mapM fun h => match h with
      | `(binderIdent| $h:ident) => `(ident| $h)
      | _ => `(ident| h)
    let (ty, vale) ← match ty with
    | some ty =>
      let ty ← Term.elabType ty
      pure (ty, ← elabTermEnsuringType val ty)
    | none =>
      let val ← elabTerm val none
      pure (← inferType val, val)
    let fvar ← liftMetaTacticAux fun goal ↦ do
      let (fvar, goal) ← (← goal.define a.getId ty vale).intro1P
      pure (fvar, [goal])
    withMainContext <|
      Term.addTermInfo' (isBinder := true) a (mkFVar fvar)
    if rw.isNone then
      evalTactic (← `(tactic|
        try rewrite [show $(← Term.exprToSyntax vale) = $a from rfl] at *))
    match h, rev with
    | some h, some none =>
      evalTactic (← `(tactic| have%$tk
        $h : $a = ($(← Term.exprToSyntax vale) : $(← Term.exprToSyntax ty)) := rfl))
    | some h, some (some _) =>
      evalTactic (← `(tactic| have%$tk
        $h : ($(← Term.exprToSyntax vale) : $(← Term.exprToSyntax ty)) = $a := rfl))
    | _, _ => pure ()

end EvmSemantics.Tactic
