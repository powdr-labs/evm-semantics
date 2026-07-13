# Brief: close the `sorry`s in your `StepComplete` group file

You are proving **completeness** cases: each `StepRunning` constructor's
premises force the executable `stepF` to compute exactly that constructor's
successor. The statements are FROZEN (the assembly in
`EvmSemantics/EVM/StepDeterminism.lean` applies them positionally by name) —
do not rename lemmas, reorder/alter hypotheses, or change conclusions. Only
replace each `sorry` with a proof. You MAY add `private` helper lemmas inside
your own file. Do NOT edit any other file. Docstrings are already present.

## Verification (the only accepted done-criterion)

```sh
lake env lean EvmSemantics/EVM/StepComplete/<YourFile>.lean
```
must produce **zero output** — no errors AND no warnings (warnings include
`sorry`, unused variables/simp args, lines over 100 columns, unreachable
tactics). Do not run `lake build` (other agents share this worktree; `lake
env lean` avoids write races). Never introduce `sorry`, `admit`, new axioms,
or `native_decide`.

## The proof pattern

Shared evaluation lemmas live in `EvmSemantics/EVM/StepComplete/Dispatch.lean`:
- `State.decodedOp_some : s.decodedOp = some op → ∃ argOpt, s.decoded = some (op, argOpt)`
- `stepF_eq_ok : stepFE s = .ok t → stepF s = t`
- `stepF_eq_error : stepFE s = .error e → stepF s = { s with halt := .Exception e }`
- `stepFE_dispatch (h_run) (h_np) (h_dec) (h_cap : length + pushArity ≤ 1024 + popArity)
   (h_g : baseCost ≤ gas) : stepFE s = <per-group helper on (s.consumeGas base h_g)>`
- `stepFE_decodeNone`, `stepFE_overflow`, `stepFE_baseOog` — the three
  top-level error outcomes.

A validated exemplar (this exact proof compiles for `complete_add`):

```lean
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  refine stepF_eq_ok ?_
  rw [stepFE_dispatch h_run h_np h_dec h_cap h_gas]
  simp only [stepF.stopArith, h_stack]
  rfl
```

After `rw [stepFE_dispatch …]` the goal is `<group helper applied> = .ok <target>`
(or `.error e` for exception rules via `stepF_eq_error`). `simp only [stepF.<helper>,
h_stack]` reduces the helper's op-match and stack-match; the remaining record
equality is usually definitional (`rfl`). When it is not, the *same* equality
was already proven in the soundness direction — open `EvmSemantics/EVM/Equiv.lean`,
find the matching case in `<group>_sound` / `<group>_sound_error`, and reuse its
`post_eq` simp set / bridging steps (e.g. `simp [State.consumeGas, State.consumeMemExp,
State.replaceStackAndIncrPC, State.activeWordsAfterUInt256, Gas.<op>Total, UInt256.succ,
MachineState.memExpansionDelta, show ∀ (a b : UInt256), a + b = a.add b from fun _ _ => rfl]`
possibly followed by `grind`) — you need it in the mirrored orientation.

For rules whose `h_gas` is a bundled total (e.g. `Gas.mloadTotal s offset ≤ gas`),
derive the base-fee bound for `stepFE_dispatch` first, e.g.
`have h_base : Gas.baseCost s.fork .MLOAD ≤ s.gasAvailable := by
   unfold Gas.mloadTotal at h_gas; omega`
and discharge the staged `chargeMem`/dynamic-cost branches (`unfold chargeMem`,
`rw [dif_pos …]`) from the same bundled bound.

## Gotchas

- `s.fork` is an abbrev for `s.executionEnv.fork`. `omega` treats the two
  spellings as different atoms — normalize with `simp only [State.fork] at …`
  or `show`-conversions before `omega` when both occur.
- Dependent matches (`match h : x with …`) in goals don't reduce under
  `simp only [hx]`; use `split` and kill the impossible branch, or do case
  analysis with `rcases hh : x with …` then `simp only [hh]`.
- `stepF.push`'s width-0 vs width-(k+1) arms: `StepRunning.push0` pins
  `.Push ⟨0, _⟩`; `pushN` pins the full `s.decoded` with a `some (data, immWidth)`
  argument — use it directly as `h_dec` (skip `decodedOp_some`).
- EXP uses `UInt256.expFast` in `stepF` but `UInt256.exp` in the rule:
  rewrite with `UInt256.expFast_eq_exp`.
- LOG: `stepF.popN` vs the rule's `topics ++ rest` witness — see
  `popN_correct` (`StepF.lean`) and how `log_sound` uses it; for completeness
  you need the other direction: from `h_stack : s.stack = offset :: size ::
  topics ++ rest` and `h_topics_n : topics.length = n.val`, show
  `stepF.popN (topics ++ rest) n.val = some (topics, rest)`. Prove a small
  private lemma by induction if needed.
- SWAP/SWAPN/EXCHANGE: the rule premise is `s.stack.exchange … = some stk'` —
  `stepF` matches on the same expression; `simp only [h_swap]` reduces it.
- The reach predicates (`State.oogReach`, `State.underflowReach`,
  `State.staticReach`) are defs by `match`; on a concrete op
  `unfold State.oogReach` (or `simp [State.oogReach]`) reduces them.
- `Gas.totalCost` matches on `(op, s.stack)`; with a concrete op it reduces
  by `unfold Gas.totalCost` (plus the stack shape when the op has a
  stack-dependent arm).
- `⋯`-proof arguments differ freely (proof irrelevance): `rfl`/`exact` close
  goals whose two sides differ only in embedded proofs.
- Keep every line ≤ 100 characters.

## Definitions of the objects you are evaluating

- `stepFE` / helpers: `EvmSemantics/EVM/StepF.lean`
- The rules (your lemma statements mirror them): `EvmSemantics/EVM/Step.lean`
- Gas totals: `EvmSemantics/EVM/Gas.lean`
- The soundness mirror (idiom mine): `EvmSemantics/EVM/Equiv.lean`
  (note: its `totalCost_*` mini-lemmas are `private` — re-prove locally if
  you need one, they are one-liners: `unfold Gas.totalCost; rfl`-ish given
  the stack shape).

Report back: which lemmas closed, and paste the (empty) verifier output.
If a statement itself seems unprovable (premises genuinely insufficient to
pin `stepF`'s path), STOP on that lemma and report exactly why — that would
mean a rule in Step.lean needs another premise, which is a design-level
decision, not yours to make. Leave that single `sorry` in place, finish the
others, and include the analysis in your final report.
