---
name: prove-soundness
description: Work on the stepF-to-Step soundness proofs in EVM/Equiv.lean — discharge a proof obligation, extend a helper lemma after an opcode change, or fix a broken proof. Use when touching Equiv.lean, when a soundness lemma fails to close, or after changing Step/stepF for an opcode.
---

# prove-soundness

Maintain `EVM/Equiv.lean`, which proves
`stepF_sound : stepF s = .ok s' → Step s s'` — every transition the executable
`stepF` produces is a valid `Step` derivation. Read `AGENTS.md` for the
three-view architecture (Step / Eval / stepF) before editing.

## The hard rule

`Equiv.lean` is **closed — no `sorry`**. Do not introduce `sorry`, `admit`, or
`native_decide`-style escape hatches to make it build. If a proof won't close,
the fix is in the proof or in a missing supporting lemma, not in weakening the
statement.

## Proof structure (two layers)

1. **Per-helper soundness lemmas** — one per `stepF.*` group helper:
   `stopArith_sound`, `compBit_sound`, `keccak_sound`, `env_sound`,
   `block_sound`, `system_sound`, `stackMemFlow_sound`, `push_sound`,
   `log_sound`, `dup_sound`, `swap_sound`, `dupN_sound`, `swapN_sound`,
   `exchange_sound`. Each `unfold`s the helper, `match`es on the operation kind
   and stack shape, then closes every leaf either by applying the matching
   `Step` constructor or by deriving a contradiction from `h : … = .ok _` when
   `stepF` actually returned `.error`.
2. **Headline `stepF_sound`** — unfolds `stepF`, splits on
   `s.halt` / `s.decoded` / the gas check / the operation kind, and dispatches
   each `Operation` constructor to its helper lemma.

`Eval.halted_inv` (a halted state's only `Eval` is `Eval.halted`) is also
exported and does not go through `stepF`.

## Working idioms in this file

- **Contradiction leaves.** When a `match` arm corresponds to a `stepF` path
  that returns `.error`, the hypothesis `h : stepF… = .ok s'` is absurd. Close
  it with `nomatch h` / `simp at h` / `exact absurd h …` rather than fabricating
  a transition.
- **Constructor premises must line up — but they vary by constructor.** A
  typical arithmetic/stack success constructor takes `h_op`
  (`s.decoded = some (.OP, arg)`), `h_running`, `h_gas`
  (`Gas.cost op ≤ s.gasAvailable` — `gasAvailable` is a `Nat`, no `.toNat`), and
  an `h_stack` shape. Notable exceptions to check before chasing arguments:
  `Step.stop` (and the other halts) has **only** `h_op` + `h_running` (no
  `h_gas`, no `h_stack`); stackless reads like `address`/`coinbase`/`pc` have
  `h_gas` but **no** `h_stack`. Read the actual constructor. Supply each premise
  from the helper's match context; `consumeGas` needs the gas proof explicitly.
- **List witnesses.** `log_sound` recovers the topics list via
  `popN_correct` (in `StepF.lean`): `popN stk k = some (topics, rest)` implies
  `topics.length = k ∧ stk = topics ++ rest`. Reuse it rather than re-inducting.
- **Decoder-width pitfall.** `Step.pushN` takes the immediate width as an
  explicit `immWidth : Nat` parameter (not `k.val`) so push soundness doesn't
  need a separate decoder invariant. Preserve this if you touch PUSH.

## After an opcode change

If you changed `Step.lean` / `StepF.lean` for an opcode (see "Adding or changing
an opcode" in `AGENTS.md`), extend the matching `*_sound` helper so it still
closes, then verify against the targets CI builds (warning-clean) and `lake
lint`:

Run the **build-and-lint** skill's CI warning gate (the `set -o pipefail` +
`grep warning:` + `exit 1` block over `lake build evm_semantics vmtests`), then
`lake lint`. A plain `lake build` is **not** enough on its own: a proof hole only
emits a `declaration uses 'sorry'` *warning*, and `lake build` still exits `0` —
the build-and-lint gate is what turns that warning into a non-zero exit, the same
way CI does.

A textual `grep` for `sorry` is not a reliable hole-check either: `Equiv.lean`'s
own docstring contains the phrase `` (no `sorry`) ``, so `grep sorry` reports a
false positive. If you grep anyway, expect only that docstring line:

```sh
grep -n 'sorry' EvmSemantics/EVM/Equiv.lean   # only the docstring "(no `sorry`)" should match
```

## Reporting

State whether the proof closes with no `sorry` and that `lake build` is clean.
If a lemma won't close, name the exact lemma and the leaf goal that's stuck.
