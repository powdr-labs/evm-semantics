import EvmSemantics
import EvmSemantics.EVM.StepDeterminism

/-!
# Checks — the declared headline theorems and their axiom footprint

CI meta-checks for this project's machine-checked guarantees. This file is
**not** part of the `EvmSemantics` library; CI type-checks it separately with
`lake env lean Checks.lean`, after `lake build`.

It does two things:

1. Names the **headline theorems** in `roots`, so that "what does this repo
   prove?" has one machine-readable answer instead of being spread across
   per-file `#print axioms` lines. External audit tooling reads this list.
2. Pins the **exact axiom set** of each one with `#guard_msgs in #print
   axioms …`. A `sorry` shows up as `sorryAx`, and a new `axiom` produces no
   build warning at all — either would change the printed message, so
   `#guard_msgs` turns it into a hard elaboration failure. This file failing
   to compile means the guarantees below no longer hold on the terms recorded
   here.

The expected footprint is exactly Lean's three standard classical axioms —
`propext`, `Classical.choice`, `Quot.sound` — and notably *not* `sorryAx`.
There are no project-specific axioms.

## What these theorems do and do not say

Read the statements before reading the axiom lists. Every root below relates
two definitions that both live in **this repository**:

* `Step` — the `Prop`-valued small-step relation (`EVM/Step.lean`), the
  source of truth.
* `stepF` — the executable `Except`-valued shadow (`EVM/StepF.lean`), what the
  demo and the conformance runners actually execute.

So the roots say: *the executable and the relational definitions are the same
function*, and that function is deterministic. `step_iff_stepF` is the master
statement; the other four are its two halves and their immediate corollaries.

They say **nothing about Ethereum**. No theorem here compares `Step` against
the Yellow Paper, the execution-specs, or any other EVM. That claim is not a
theorem in this repository, and it cannot be one, because the reference
semantics is not formalised here. It rests on two other things:

* **The definitions themselves** — `Step`'s constructors, `Gas.baseCost` and
  the dynamic-cost helpers, `Decode.opcodeOf` / `isValidJumpDest`,
  `Precompile.run`, `Tx.execute`, and the `State` / `Frame` records. These are
  *asserted*, not proved; a human reads them against the Yellow Paper and the
  EIPs. That is the real audit surface, and it is far larger than this file.
* **Differential conformance** — the eight runner suites against
  `ethereum/tests` and EEST, each gated in CI by a committed baseline under
  `.github/`. See `VMTESTS.md`. This is the empirical evidence that stands in
  for the proof that cannot be written.

Outside all of the above sits the trusted computing base: the `opaque
keccak256` / `@[implemented_by keccak256Impl]` bridge (the kernel never checks
the two agree — see `ARCHITECTURE.md`), the rest of `Crypto/`, the `partial
def run` fuel loops, and the JSON test harnesses.

Keeping that distinction visible is the point of this file. "Zero `sorry`,
standard axioms only" is a true and useful statement about layer 1; it is not
a statement that the EVM is verified.
-/

namespace EvmSemantics.Checks

open Lean

/--
The headline guarantees of this repository: the theorems whose statements a
reader should read first, and whose axiom footprint is pinned below.

Double-backtick quotation means Lean resolves each name at elaboration time,
so this list cannot drift out of date silently — a rename that misses it is a
build error rather than a stale string.

The five are one claim viewed five ways. `step_iff_stepF` is the whole of it;
`stepF_sound` and `step_complete` are its two directions; `stepFE_sound` is
the `Except`-level lemma `stepF_sound` is a corollary of; `step_deterministic`
is the corollary that matters most to a downstream prover.
-/
def roots : List Name :=
  [ ``EvmSemantics.EVM.step_iff_stepF
  , ``EvmSemantics.EVM.stepF_sound
  , ``EvmSemantics.EVM.stepFE_sound
  , ``EvmSemantics.EVM.step_complete
  , ``EvmSemantics.EVM.step_deterministic ]

/-!
Beyond the roots, the second group of pins below covers **supporting**
theorems: local spec-versus-implementation bridges (`expFast_eq_exp`) and
facts downstream repositories build on (yul-compiler's own `Checks.lean`
cites `MachineState.writeBytes_getElem?_getD` by name). They are deliberately
*not* listed in `roots`. A theorem worth an axiom pin is not automatically a
claim about what this project guarantees, and folding the two groups together
would inflate the audited surface.

There is no second `List Name` for them on purpose: a bare `#print axioms`
already fails to elaborate on a name that does not resolve, so nothing is
lost, and the weaker signal stays weaker — which is how the two groups are
meant to be told apart from the outside.

Their footprints are not uniform, and the pins record that: three need only
`propext` and `Quot.sound`, and
`Precompile.isPrecompile_of_isPrecompileWithConfig` needs only `propext`.
-/

end EvmSemantics.Checks

/-! ## Axiom footprint of the headline theorems -/

/-- info: 'EvmSemantics.EVM.step_iff_stepF' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms EvmSemantics.EVM.step_iff_stepF

/-- info: 'EvmSemantics.EVM.stepF_sound' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms EvmSemantics.EVM.stepF_sound

/-- info: 'EvmSemantics.EVM.stepFE_sound' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms EvmSemantics.EVM.stepFE_sound

/-- info: 'EvmSemantics.EVM.step_complete' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms EvmSemantics.EVM.step_complete

/-- info: 'EvmSemantics.EVM.step_deterministic' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms EvmSemantics.EVM.step_deterministic

/-! ## Axiom footprint of the supporting theorems -/

/-- info: 'EvmSemantics.UInt256.expFast_eq_exp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms EvmSemantics.UInt256.expFast_eq_exp

/-- info: 'EvmSemantics.MachineState.writeBytes_getElem?_getD' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms EvmSemantics.MachineState.writeBytes_getElem?_getD

/-- info: 'EvmSemantics.EVM.Gas.baseCost_le_totalCost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms EvmSemantics.EVM.Gas.baseCost_le_totalCost

/-- info: 'EvmSemantics.EVM.Gas.sstoreFloor_le_totalCost' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms EvmSemantics.EVM.Gas.sstoreFloor_le_totalCost

/-- info: 'EvmSemantics.EVM.Step.not_from_done' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms EvmSemantics.EVM.Step.not_from_done

/-- info: 'EvmSemantics.EVM.Eval.iff_steps_halted' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms EvmSemantics.EVM.Eval.iff_steps_halted

-- The one pin whose expected message exceeds the project's 100-column
-- convention: it transcribes generated output verbatim, so it cannot be
-- rewrapped without breaking the comparison.
/-- info: 'EvmSemantics.EVM.Precompile.isPrecompile_of_isPrecompileWithConfig' depends on axioms: [propext] -/
#guard_msgs in
#print axioms EvmSemantics.EVM.Precompile.isPrecompile_of_isPrecompileWithConfig
