import EvmSemantics
import Batteries.Tactic.Lint

/-!
`Lint.lean` — run the global `#lint` command (from `Batteries`, also
re-exported by Mathlib) over the `EvmSemantics` package. This file is
invoked by the CI's `lint` job via `lake env lean Lint.lean`,
separately from the main `lake build`.

`#lint` checks for: unused arguments, definitions without doc-strings,
simp lemmas that are not in simp-normal-form, `sorry` axioms, unused
`have`s, dangerous instances, and more — the standard Lean/Batteries
suite.

To run locally:
```sh
lake env lean Lint.lean
```
-/

-- Globally lint every declaration in the `EvmSemantics` package.
#lint in EvmSemantics
