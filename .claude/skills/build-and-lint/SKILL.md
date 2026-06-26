---
name: build-and-lint
description: Build EvmSemantics and reproduce the CI lint discipline (warning-clean build + lake lint). Use when asked to build the project, fix build/lint errors, check the code compiles, or before pushing changes to Lean sources.
---

# build-and-lint

Build the EvmSemantics Lean project and enforce the same gates CI does. Read
`AGENTS.md` at the repo root first — it has the command list, the toolchain
pin, and the non-negotiable conventions this skill enforces.

## Steps

1. **First build / after `lake update`:** fetch Mathlib's prebuilt oleans so
   Mathlib is never compiled from source.
   ```sh
   lake exe cache get
   ```
   Skip if `.lake/packages/mathlib` oleans are already present (warm build).

2. **Build the binaries CI builds** (not just the default target):
   ```sh
   lake build evm_semantics vmtests
   ```
   Cold ~10 min, warm ~30 s.

3. **Reproduce the CI warning gate.** CI does a clean rebuild and fails on *any*
   `warning:` line — so a warm `lake build` that prints nothing is not proof.
   To check the way CI does:
   ```sh
   rm -rf .lake/build
   set -o pipefail                                   # else tee masks a build failure
   lake build evm_semantics vmtests 2>&1 | tee build.log || exit 1
   if grep -E "warning:" build.log; then
     echo "FAIL: warnings present"; exit 1           # warnings must fail the check
   fi
   echo "clean"
   ```
   `set -o pipefail` and the explicit `exit 1` matter for scripted use: without
   them a hard build failure is hidden by `tee`'s zero exit, and a warning hit
   would still exit successfully — exactly the CI gate's own form.
   The most common warning is the **100-column line limit**
   (`linter.style.longLine`, configured in `lakefile.toml`) — it counts
   comments and docstrings too. Wrap any line over 100 chars.

4. **Run the linter** (Batteries `runLinter` over the `EvmSemantics` namespace):
   ```sh
   lake lint
   ```

## Rules (from AGENTS.md)

- **Never** add `sorry` to make a build pass — `EVM/Equiv.lean` is fully closed.
- There is **no `scripts/nolints.json`** allow-list: fix lint findings in
  source. New declarations need a docstring; intentional exceptions get an
  explicit `@[nolint ...]` annotation (see existing ones on `Gas.cost`'s `_op`,
  `consumeGas`'s `_h`, and the `deriving`-generated decls).

## Reporting

State plainly whether the build was warning-clean and whether `lake lint`
passed. If either failed, quote the offending lines.
