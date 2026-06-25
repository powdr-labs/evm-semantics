---
name: vmtests
description: Run the ethereum/legacytests VMTests conformance suite against the evaluator (stepF/run), interpret the pass/fail/skip/incon/crash results, and refresh the committed CI baseline. Use when asked to run vmtests, check conformance, investigate a failing or crashing test, or update the baseline after an evaluator fix.
---

# vmtests

Run the legacy ethereum **VMTests** suite against the executable evaluator. This
is the conformance suite matching the v1 scope: single-frame EVM, no
inter-contract calls, no transaction processing. Read `AGENTS.md` for project
scope and `VMTESTS.md` for the full harness writeup and known gaps.

## Get the corpus (one-time)

```sh
git clone --depth 1 https://github.com/ethereum/legacytests
```
The suite lives in `legacytests/Constantinople/VMTests`. (CI sparse-fetches the
same dir pinned to `CORPUS_REV` in `.github/workflows/ci.yml`.)

## Run

```sh
lake build vmtests
./.lake/build/bin/vmtests <path>/legacytests/Constantinople/VMTests   # full suite
./.lake/build/bin/vmtests --file <path>/.../add0.json                 # single test
```
Each test runs in its own child process (`--file` mode under the hood), so a
panic or hang loses only that test, not the run.

## Reading the summary

Line looks like: `pass=… (gas-checked=…) fail=… skip=… (unsup/keccak/gas) incon=… crash=…`

- **pass / gas-checked** — gas-checked tests run with the real `exec.gas` budget
  and compare the remaining `gas`; the rest run gas-ignored (`gasAvailable=2^63`).
- **skip** — `unsup` (CALL/CREATE family, SELFDESTRUCT), `keccak`
  (KECCAK256/EXTCODEHASH — `keccak256` is opaque, returns 0), `gas` (GAS opcode
  where gas-checked mode isn't available).
- **incon** — out-of-gas / fuel-exhausted cases the infinite-gas harness can't
  reproduce, plus the ~11 jump-into-PUSH-data tests (a real soundness gap).
- **crash** — child panicked or timed out. Should be 0; a new crash is a real
  regression — investigate with `--file` on that test.

## Refresh the baseline (after an evaluator fix turns fails into passes)

CI's VMTests job is non-gating but compares against
`.github/vmtests-baseline.txt`. When you improve results, move the floor:

```sh
./.lake/build/bin/vmtests <path>/legacytests/Constantinople/VMTests > raw.txt
.github/scripts/vmtests_summary.sh raw.txt > .github/vmtests-baseline.txt
```
If you regenerated against a **newer corpus**, bump `CORPUS_REV` in
`.github/workflows/ci.yml` in the *same commit* — the baseline and pinned corpus
revision must always move together. Never bump one without the other.

## Reporting

Restate the summary counts in text (the extractor can't see tool output). Call
out any regression vs baseline (a previously-passing test now FAIL/CRASH) — that
is the thing the CI check exists to catch.
