---
name: vmtests
description: Run the ethereum/legacytests VMTests conformance suite against the evaluator (stepF/run), interpret the pass/fail/incon/crash results, and refresh the committed CI baseline. Use when asked to run vmtests, check conformance, investigate a failing or crashing test, or update the baseline after an evaluator fix.
---

# vmtests

Run the legacy ethereum **VMTests** suite against the executable evaluator. This
is the conformance suite matching the project scope: single-frame EVM, no
inter-contract calls, no transaction processing. Read `AGENTS.md` for project
scope and `VMTESTS.md` for the full harness writeup and known gaps.

## Get the corpus (one-time)

Pin to the **exact** `CORPUS_REV` that CI uses (in `.github/workflows/ci.yml`) —
the committed `.github/vmtests-baseline.txt` was generated against that revision,
so a different corpus HEAD will make your counts and any refreshed baseline
disagree with CI:

```sh
REV=$(grep -m1 'CORPUS_REV:' .github/workflows/ci.yml | awk '{print $2}')
git clone https://github.com/ethereum/legacytests
git -C legacytests checkout "$REV"
```
The suite lives in `legacytests/Constantinople/VMTests`. (CI does a sparse
blobless fetch of just that dir at the same rev.)

## Run

```sh
lake build vmtests
./.lake/build/bin/vmtests <path>/legacytests/Constantinople/VMTests   # full suite
./.lake/build/bin/vmtests --file <path>/.../add0.json                 # single test
```
The full suite runs tests as **in-process Lean `Task`s** across `jobs` workers
(`-j N` / `VMTESTS_JOBS`, default 8) — there is **no subprocess isolation** (a
deliberate ~7× speedup over the old subprocess-per-file design). A worker `Task`
that throws is recorded as a `crash`, but a hard panic aborts the *whole run*.
Use `--file` to run a single test in its own process when you need to isolate
one that panics.

## Reading the summary

Line looks like: `pass=… fail=… incon=… crash=…`

- **pass** — every test runs with its real `exec.gas` budget; on a test
  with a `post` block, the remaining `gas` is compared too.
- **fail** — storage / return-data / balance / nonce / gas mismatch
  against the test's `post` block.
- **incon** — out-of-gas / fuel-exhausted cases the harness can't
  reproduce (the loop legitimately exceeds the 2M-step fuel cap, or the
  test relies on enforcement we don't yet model — e.g. the 1024-stack
  cap).
- **crash** — a worker `Task` threw and the parent recorded it (a hard
  panic instead aborts the whole run). Should be 0; a new crash is a
  real regression — isolate it with `--file` on that test.

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
