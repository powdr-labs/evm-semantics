#!/usr/bin/env bash
#
# Normalize raw `vmtests <dir>` output into a stable, diffable summary of
# non-passing tests, one line per test:
#
#   <test_id>: FAIL
#   <test_id>: CRASH
#
# Sorted alphabetically. No aggregate counts, no comment header. The same
# format is stored as the committed *expected-failures* file
# (`.github/vmtests-expected-failures.txt`): merges stay conflict-free because
# each fixed test removes exactly one line at a known sorted position and each
# new failure inserts one, with nothing in between that both branches touch.
# Regenerate the committed file after an intentional pass/fail change:
#
#   .github/scripts/vmtests_summary.sh <raw> > .github/vmtests-expected-failures.txt
#
# INCON is out of scope for VMTests (the runner reports task-level hangs/panics
# as `crash`; there is no separate INCON tier). Tests that are neither FAIL
# nor CRASH are omitted — a passing test is simply absent from the file.
#
# Usage: vmtests_summary.sh <raw-output-file>
set -euo pipefail

raw="${1:?usage: vmtests_summary.sh <raw-output-file>}"

# Sanity: refuse to emit an empty summary for an incomplete run. Every complete
# vmtests run prints a final `pass=… fail=…` aggregate; if that line is missing
# the run was aborted mid-way and the summary would silently look like a clean
# pass. Fail loud instead so the check step can skip its comparison.
if ! grep -qE 'pass=[0-9]+ fail=[0-9]+' "$raw"; then
  echo "vmtests_summary.sh: no aggregate 'pass=… fail=…' line found in '$raw'" \
       "— the run is incomplete or its output format changed." >&2
  exit 2
fi

# Per-test notes look like:  "    FAIL smod0: ..."  /  "    CRASH exp1.json: ..."
# Emit `<id>: <tier>`, dropping the trailing message so reworded diagnostics
# do not register as spurious churn.
# `|| true`: a clean run has zero FAIL/CRASH lines, where `grep` exits 1 —
# without this, `set -o pipefail` would fail the whole script after it already
# wrote a valid summary (and CI would treat a clean run as unparseable).
{ grep -E '^[[:space:]]+(FAIL|CRASH) ' "$raw" || true; } \
  | sed -E 's/^[[:space:]]+(FAIL|CRASH) ([^:]+):.*/\2: \1/' \
  | sort -u
