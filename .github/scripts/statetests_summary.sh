#!/usr/bin/env bash
#
# Normalize raw `statetests -v <dir>` output into a stable, diffable summary of
# non-passing tests, one line per test:
#
#   <test_id>: FAIL
#   <test_id>: INCON
#   <test_id>: CRASH
#
# Sorted alphabetically. No aggregate counts, no comment header. The same
# format is stored as the committed *expected-failures* file
# (`.github/statetests-expected-failures.txt`): merges stay conflict-free
# because each fixed test removes exactly one line at a known sorted position
# and each new failure inserts one, with nothing in between that both branches
# touch. Regenerate the committed file after an intentional change:
#
#   .github/scripts/statetests_summary.sh <raw> > .github/statetests-expected-failures.txt
#
# INCON tests are intentionally listed (unlike the older baseline format):
# recording their tier catches INCON -> FAIL regressions that a FAIL-only file
# would silently miss. Passing tests are omitted.
#
# Usage: statetests_summary.sh <raw-output-file>
set -euo pipefail

raw="${1:?usage: statetests_summary.sh <raw-output-file>}"

# Sanity: refuse to emit an empty summary for an incomplete run.
if ! grep -qE 'pass\(root=[0-9]+ full\+=[0-9]+ core\+=[0-9]+\) fail=[0-9]+' "$raw"; then
  echo "statetests_summary.sh: no aggregate 'pass(root=… full+=… core+=…) fail=…' line" \
       "found in '$raw' — the run is incomplete or its output format changed." >&2
  exit 2
fi

# Per-test notes look like:  "FAIL callcodeEmpty…_Constantinople: <msg>"
# Emit `<id>: <tier>`, dropping the trailing message so reworded diagnostics
# do not register as spurious churn.
# `|| true`: a run with zero FAIL/INCON/CRASH tests makes `grep` exit 1;
# without this, `set -o pipefail` would fail the whole script after a valid run.
{ grep -E '^(FAIL|INCON|CRASH) ' "$raw" || true; } \
  | sed -E 's/^(FAIL|INCON|CRASH) ([^:]+):.*/\2: \1/' \
  | sort -u
