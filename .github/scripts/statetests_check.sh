#!/usr/bin/env bash
#
# Compare a freshly generated statetests summary against the committed baseline
# and emit a Markdown regression report on stdout (for $GITHUB_STEP_SUMMARY).
#
# By default this is a REPORT: it exits 0 and only surfaces regressions as
# GitHub `::warning::` annotations. With `--strict` it becomes a GATE: it exits
# 1 if there is an id-level regression — a test that was NOT FAILing in the
# baseline now FAILs (i.e. produces a wrong answer). Gating keys on the FAIL id
# set, not on count deltas, so a wall-timeout flip (pass/core -> incon on a slow
# runner) does NOT fail the build — only a genuine pass -> FAIL does.
#
# Usage: statetests_check.sh [--strict] <baseline-file> <current-summary-file>
set -uo pipefail

strict=0
if [ "${1:-}" = "--strict" ]; then strict=1; shift; fi

baseline="${1:?usage: statetests_check.sh [--strict] <baseline> <current>}"
current="${2:?usage: statetests_check.sh [--strict] <baseline> <current>}"

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

grep '^test=' "$baseline" | sort -u > "$tmp/base.set"
grep '^test=' "$current"  | sort -u > "$tmp/cur.set"

# Regressions: FAIL now, but not FAIL in the baseline (i.e. used to pass/incon).
mapfile -t regressions < <(comm -13 "$tmp/base.set" "$tmp/cur.set" | sed 's/^test=//')
# Improvements: FAIL in the baseline, but not FAIL now.
mapfile -t improvements < <(comm -23 "$tmp/base.set" "$tmp/cur.set" | sed 's/^test=//')

cval() { sed -nE "s/^$2=([0-9]+)$/\1/p" "$1"; }

echo "## StateTests regression report"
echo
echo "_BlockchainTests GeneralStateTests (curated subset) run against the"
echo "evaluator. \`core\` = storage/nonce/code match; \`full\` also"
echo "requires exact balances. Non-gating._"
echo
echo "| metric | baseline | current | Δ |"
echo "| --- | ---: | ---: | ---: |"
for key in pass_full pass_core fail incon crash total; do
  b="$(cval "$baseline" "$key")"; c="$(cval "$current" "$key")"
  b="${b:-0}"; c="${c:-0}"
  d=$((c - b))
  [ "$d" -gt 0 ] && d="+$d"
  echo "| \`$key\` | $b | $c | $d |"
done
echo

if [ "${#regressions[@]}" -gt 0 ]; then
  echo "### ⚠️ ${#regressions[@]} regression(s) — previously passing/incon, now FAIL"
  echo
  for t in "${regressions[@]}"; do
    echo "- \`$t\`"
    echo "::warning title=StateTests regression::$t was not FAILing in the baseline and now FAILs"
  done
  echo
else
  echo "### ✅ No regressions (no previously-non-FAIL test now fails)"
  echo
fi

if [ "${#improvements[@]}" -gt 0 ]; then
  echo "### 🎉 ${#improvements[@]} improvement(s) — baseline FAIL no longer failing"
  echo
  for t in "${improvements[@]}"; do echo "- \`$t\`"; done
  echo
  echo "> Refresh the baseline once these are intentional:"
  echo "> \`.github/scripts/statetests_summary.sh <raw-output> > .github/statetests-baseline.txt\`"
  echo
fi

# Gate (only with --strict): fail iff a previously-non-FAIL test now FAILs.
if [ "$strict" -eq 1 ] && [ "${#regressions[@]}" -gt 0 ]; then
  echo "::error title=StateTests::${#regressions[@]} CALL test(s) regressed (pass -> FAIL); failing the build."
  exit 1
fi
exit 0
