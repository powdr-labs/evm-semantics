#!/usr/bin/env bash
#
# Compare a freshly generated gstatetests summary against the committed baseline
# and emit a Markdown regression report on stdout (for $GITHUB_STEP_SUMMARY).
#
# This job is a REPORT (non-gating): it exits 0 and only surfaces regressions as
# GitHub `::warning::` annotations. A regression is an id-level transition — a
# test that was NOT FAILing in the baseline now FAILs (produces a wrong answer).
# It keys on the FAIL id set, not on count deltas, so a wall-timeout flip
# (pass/core -> incon on a slow runner) does NOT register as a regression.
#
# Usage: gstatetests_check.sh <baseline-file> <current-summary-file>
set -uo pipefail

baseline="${1:?usage: gstatetests_check.sh <baseline> <current>}"
current="${2:?usage: gstatetests_check.sh <baseline> <current>}"

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

grep '^test=' "$baseline" | sort -u > "$tmp/base.set"
grep '^test=' "$current"  | sort -u > "$tmp/cur.set"

# Regressions: FAIL now, but not FAIL in the baseline (i.e. used to pass/incon).
mapfile -t regressions < <(comm -13 "$tmp/base.set" "$tmp/cur.set" | sed 's/^test=//')
# Improvements: FAIL in the baseline, but not FAIL now.
mapfile -t improvements < <(comm -23 "$tmp/base.set" "$tmp/cur.set" | sed 's/^test=//')

cval() { sed -nE "s/^$2=([0-9]+)$/\1/p" "$1"; }

echo "## GeneralStateTests (modern) regression report"
echo
echo "_Modern \`ethereum/tests\` GeneralStateTests (\`state_test\` fixtures,"
echo "curated subset) run against the evaluator. \`core\` = storage/nonce/code"
echo "match; \`full\` also requires exact balances; \`root\` additionally requires"
echo "the world MPT \`stateRoot\` to match the fixture's \`hash\`. Non-gating._"
echo
echo "| metric | baseline | current | Δ |"
echo "| --- | ---: | ---: | ---: |"
for key in pass_root pass_full pass_core fail incon crash total; do
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
    echo "::warning title=GeneralStateTests regression::$t was not FAILing in the baseline and now FAILs"
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
  echo "> \`.github/scripts/gstatetests_summary.sh <raw-output> > .github/gstatetests-baseline.txt\`"
  echo
fi

exit 0
