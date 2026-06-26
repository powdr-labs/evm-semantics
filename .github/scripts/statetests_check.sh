#!/usr/bin/env bash
#
# Compare a freshly generated statetests summary against the committed baseline
# and emit a Markdown regression report on stdout (for $GITHUB_STEP_SUMMARY).
#
# This is a REPORT, not a gate: it always exits 0. Regressions are surfaced as
# GitHub `::warning::` annotations and in the report, but never fail the job.
#
# Usage: statetests_check.sh <baseline-file> <current-summary-file>
set -uo pipefail

baseline="${1:?usage: statetests_check.sh <baseline> <current>}"
current="${2:?usage: statetests_check.sh <baseline> <current>}"

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

grep '^test=' "$baseline" | sort -u > "$tmp/base.set"
grep '^test=' "$current"  | sort -u > "$tmp/cur.set"

# Regressions: FAIL now, but not FAIL in the baseline (i.e. used to pass/incon).
mapfile -t regressions < <(comm -13 "$tmp/base.set" "$tmp/cur.set" | sed 's/^test=//')
# Improvements: FAIL in the baseline, but not FAIL now.
mapfile -t improvements < <(comm -23 "$tmp/base.set" "$tmp/cur.set" | sed 's/^test=//')

cval() { sed -nE "s/^$2=([0-9]+)$/\1/p" "$1"; }

echo "## StateTests (CALL) regression report"
echo
echo "_BlockchainTests \`stCall*\` suites (Constantinople variant) run against the"
echo "recursive-CALL evaluator. \`core\` = storage/nonce/code match; \`full\` also"
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

exit 0
