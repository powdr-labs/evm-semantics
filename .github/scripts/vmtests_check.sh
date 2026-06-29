#!/usr/bin/env bash
#
# Compare a freshly generated vmtests summary against the committed baseline and
# emit a Markdown regression report on stdout (intended for $GITHUB_STEP_SUMMARY).
#
# This is a REPORT, not a gate: it always exits 0. Regressions are surfaced as
# GitHub `::warning::` annotations and in the report, but never fail the job.
#
# Usage: vmtests_check.sh <baseline-file> <current-summary-file>
set -uo pipefail

baseline="${1:?usage: vmtests_check.sh <baseline> <current>}"
current="${2:?usage: vmtests_check.sh <baseline> <current>}"

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

grep '^test=' "$baseline" | sort -u > "$tmp/base.set"
grep '^test=' "$current"  | sort -u > "$tmp/cur.set"

# Regressions: non-passing now, but not in the baseline (i.e. were passing).
mapfile -t regressions < <(comm -13 "$tmp/base.set" "$tmp/cur.set" | sed 's/^test=//')
# Improvements: in the baseline's non-passing set, but passing now.
mapfile -t improvements < <(comm -23 "$tmp/base.set" "$tmp/cur.set" | sed 's/^test=//')

cval() { sed -nE "s/^$2=([0-9]+)$/\1/p" "$1"; }

echo "## VMTests regression report"
echo
echo "_Full ethereum/legacytests VMTests suite, run against the evaluator. Non-gating._"
echo
echo "| metric | baseline | current | Δ |"
echo "| --- | ---: | ---: | ---: |"
for key in pass fail crash incon total; do
  b="$(cval "$baseline" "$key")"; c="$(cval "$current" "$key")"
  b="${b:-0}"; c="${c:-0}"
  d=$((c - b))
  [ "$d" -gt 0 ] && d="+$d"
  echo "| \`$key\` | $b | $c | $d |"
done
echo

if [ "${#regressions[@]}" -gt 0 ]; then
  echo "### ⚠️ ${#regressions[@]} regression(s) — previously passing, now FAIL/CRASH"
  echo
  for t in "${regressions[@]}"; do
    echo "- \`$t\`"
    echo "::warning title=VMTests regression::$t was passing in the baseline and now FAILs/CRASHes"
  done
  echo
else
  echo "### ✅ No regressions (no previously-passing test now fails or crashes)"
  echo
fi

if [ "${#improvements[@]}" -gt 0 ]; then
  echo "### 🎉 ${#improvements[@]} improvement(s) — baseline FAIL/CRASH now passing"
  echo
  for t in "${improvements[@]}"; do echo "- \`$t\`"; done
  echo
  echo "> Refresh the baseline once these are intentional:"
  echo "> \`.github/scripts/vmtests_summary.sh <raw-output> > .github/vmtests-baseline.txt\`"
  echo
fi

exit 0
