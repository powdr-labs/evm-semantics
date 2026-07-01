#!/usr/bin/env bash
#
# Compare a freshly generated statetests summary against the committed
# *expected-failures* file (sorted "<id>: <tier>" lines) and emit a Markdown
# regression report on stdout (for $GITHUB_STEP_SUMMARY).
#
# By default this is a REPORT: it exits 0 and only surfaces regressions as
# GitHub `::warning::` annotations. With `--strict` it becomes a GATE: it exits
# 1 if there is any regression — a test that ran at a *worse* tier than
# expected (severity order: pass < INCON < FAIL < CRASH).
#
# Regression / improvement classification is tier-aware, not just id-set
# membership. Examples:
#   expected `foo: INCON`, current `foo: FAIL` — regression (INCON -> FAIL).
#   expected `foo: FAIL`,  current absent      — improvement (FAIL -> pass).
#   expected absent,       current `foo: INCON`— regression (pass -> INCON).
#
# The aggregate count table (pass_root / pass_full / pass_core / fail / …) is
# read directly from the runner's raw output rather than a committed baseline,
# so the committed file never contains numbers that different branches would
# both touch.
#
# Usage: statetests_check.sh [--strict] <expected-failures-file> <current-summary-file> <raw-output-file>
set -uo pipefail

strict=0
if [ "${1:-}" = "--strict" ]; then strict=1; shift; fi

expected="${1:?usage: statetests_check.sh [--strict] <expected> <current> <raw>}"
current="${2:?usage: statetests_check.sh [--strict] <expected> <current> <raw>}"
raw="${3:?usage: statetests_check.sh [--strict] <expected> <current> <raw>}"

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

# Tier-aware diff of expected vs current. Each output line is one of:
#   REG <id> <expected-tier> <current-tier>       — regression (worse now)
#   IMP <id> <expected-tier> <current-tier>       — improvement (better now)
# `pass` is the sentinel for "not listed" (i.e. the test passes cleanly).
awk '
  BEGIN { sev["pass"]=0; sev["INCON"]=1; sev["FAIL"]=2; sev["CRASH"]=3 }
  function tier(line, a) { split(line, a, ": "); return a[2] }
  function id(line, a)   { split(line, a, ": "); return a[1] }
  FNR==NR { base[id($0)] = tier($0); next }
  {
    i = id($0); c = tier($0); b = (i in base) ? base[i] : "pass"
    delete base[i]
    if (sev[c] > sev[b]) print "REG " i " " b " " c
    else if (sev[c] < sev[b]) print "IMP " i " " b " " c
  }
  END {
    for (i in base) print "IMP " i " " base[i] " pass"
  }
' "$expected" "$current" | sort -u > "$tmp/diff"

mapfile -t regressions < <(grep '^REG ' "$tmp/diff" || true)
mapfile -t improvements < <(grep '^IMP ' "$tmp/diff" || true)

# Aggregate table lives in the raw output, not any committed file.
total_line="$(grep -E 'pass\(root=[0-9]+ full\+=[0-9]+ core\+=[0-9]+\) fail=[0-9]+' "$raw" | tail -1 || true)"
num() { sed -nE "s/.*[ (]$1=([0-9]+).*/\1/p" <<<"$total_line"; }

echo "## StateTests regression report"
echo
echo "_BlockchainTests GeneralStateTests (curated subset) run against the"
echo "evaluator. \`core\` = storage/nonce/code match; \`full\` also"
echo "requires exact balances; \`root\` additionally requires the world"
echo "MPT \`stateRoot\` to match the corpus's blockHeader._"
echo
if [ -n "$total_line" ]; then
  echo "| metric | count |"
  echo "| --- | ---: |"
  for key in pass_root:root pass_full:'full\+' pass_core:'core\+' fail:fail incon:incon crash:crash; do
    label="${key%%:*}"; pat="${key##*:}"
    echo "| \`$label\` | $(num "$pat") |"
  done
  echo "| \`total\` | $(sed -nE 's/.*total ([0-9]+).*/\1/p' <<<"$total_line") |"
  echo
else
  echo "> Note: no aggregate line found in the raw output — count table omitted."
  echo
fi

if [ "${#regressions[@]}" -gt 0 ]; then
  echo "### ⚠️ ${#regressions[@]} regression(s) — worse tier than expected"
  echo
  for line in "${regressions[@]}"; do
    read -r _ id b c <<<"$line"
    echo "- \`$id\`: expected \`$b\`, got \`$c\`"
    echo "::warning title=StateTests regression::$id regressed ($b -> $c)"
  done
  echo
else
  echo "### ✅ No regressions"
  echo
fi

if [ "${#improvements[@]}" -gt 0 ]; then
  echo "### 🎉 ${#improvements[@]} improvement(s) — better tier than expected"
  echo
  for line in "${improvements[@]}"; do
    read -r _ id b c <<<"$line"
    echo "- \`$id\`: expected \`$b\`, got \`$c\`"
  done
  echo
  echo "> Refresh the expected-failures file once these are intentional:"
  echo "> \`.github/scripts/statetests_summary.sh <raw> > .github/statetests-expected-failures.txt\`"
  echo
fi

if [ "$strict" -eq 1 ] && [ "${#regressions[@]}" -gt 0 ]; then
  echo "::error title=StateTests::${#regressions[@]} test(s) regressed; failing the build."
  exit 1
fi
exit 0
