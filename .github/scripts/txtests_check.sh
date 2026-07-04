#!/usr/bin/env bash
#
# Compare a freshly generated txtests summary against the committed
# *expected-failures* file (sorted "<id>: <tier>" lines) and emit a Markdown
# regression report on stdout (for $GITHUB_STEP_SUMMARY).
#
# This is a HYBRID report/gate: regressions whose *new* tier is FAIL or
# CRASH (correctness) exit 1 and fail the shard; INCON-tier regressions
# (e.g. walltimeout flapping under CPU load) are surfaced as
# GitHub `::warning::` annotations. Regression / improvement classification is
# tier-aware (severity order: pass < INCON < FAIL < CRASH), so INCON -> FAIL,
# FAIL -> CRASH, and pass -> anything all count as regressions.
#
# The aggregate count table is read from the runner's raw output, so the
# committed file never contains numbers that different branches would both
# touch.
#
# Usage: txtests_check.sh <expected-failures-file> <current-summary-file> <raw-output-file>
set -uo pipefail

expected="${1:?usage: txtests_check.sh <expected> <current> <raw>}"
current="${2:?usage: txtests_check.sh <expected> <current> <raw>}"
raw="${3:?usage: txtests_check.sh <expected> <current> <raw>}"

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

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

total_line="$(grep -E 'pass=[0-9]+ fail=[0-9]+ incon=[0-9]+ crash=[0-9]+' "$raw" | tail -1 || true)"
num() { sed -nE "s/.*[ (]?$1=([0-9]+).*/\1/p" <<<"$total_line"; }

echo "## TransactionTests regression report"
echo
echo "_ethereum/tests \`TransactionTests\` run against the transaction decoder /"
echo "validator (RLP decode, EIP-155 & typed signing-hash sender recovery, tx"
echo "hash, intrinsic gas, static validity). Legacy + EIP-2930 + EIP-1559 +"
echo "EIP-7702 are checked; EIP-4844 (0x03) and reserved type bytes activated at"
echo "a fork are reported \`incon\`. Non-gating._"
echo
if [ -n "$total_line" ]; then
  echo "| metric | count |"
  echo "| --- | ---: |"
  for key in pass fail incon crash; do
    echo "| \`$key\` | $(num "$key") |"
  done
  echo "| \`total\` | $(sed -nE 's/.*total ([0-9]+).*/\1/p' <<<"$total_line") |"
  echo
else
  echo "> Note: no aggregate line found in the raw output — count table omitted."
  echo
fi

gating=0
if [ "${#regressions[@]}" -gt 0 ]; then
  echo "### ⚠️ ${#regressions[@]} regression(s) — worse tier than expected"
  echo
  for line in "${regressions[@]}"; do
    read -r _ id b c <<<"$line"
    echo "- \`$id\`: expected \`$b\`, got \`$c\`"
    case "$c" in
      FAIL|CRASH)
        echo "::error title=TransactionTests correctness regression::$id regressed ($b -> $c)"
        gating=1 ;;
      *)
        echo "::warning title=TransactionTests regression::$id regressed ($b -> $c)" ;;
    esac
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
  echo "> \`.github/scripts/txtests_summary.sh <raw> > .github/txtests-expected-failures.txt\`"
  echo
fi

# GATE: a regression whose *new* tier is FAIL or CRASH is a correctness
# regression and fails the shard. Regressions that only land at INCON (e.g.
# the known walltimeout perf incons flapping under CPU load) stay
# warnings-only, as do improvements.
if [ "$gating" -ne 0 ]; then
  echo "⛔ Correctness regression(s) — new tier FAIL/CRASH — failing this shard."
  exit 1
fi
exit 0
