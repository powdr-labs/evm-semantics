#!/usr/bin/env bash
#
# Compare a freshly generated trietests summary against the committed
# *expected-failures* file (sorted "<id>: <tier>" lines) and emit a Markdown
# regression report on stdout (for $GITHUB_STEP_SUMMARY).
#
# Same tier-aware diff as txtests_check.sh (the trietests runner emits the
# txtests output format, and txtests_summary.sh produces the summary); only
# the report title/description differ.
#
# Usage: trietests_check.sh <expected-failures-file> <current-summary-file> <raw-output-file>
set -uo pipefail

expected="${1:?usage: trietests_check.sh <expected> <current> <raw>}"
current="${2:?usage: trietests_check.sh <expected> <current> <raw>}"
raw="${3:?usage: trietests_check.sh <expected> <current> <raw>}"

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

echo "## TrieTests regression report"
echo
echo "_ethereum/tests \`TrieTests\` run against the MPT (\`EvmSemantics.Mpt\`,"
echo "the trie behind the \`passRoot\` tier of every state/blockchain runner):"
echo "fold each fixture's key/value operations (ordered lists with deletes, or"
echo "any-order objects; \`*secureTrie*\` fixtures keccak the keys) and compare"
echo "the resulting canonical root hash. \`trietestnextprev\` (iterator"
echo "semantics we don't model) is reported \`incon\`. Non-gating._"
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

if [ "${#regressions[@]}" -gt 0 ]; then
  echo "### ⚠️ ${#regressions[@]} regression(s) — worse tier than expected"
  echo
  for line in "${regressions[@]}"; do
    read -r _ id b c <<<"$line"
    echo "- \`$id\`: expected \`$b\`, got \`$c\`"
    echo "::warning title=TrieTests regression::$id regressed ($b -> $c)"
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
  echo "> \`.github/scripts/txtests_summary.sh <raw> > .github/trietests-expected-failures.txt\`"
  echo
fi

exit 0
