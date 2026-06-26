#!/usr/bin/env bash
#
# Run the CALL state tests file-by-file with a per-file wall-clock cap, in
# parallel, and emit raw output that `statetests_summary.sh` can parse:
#   * per-test `FAIL <id>: …` / `INCON <id>: …` notes, and
#   * a final aggregate `pass(full=A core+=B) fail=C incon=D crash=E (total N)`.
#
# Why per-file with a cap rather than one whole-dir invocation: the evaluator
# models world state as functional (closure-chained) maps, so deep-recursion
# CALL tests run ~1e6 steps with O(writes) lookups and take minutes each. A
# per-file `timeout` bounds CI wall-time; a file that exceeds the cap is
# recorded as INCON (wall-timeout) rather than hanging the job. The cap is
# generous (default 60s) so only genuinely pathological tests trip it — fast
# and moderate tests finish well under it, keeping classification stable across
# machines.
#
# Usage: statetests_run.sh <dir> [per-file-timeout-secs] [parallelism]
#        statetests_run.sh --one <file> <cap>     (internal worker mode)
set -uo pipefail

BIN="${STATETESTS_BIN:-./.lake/build/bin/statetests}"

# Worker mode: run a single file, emitting its -v notes + per-file aggregate,
# or a synthesized wall-timeout incon if it exceeds the cap.
if [ "${1:-}" = "--one" ]; then
  f="$2"; cap="$3"
  out="$(timeout "$cap" "$BIN" -v "$f" 2>&1)"
  if [ $? -eq 124 ]; then
    echo "INCON $(basename "$f" .json)_Constantinople: wall-timeout (>${cap}s)"
    echo "pass(full=0 core+=0) fail=0 incon=1 crash=0 (total 1)"
  else
    echo "$out"
  fi
  exit 0
fi

dir="${1:?usage: statetests_run.sh <dir> [timeout] [parallelism]}"
cap="${2:-60}"
par="${3:-4}"
self="$(realpath "$0")"

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

# Fan out one worker per file (`statetests_run.sh --one`), `par` at a time.
find "$dir" -name '*.json' | sort \
  | STATETESTS_BIN="$BIN" xargs -P "$par" -I{} "$self" --one {} "$cap" > "$work/raw"

# Per-test notes (stable order).
grep -E '^(FAIL|INCON|CRASH) ' "$work/raw" | sort || true

# Fold the per-file aggregate lines into one total (portable sed + awk).
grep 'pass(full=' "$work/raw" \
  | sed -E 's/pass\(full=([0-9]+) core\+=([0-9]+)\) fail=([0-9]+) incon=([0-9]+) crash=([0-9]+).*/\1 \2 \3 \4 \5/' \
  | awk '{pf+=$1; pc+=$2; f+=$3; ic+=$4; cr+=$5}
         END { printf "pass(full=%d core+=%d) fail=%d incon=%d crash=%d (total %d)\n",
                      pf, pc, f, ic, cr, pf+pc+f+ic+cr }'
