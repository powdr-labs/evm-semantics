#!/usr/bin/env bash
#
# Run the CALL state tests file-by-file with a per-file wall-clock cap, in
# parallel, and emit raw output that `statetests_summary.sh` can parse:
#   * per-test `FAIL <id>: …` / `INCON <id>: …` notes, and
#   * a final aggregate `pass(root=A full+=B core+=C) fail=D incon=E crash=F (total N)`.
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

# Worker mode: run a single file, emitting its -v notes + per-file aggregate.
# A timeout (exit 124) becomes an INCON wall-timeout; any other non-zero exit
# without an aggregate line (a panic/OOM that killed the process before it
# could print one) becomes a CRASH — both synthesised with a per-file
# aggregate so the fold in dir mode still sees one line per file and the
# strict gate can't silently drop a crashed file. (Same containment as
# gstatetests_run.sh.)
if [ "${1:-}" = "--one" ]; then
  f="$2"; cap="$3"
  base="$(basename "$f" .json)"
  out="$(timeout "$cap" "$BIN" -v "$f" 2>&1)"; ec=$?
  if [ "$ec" -eq 124 ]; then
    echo "INCON ${base}_Constantinople: wall-timeout (>${cap}s)"
    echo "pass(root=0 full+=0 core+=0) fail=0 incon=1 crash=0 (total 1)"
  elif [ "$ec" -ne 0 ] && ! echo "$out" | grep -q 'pass(root='; then
    # Non-zero exit and no aggregate printed ⇒ the process died (panic/OOM).
    echo "$out" | grep -iE 'panic|error' | head -1 | sed "s/^/CRASH ${base}_crash: /"
    echo "CRASH ${base}_crash: process exited $ec without an aggregate"
    echo "pass(root=0 full+=0 core+=0) fail=0 incon=0 crash=1 (total 1)"
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

# Guard against silently dropped files: every corpus file must have produced
# a per-file aggregate line (the worker synthesises one even on timeout or
# crash). If any are missing (e.g. a worker was killed before it could print),
# count them as crashes so the strict gate sees them instead of a silently
# shrunken total.
files=$(find "$dir" -name '*.json' | wc -l)
aggs=$(grep -c 'pass(root=' "$work/raw" || true)
if [ "$aggs" -lt "$files" ]; then
  missing=$((files - aggs))
  {
    echo "CRASH corpus_files_missing_aggregate: $missing of $files corpus files produced no aggregate"
    echo "pass(root=0 full+=0 core+=0) fail=0 incon=0 crash=$missing (total $missing)"
  } >> "$work/raw"
fi

# Per-test notes (stable order).
grep -E '^(FAIL|INCON|CRASH) ' "$work/raw" | sort || true

# Fold the per-file aggregate lines into one total (portable sed + awk).
grep 'pass(root=' "$work/raw" \
  | sed -E 's/pass\(root=([0-9]+) full\+=([0-9]+) core\+=([0-9]+)\) fail=([0-9]+) incon=([0-9]+) crash=([0-9]+).*/\1 \2 \3 \4 \5 \6/' \
  | awk '{pr+=$1; pf+=$2; pc+=$3; f+=$4; ic+=$5; cr+=$6}
         END { printf "pass(root=%d full+=%d core+=%d) fail=%d incon=%d crash=%d (total %d)\n",
                      pr, pf, pc, f, ic, cr, pr+pf+pc+f+ic+cr }'
