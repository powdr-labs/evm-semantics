#!/usr/bin/env bash
#
# Run the modern BlockchainTests file-by-file in separate processes, with a
# per-file wall-clock cap, in parallel, and emit raw output that
# `blockchaintests_summary.sh` can parse:
#   * per-test `FAIL <id>: …` / `INCON <id>: …` notes, and
#   * a final aggregate `pass(root=A full+=B core+=C) fail=D incon=E crash=F (total N)`.
#
# Why per-file subprocesses rather than one whole-dir invocation: `blockchaintests`
# runs each file as an in-process Lean `Task`, so a hard panic in ONE
# pathological test (e.g. a huge-memory-offset test that hits the evaluator's
# unbounded `readPadded`/`writeBytes` allocation → `INTERNAL PANIC: out of
# memory`) aborts the WHOLE run. Isolating each file in its own process
# contains such a panic: that file is recorded as a `crash`, its slot freed, and
# the rest of the corpus still runs. A `timeout` additionally bounds the handful
# of genuinely slow tests (recorded as `incon` wall-timeout) so CI can't hang.
#
# Usage: blockchaintests_run.sh <dir> [per-file-timeout-secs] [parallelism]
#        blockchaintests_run.sh --one <file> <cap>     (internal worker mode)
set -uo pipefail

BIN="${BLOCKCHAINTESTS_BIN:-./.lake/build/bin/blockchaintests}"

# Worker mode: run a single file in its own process, emitting its -v notes +
# per-file aggregate. A timeout (exit 124) becomes an INCON wall-timeout; any
# other non-zero exit (a panic/OOM that killed the process before it could
# print its own aggregate) becomes a CRASH — both synthesised with a per-file
# aggregate line so the fold in dir mode still sees one line per file.
if [ "${1:-}" = "--one" ]; then
  f="$2"; cap="$3"
  base="$(basename "$f" .json)"
  out="$(timeout "$cap" "$BIN" -v "$f" 2>&1)"; ec=$?
  if [ "$ec" -eq 124 ]; then
    echo "INCON ${base}_walltimeout: wall-timeout (>${cap}s)"
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

dir="${1:?usage: blockchaintests_run.sh <dir> [timeout] [parallelism]}"
cap="${2:-45}"
par="${3:-4}"
self="$(realpath "$0")"

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

# Fan out one worker per file (`blockchaintests_run.sh --one`), `par` at a time.
find "$dir" -name '*.json' | sort \
  | BLOCKCHAINTESTS_BIN="$BIN" xargs -P "$par" -I{} "$self" --one {} "$cap" > "$work/raw"

# Per-test notes (stable order).
grep -E '^(FAIL|INCON|CRASH) ' "$work/raw" | sort || true

# Fold the per-file aggregate lines into one total (portable sed + awk).
grep 'pass(root=' "$work/raw" \
  | sed -E 's/pass\(root=([0-9]+) full\+=([0-9]+) core\+=([0-9]+)\) fail=([0-9]+) incon=([0-9]+) crash=([0-9]+).*/\1 \2 \3 \4 \5 \6/' \
  | awk '{pr+=$1; pf+=$2; pc+=$3; f+=$4; ic+=$5; cr+=$6}
         END { printf "pass(root=%d full+=%d core+=%d) fail=%d incon=%d crash=%d (total %d)\n",
                      pr, pf, pc, f, ic, cr, pr+pf+pc+f+ic+cr }'
