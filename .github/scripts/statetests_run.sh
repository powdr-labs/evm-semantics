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
# Progress output goes to **stderr** (not the summary-parseable stdout):
#   * every `LOG_EVERY` completed files a `[i/N …s elapsed]` line
#   * every file that takes more than `LOG_SLOW_MS` prints its wall time
#   * final "top slowest" report after all workers finish
# Tuning knobs:
#   `LOG_EVERY`   (default 200)  — heartbeat interval (files).
#   `LOG_SLOW_MS` (default 1000) — print per-file line if the file took ≥ this.
#   `LOG_TOP_N`   (default 20)   — how many entries in the tail summary.
#
# Usage: statetests_run.sh <dir> [per-file-timeout-secs] [parallelism]
#        statetests_run.sh --one <file> <cap>     (internal worker mode)
set -uo pipefail

BIN="${STATETESTS_BIN:-./.lake/build/bin/statetests}"

# Worker mode: run a single file, emitting its -v notes + per-file aggregate,
# or a synthesized wall-timeout incon if it exceeds the cap. Also emits a
# timing line to `PROGRESS_FD` (fd 3, connected to a per-file log the parent
# scrapes for progress + tail reporting).
if [ "${1:-}" = "--one" ]; then
  f="$2"; cap="$3"
  s=$(date +%s%N)
  out="$(timeout "$cap" "$BIN" -v "$f" 2>&1)"
  rc=$?
  e=$(date +%s%N)
  ms=$(( (e - s) / 1000000 ))
  if [ "$rc" -eq 124 ]; then
    echo "INCON $(basename "$f" .json)_Constantinople: wall-timeout (>${cap}s)"
    echo "pass(root=0 full+=0 core+=0) fail=0 incon=1 crash=0 (total 1)"
    printf 'TIMEOUT\t%d\t%s\n' "$ms" "$f" >&3
  else
    echo "$out"
    printf 'OK\t%d\t%s\n' "$ms" "$f" >&3
  fi
  exit 0
fi

dir="${1:?usage: statetests_run.sh <dir> [timeout] [parallelism]}"
cap="${2:-60}"
par="${3:-$(nproc 2>/dev/null || echo 4)}"
LOG_EVERY="${LOG_EVERY:-200}"
LOG_SLOW_MS="${LOG_SLOW_MS:-1000}"
LOG_TOP_N="${LOG_TOP_N:-20}"
self="$(realpath "$0")"

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT

# Enumerate files up-front so we know the total; keep sorted so ordering is
# deterministic across runs.
find "$dir" -name '*.json' | sort > "$work/files"
total=$(wc -l < "$work/files")
run_start=$(date +%s)
echo "[statetests] $total tests, par=$par, cap=${cap}s" >&2

# Fan out one worker per file. Each worker writes one line to $work/progress
# (via fd 3) as it completes; we tail that in the background to emit heartbeat
# / slow-file lines to stderr in real time.
: > "$work/progress"

# Background tail: reads worker completion lines and emits progress to stderr.
(
  count=0
  awk_prog='
    /^OK\t/     { print; fflush() }
    /^TIMEOUT\t/{ print; fflush() }
  '
  # `tail -F` follows the file even before it exists; `--pid=$$` would need
  # the parent PID, but the trap on EXIT will kill the tail via the subshell.
  tail -n +1 -F "$work/progress" 2>/dev/null | while IFS=$'\t' read -r tag ms path; do
    count=$((count + 1))
    base="${path##*/GeneralStateTests/}"
    if [ "$tag" = "TIMEOUT" ] || [ "$ms" -ge "$LOG_SLOW_MS" ]; then
      # Slow / timed-out files get their own line.
      elapsed=$(( $(date +%s) - run_start ))
      printf '  [%5ds] %5dms %s  %s\n' "$elapsed" "$ms" "$tag" "$base" >&2
    fi
    if [ "$((count % LOG_EVERY))" = 0 ] || [ "$count" = "$total" ]; then
      elapsed=$(( $(date +%s) - run_start ))
      printf '[%5ds] %d/%d done\n' "$elapsed" "$count" "$total" >&2
    fi
  done
) &
tail_pid=$!
# Kill the background tail on exit even if we die abnormally. Overrides the
# earlier trap that only cleaned up `$work`.
trap 'kill $tail_pid 2>/dev/null; rm -rf "$work"' EXIT

# Dispatch: 3-> progress pipe so workers can write timing lines to it.
xargs -a "$work/files" -P "$par" -I{} bash -c \
  '"$0" --one "$1" "$2" 3>>"$3"' \
  "$self" {} "$cap" "$work/progress" > "$work/raw"

# Give the progress tail a moment to catch up, then stop it.
sleep 0.5
kill "$tail_pid" 2>/dev/null || true
wait "$tail_pid" 2>/dev/null || true

# Final "top-N slowest" summary (stderr).
{
  echo "[statetests] top-$LOG_TOP_N slowest files:"
  sort -k2 -rn "$work/progress" \
    | head -n "$LOG_TOP_N" \
    | awk -F'\t' '{ printf "  %6d ms  %-8s %s\n", $2, $1, $3 }'
  elapsed=$(( $(date +%s) - run_start ))
  echo "[statetests] wall clock: ${elapsed}s"
} >&2

# Per-test notes (stable order).
grep -E '^(FAIL|INCON|CRASH) ' "$work/raw" | sort || true

# Fold the per-file aggregate lines into one total (portable sed + awk).
grep 'pass(root=' "$work/raw" \
  | sed -E 's/pass\(root=([0-9]+) full\+=([0-9]+) core\+=([0-9]+)\) fail=([0-9]+) incon=([0-9]+) crash=([0-9]+).*/\1 \2 \3 \4 \5 \6/' \
  | awk '{pr+=$1; pf+=$2; pc+=$3; f+=$4; ic+=$5; cr+=$6}
         END { printf "pass(root=%d full+=%d core+=%d) fail=%d incon=%d crash=%d (total %d)\n",
                      pr, pf, pc, f, ic, cr, pr+pf+pc+f+ic+cr }'
