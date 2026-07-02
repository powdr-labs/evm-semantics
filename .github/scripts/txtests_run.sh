#!/usr/bin/env bash
#
# Run the ethereum/tests TransactionTests suite and emit raw output that
# `txtests_summary.sh` can parse:
#   * per-test `FAIL <id>: …` / `INCON <id>: …` / `CRASH <id>: …` notes, and
#   * a final aggregate `pass=A fail=B incon=C crash=D (total N)`.
#
# Unlike the state-test runners, TransactionTests only *decode and validate*
# transactions — no EVM execution — so there is no per-test memory/panic risk
# that would need per-file subprocess isolation. A single whole-directory
# invocation is sufficient: the runner already fans out one Lean `Task` per
# file, catches a malformed JSON file as a per-file `CRASH`, and prints the
# aggregate line the summary script keys on.
#
# Usage: txtests_run.sh <dir> [parallelism]
set -uo pipefail

BIN="${TXTESTS_BIN:-./.lake/build/bin/txtests}"
dir="${1:?usage: txtests_run.sh <dir> [parallelism]}"
par="${2:-8}"

TXTESTS_JOBS="$par" "$BIN" -v "$dir"
