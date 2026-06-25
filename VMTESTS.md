# VMTests harness

`VMRunner.lean` (executable `vmtests`) runs the legacy ethereum/tests **VMTests**
suite against the verified evaluator (`stepF` / `run`). VMTests is the suite that
matches this evaluator's scope: single-frame EVM execution, no inter-contract
calls, no transaction processing, uniform gas.

## How to run
```
# one-time: fetch the corpus (the LegacyTests/ dir in ethereum/tests is a
# submodule that points at this repo)
git clone --depth 1 https://github.com/ethereum/legacytests

lake build vmtests
./.lake/build/bin/vmtests <path>/legacytests/Constantinople/VMTests
# single test:
./.lake/build/bin/vmtests --file <path>/.../add0.json
```
Each test runs in its own child process (`--file` mode), so an evaluator panic or
hang only loses that one test instead of aborting the whole run.

## Current results (609 tests)
Will be refreshed once the memory-expansion-gas branch is merged and the
baseline regenerated. Pre-merge counts on `origin/main`:
```
pass=533  fail=0  skip=31 (unsup=6 keccak=23 gas=2)  incon=28  crash=17
```

## CI regression check
CI runs the **full** suite on every PR as a **non-gating** job (`vmtests` in
`.github/workflows/ci.yml`): it never blocks a merge, but compares the run
against a committed baseline and surfaces any regression (a previously-passing
test that now FAILs/CRASHes) as a GitHub warning plus a report in the run
summary. The full output and normalized summary are uploaded as artifacts.

- Baseline: `.github/vmtests-baseline.txt` (aggregate counts + the set of
  FAIL/CRASH test ids), generated against the corpus revision pinned as
  `CORPUS_REV` in the workflow.
- When an evaluator fix turns failures into passes, the report lists them as
  improvements — refresh the baseline so it tracks the new floor:
  ```
  ./.lake/build/bin/vmtests <path>/legacytests/Constantinople/VMTests > raw.txt
  .github/scripts/vmtests_summary.sh raw.txt > .github/vmtests-baseline.txt
  ```
  If you regenerate against a newer corpus, bump `CORPUS_REV` in
  `.github/workflows/ci.yml` in the same commit — the baseline and the pinned
  corpus revision must always move together.

## How the harness works
- **Gas is ignored.** It injects `gasAvailable = 2^63` so `OutOfGas` never fires,
  and never compares the `gas` field. (The evaluator's gas model is uniform —
  `Gas.cost = 1` — so the field isn't meaningful to compare anyway.)
- **Tests using the `GAS` opcode (0x5a) are skipped** (2). With injected gas the
  pushed value is wrong, which would corrupt any stored/returned result.
- **Tests using unsupported opcodes are skipped** (6) via a bytecode pre-scan:
  CALL / CALLCODE / DELEGATECALL / STATICCALL / CREATE / CREATE2 / SELFDESTRUCT
  are not implemented by the evaluator.
- **Tests using keccak are skipped** (23) — KECCAK256 / EXTCODEHASH. `keccak256`
  is `opaque` and returns 0 at runtime, so any result depending on it (all of
  vmSha3Test, keccak-derived storage slots, code hashes) would not match.
- **Comparison** covers storage (over the union of pre/post slot keys),
  return-data, balance, and nonce. Logs are not compared (would need RLP encoding
  plus a real keccak).
- **Classification.** A test with a `post` expects success; absence of `post`
  expects an exceptional halt. Out-of-gas / out-of-fuel cases that the evaluator
  can't reproduce under infinite gas are reported as `incon` rather than
  pass/fail. A child that aborts (panic) or times out is reported as `crash`.

## Known evaluator limitations surfaced by the suite
These are gaps in the evaluator (not the harness), in rough order of impact.

### CRASH — previously known categories
- **`EXP` with a large exponent** (38: `exp*`, `loop-exp*`) — now **fixed**
  via modular fast-exponentiation (`UInt256.expFast`, `UInt256.lean`).
- **Huge memory offset/size** (17: `calldatacopy`/`codecopy`/`calldataload`/
  `log*` …`TooHigh`) — now **fixed** via proper memory-expansion gas:
  `chargeMem` / `chargeMem2` charge the Yellow-Paper quadratic cost for the
  touched range, so a `~2^256` offset hits `OutOfGas` long before the
  underlying `ByteArray` allocates. The zero-padding cases (calldata read
  past end) pass; `log*…TooHigh` lands as `incon` (real EVM expects a
  memory-expansion OOG halt the gas-ignoring harness can't reproduce).

### INCONCLUSIVE — mostly outside the evaluator's scope; ~11 are real gaps
- **~11 jump-into-PUSH-data accepted** (`*InsidePushWithJumpDest`,
  `DynamicJumpPathologicalTest{1,2,3}`): the EVM rejects a JUMP whose target is a
  `0x5b` byte sitting *inside* PUSH immediate data (`BadJumpDestination`). The
  evaluator's JUMP just re-decodes the target byte with no push-data-aware
  jumpdest analysis, so it accepts the jump and halts successfully. **Real
  soundness gap.**
- **~10 explicit out-of-gas / memory-expansion-gas** (`*MemExp`, `*OutOfGas*`,
  `loop_stacklimit_1021`): expect an OOG halt that can't be reproduced with
  infinite gas.
- **7 fuel-exhausted** (`*foreverOutOfGas`, `loop-*`, `ackermann33`): infinite or
  very long loops that the real EVM stops via gas.

### StackOverflow not raised executably
`stepF` enforces no 1024-deep stack limit; the cap exists only in the relation
`Step` (`Step.lean`). No VMTest in the suite currently turns this into a mismatch,
but it remains a divergence between `stepF` and `Step`.

## Evaluator behavior relied upon
- **End-of-code implicit STOP.** `Decode.decodeAt` returns `(STOP, none)` for
  `pc ≥ code.size`, matching the Yellow Paper's zero-padding of code
  (`0x00` = STOP). Both `stepF` and the relation `Step` (via `Step.stop`) treat
  running off the end of the code as a successful halt, so programs without an
  explicit trailing `STOP` (most push/dup/swap/jump tests) behave correctly.

## TODO / next steps
Ordered by impact on the suite. Each item lists the tests it would unlock.

### Evaluator fixes (turn crashes/fails into passes)
- [ ] **Push-data-aware jumpdest validation** — reject a JUMP/JUMPI whose target
      `0x5b` lies inside PUSH immediate data. *Unlocks ~11 inconclusive*
      (`*InsidePushWithJumpDest`, `DynamicJumpPathologicalTest{1,2,3}`).
- [ ] **Executable `StackOverflow`** — enforce the 1024-deep stack limit in
      `stepF` (currently only in the relation `Step`), removing a `stepF`/`Step`
      divergence.

### Keccak (lift the 23 keccak skips)
- [ ] Provide a concrete Keccak-256 (e.g. via `@[implemented_by]` on the `opaque`
      `keccak256`). *Unlocks all of vmSha3Test + keccak-derived storage/code-hash
      tests*, and enables **log-hash comparison** (currently logs aren't checked).

### Harness improvements
- [ ] **Gas-faithful mode** — once the evaluator has a real gas schedule, run with
      each test's actual gas budget and compare the `gas` field, converting the
      ~17 gas/fuel `incon` tests (`*MemExp`, `*OutOfGas*`, `*foreverOutOfGas`,
      `loop_stacklimit_1021`) into pass/fail. Currently impossible under uniform
      `Gas.cost = 1` + infinite gas.
- [ ] **Storage extra-write detection** — comparison only checks the union of
      pre/post slot keys, so a write to a slot named in neither is invisible.
      Track written keys to close this blind spot.

### Scope expansion
- [ ] Once calls/transaction processing land, target **GeneralStateTests** (the
      current/maintained suite) in addition to the frozen legacy VMTests.
