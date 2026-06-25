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
The full suite runs tests as in-process Lean `Task`s across `jobs` workers (`-j`
/ `VMTESTS_JOBS`, default 8) — there is no subprocess isolation (a deliberate
~7× speedup over the old subprocess-per-file design), so a hard evaluator panic
aborts the whole run; a `Task` that merely throws is recorded as one `crash`.
Use `--file <one>.json` to run a single test in its own process for isolation.

## Current results (609 tests)
```
pass=558 (gas-checked=32) fail=0 skip=31 (unsup=6 keccak=23 gas=2) incon=20 crash=0
```
- **gas-checked=32** — tests whose bytecode uses only opcodes with a fixed
  Yellow-Paper cost (no SSTORE/SLOAD/COPYs/EXP/LOG/CALL family) are run with
  the test's actual `exec.gas` budget, and the remaining `gas` field is
  compared against the corpus expectation.
- The remaining 526 passes still run in gas-ignored mode (`gasAvailable = 2^63`),
  because their bytecode contains at least one opcode whose real-EVM cost has
  a dynamic component (cold/warm, per-word, per-byte, value-dependent SSTORE).
  See `Gas.cost` in `EvmSemantics/EVM/Gas.lean` for the per-opcode status.

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
- **Two gas modes, picked per test by a bytecode pre-scan.**
  - *Gas-checked* mode: the test's bytecode contains only opcodes whose
    `Gas.cost` matches the Yellow-Paper fee schedule exactly (no cold/warm,
    no per-word/byte/topic). Then the test runs with `exec.gas` as its real
    budget, and the remaining `gas` field is compared against the corpus.
  - *Gas-ignored* mode (the fallback): inject `gasAvailable = 2^63`, never
    compare `gas`. Used whenever any opcode has a dynamic component our
    schedule doesn't model (SSTORE, SLOAD, BALANCE, EXT*, *COPY, EXP, LOG,
    CALL family, SELFDESTRUCT, CREATE family).
- **Tests using the `GAS` opcode (0x5a) are skipped** (2) only when the test
  cannot use gas-checked mode anyway. With the real gas budget the value
  `GAS` pushes is honest; under hugeGas it would be corrupt.
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
  pass/fail. A worker `Task` that throws is reported as `crash` (a hard panic
  aborts the whole run instead).

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

### INCONCLUSIVE (20) — mostly outside the evaluator's scope; ~11 are real gaps
- **~11 jump-into-PUSH-data accepted** (`*InsidePushWithJumpDest`,
  `DynamicJumpPathologicalTest{1,2,3}`): the EVM rejects a JUMP whose target is a
  `0x5b` byte sitting *inside* PUSH immediate data (`BadJumpDestination`). The
  evaluator's JUMP just re-decodes the target byte with no push-data-aware
  jumpdest analysis, so it accepts the jump and halts successfully. **Real
  soundness gap.**
- **Remaining OOG / fuel-exhausted tests** (`*MemExp`, `*OutOfGas*`,
  `*foreverOutOfGas`, `loop-*`, `ackermann33`, `loop_stacklimit_1021`): the
  EVM stops these via gas; we either don't model that opcode's cost yet
  (so the test isn't gas-checked) or the loop legitimately runs to the
  evaluator's `fuel = 2_000_000` cap.

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

### Evaluator: model dynamic gas costs (lift more tests into gas-checked mode)
The current schedule has the right *base* cost for every opcode but treats the
following as cost = 1 with a `TODO(dynamic)` comment in `Gas.lean`, because
their real cost has a state-dependent component we don't yet track:

- [ ] **SSTORE** (EIP-2200 + EIP-3529 — depends on `(original, current, new)`
      and cold/warm). Highest-impact: SSTORE is how almost every test stores
      its result, so a correct cost here would lift ~450 tests into
      gas-checked mode.
- [ ] **SLOAD / BALANCE / EXTCODESIZE / EXTCODECOPY / EXTCODEHASH** —
      EIP-2929 cold/warm split (2600 / 100). Needs an
      `accessedAccounts` / `accessedSlots` set in `Substate`.
- [ ] **KECCAK256** (`30 + 6 * ⌈size/32⌉`), **CALLDATACOPY / CODECOPY /
      RETURNDATACOPY / MCOPY** (`3 + 3 * ⌈size/32⌉`), **LOG** (`375 +
      375*topics + 8*size`), **EXP** (`10 + 50 * byteLen(exponent)`) — each
      is a small per-word/per-byte/per-topic add-on to the base cost. The
      `size`/`byteLen` operand is already on the stack; the additions are
      pure arithmetic.

### Harness improvements
- [x] **Gas-faithful mode** for fixed-cost-only tests — done (gas-checked=32
      so far). Adding the dynamic costs above grows that bucket.
- [ ] **Storage extra-write detection** — comparison only checks the union of
      pre/post slot keys, so a write to a slot named in neither is invisible.
      Track written keys to close this blind spot.

### Scope expansion
- [ ] Once calls/transaction processing land, target **GeneralStateTests** (the
      current/maintained suite) in addition to the frozen legacy VMTests.
