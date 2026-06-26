# VMTests harness

`VMRunner.lean` (executable `vmtests`) runs the legacy ethereum/tests **VMTests**
suite against the verified evaluator (`stepF` / `run`). VMTests is the suite that
matches this evaluator's scope: single-frame EVM execution, no inter-contract
calls, no transaction processing, uniform gas.

## How to run
```
# one-time: fetch the corpus and pin it to the CORPUS_REV that CI uses and that
# .github/vmtests-baseline.txt was generated against (the LegacyTests/ dir in
# ethereum/tests is a submodule that points at this repo)
REV=$(grep -m1 'CORPUS_REV:' .github/workflows/ci.yml | awk '{print $2}')
git clone https://github.com/ethereum/legacytests
git -C legacytests checkout "$REV"

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
pass=561 (gas-checked=330) fail=0 skip=29 (unsup=6 keccak=23 gas=0) incon=19 crash=0
```
- **gas-checked=330** — every test whose bytecode uses only opcodes with
  an exact gas cost in our schedule (every fixed-cost op + SLOAD + SSTORE
  via the pre-EIP-1283 schedule) runs with the test's real `exec.gas`
  budget, and the corpus's remaining-`gas` value is compared.
- **fail=0** — every gas-checked test that passes the storage/return-data
  comparison also matches the expected remaining-gas value.
- **Corpus fork note.** The legacy ethereum/tests `Constantinople` corpus
  was generated against pre-EIP-1283 rules (EIP-1283 was scheduled for
  Constantinople but reverted in Petersburg). Specifically the corpus
  uses Frontier-era SLOAD (50 gas), not Tangerine Whistle's 200. Our
  schedule matches this so the comparison is sound; bumping to a newer
  corpus would mean bumping SLOAD too (see `Gas.lean`).
- The remaining 231 non-gas-checked passes still run in gas-ignored mode
  (`gasAvailable = 2^63`) because their bytecode contains an opcode with
  a still-unmodelled dynamic cost (KECCAK256, *COPY, LOG, EXP, BALANCE /
  EXT*, CALL family).

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

### StackOverflow not enforced
`stepF` enforces no 1024-deep stack limit. The relation `Step` has a
`stackOverflow` constructor, but its *success* rules (e.g. `push0`, `pushN`)
carry no stack-length guard, so from a near-full stack both a successful push
and the `stackOverflow` successor are derivable — `Step` doesn't make the cap
exclusive either. No VMTest in the suite currently turns this into a mismatch,
but closing it needs guards on the `Step` success rules *and* a check in
`stepF`.

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
- [ ] **Enforce the 1024-deep stack limit** — add the cap to `stepF` **and**
      guard the `Step` success rules (`push0`/`pushN`/…), since neither side
      currently rules out an oversized push (see "StackOverflow not enforced"
      above).

### Keccak (lift the 23 keccak skips)
- [ ] Provide a concrete Keccak-256 (e.g. via `@[implemented_by]` on the `opaque`
      `keccak256`). *Unlocks all of vmSha3Test + keccak-derived storage/code-hash
      tests*, and enables **log-hash comparison** (currently logs aren't checked).

### Evaluator: model dynamic gas costs (lift more tests into gas-checked mode)
The current schedule has the right *base* cost for every opcode plus
memory expansion (Yellow-Paper quadratic) and the pre-EIP-1283 SSTORE
schedule (`Gas.sstoreCost` — `20000` for fresh non-zero set, `5000`
otherwise). The remaining unmodelled dynamic costs:

- [ ] **BALANCE / EXTCODESIZE / EXTCODECOPY / EXTCODEHASH** — EIP-2929
      cold/warm split (2600 / 100). Needs `accessedAccounts` in `Substate`.
- [ ] **KECCAK256** (`30 + 6 * ⌈size/32⌉`), **CALLDATACOPY / CODECOPY /
      RETURNDATACOPY / MCOPY** (`3 + 3 * ⌈size/32⌉`), **LOG** (`375 +
      375*topics + 8*size`), **EXP** (`10 + 50 * byteLen(exponent)`) — each
      is a small per-word/per-byte/per-topic add-on to the base cost. The
      `size`/`byteLen` operand is already on the stack; the additions are
      pure arithmetic.
- [ ] **SSTORE refunds** (clearing a non-zero slot adds `15000` to the
      refund counter). Not modelled. Affects post-Berlin corpora but the
      legacy Constantinople corpus reports `gas` without applying refunds,
      so this isn't currently a source of FAILs.
- [ ] **Modern SSTORE** (EIP-1283 / EIP-2200 / EIP-3529) for newer
      corpora — the `original` value is already threaded through
      `Substate.originalStorage`, so adding the modern schedule is a
      one-liner in `Gas.sstoreCost`. Keep the pre-EIP-1283 logic available
      as a fork-specific variant.

### Harness improvements
- [x] **Gas-faithful mode** for fixed-cost-only tests — done (gas-checked=32
      so far). Adding the dynamic costs above grows that bucket.
- [ ] **Storage extra-write detection** — comparison only checks the union of
      pre/post slot keys, so a write to a slot named in neither is invisible.
      Track written keys to close this blind spot.

### Scope expansion
- [ ] Once calls/transaction processing land, target **GeneralStateTests** (the
      current/maintained suite) in addition to the frozen legacy VMTests.
