# Conformance harnesses

Two harnesses exercise the verified evaluator (`stepF` / `run`):

- **`VMRunner.lean`** (executable `vmtests`) — runs the legacy ethereum/tests
  **VMTests** suite, the suite that matches this evaluator's *single-frame*
  scope (no inter-contract calls, no transaction processing). This is the
  bulk of the conformance coverage; the rest of this document is about it.
- **`StateTestRunner.lean`** (executable `statetests`) — runs the
  BlockchainTests **`stCall*` / `stCallCodes`** suites, which exercise the
  CALL and CALLCODE opcodes' per-call-frame stack and the three
  `callReturn*` resume rules. Storage comparison covers the union of
  pre/post slot keys (so cleared-to-zero slots are caught). CI runs it as
  a separate, non-gating job against `.github/statetests-baseline.txt`.

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

## Current results

**VMTests (609 tests)**:
```
pass=601 (gas-checked=492) fail=0 skip=0 (unsup=0 keccak=0 gas=0) incon=8 crash=0
```

**StateTests `stCallCodes` (80 tests, run by `statetests`)**:
```
pass_full=0 pass_core=65 fail=6 incon=9 crash=0
```
- `pass_core` = storage + nonce + code match (the CALL-semantics signal);
  `pass_full` would additionally require exact balances — none reach this
  because exact balances need full gas-refund modelling (SSTORE refunds and
  cold/warm pricing). The remaining 6 FAILs are all `*_ABCB_RECURSIVE`
  tests where a four-way recursive CALL chain still ends with a storage
  slot at the deepest contract not getting written.
- **gas-checked=492** — every test whose bytecode uses only opcodes with
  an exact gas cost in our schedule runs with the test's real `exec.gas`
  budget, and the corpus's remaining-`gas` value is compared. The schedule
  currently covers: every fixed-cost op, SLOAD/SSTORE (pre-EIP-1283), all
  five `*COPY` opcodes with per-word cost, KECCAK256 (base + per-word),
  LOG with per-byte cost, and EXP with per-byte exponent cost.
- **fail=0** — every gas-checked test that passes the storage/return-data
  comparison also matches the expected remaining-gas value.
- **Corpus fork note.** The legacy ethereum/tests `Constantinople` corpus
  was generated against pre-EIP-1283 rules (EIP-1283 was scheduled for
  Constantinople but reverted in Petersburg). Specifically the corpus
  uses Frontier-era SLOAD (50 gas), not Tangerine Whistle's 200. Our
  `Constantinople` fork matches this so the comparison is sound; the
  `Cancun` fork uses the modern (warm-priced) schedule. See `Gas.lean`.
- The remaining 109 non-gas-checked passes still run in gas-ignored mode
  (`gasAvailable = 2^63`) because their bytecode contains an opcode whose
  cold/warm pricing is unmodelled (BALANCE / EXTCODESIZE / EXTCODEHASH /
  EXTCODECOPY), the unmodelled CALL surcharge, or SELFDESTRUCT (refund
  counter not yet wired into the gas-comparable arithmetic).

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
    full gas cost is captured in our schedule (`Gas.baseCost` + the dynamic
    helpers: memory expansion, `sstoreCost`, `copyWordCost`, `keccakWordCost`,
    `logDataCost`, `expByteCost`). The test runs with `exec.gas` as its real
    budget, and the remaining `gas` field is compared against the corpus.
  - *Gas-ignored* mode (the fallback): inject `gasAvailable = 2^63`, never
    compare `gas`. Used when the bytecode contains an opcode whose cold/warm
    cost we don't yet model — `BALANCE`, `EXTCODESIZE`, `EXTCODEHASH`,
    `EXTCODECOPY` — or `SELFDESTRUCT` (whose refund counter is unmodelled).
    (CREATE family short-circuits earlier via `skipReasonOf` — see the
    next bullet.)
- **`GAS` opcode** is fine under gas-checked mode (the pushed value matches
  the corpus's bookkeeping). Under hugeGas it would be corrupt — but the
  harness only falls back to hugeGas when *some other* opcode is non-gas-
  comparable, so the previous "gas-skip" bucket is currently empty.
- **Tests using unsupported opcodes are skipped** via a bytecode pre-scan
  (`VMRunner.skipReasonOf`): only CREATE / CREATE2 remain. The four
  call-family opcodes (CALL / CALLCODE / DELEGATECALL / STATICCALL) and
  SELFDESTRUCT are implemented in the evaluator. The call family is
  exercised by the separate `statetests` exe against the `stCall*` /
  `stCallCodes` BlockchainTests; in VMTests these opcodes still route
  through the gas-comparable filter because their dynamic surcharges
  aren't yet gas-comparable.
- **Keccak.** `EvmSemantics.keccak256` is wired (via `@[implemented_by]`)
  to a self-contained Keccak-256 implementation in
  `EvmSemantics.Crypto.Keccak256` (Keccak-f[1600] permutation + sponge,
  using the *original* Keccak padding `0x01` rather than NIST SHA3's
  `0x06`). The separate `keccak_test` exe verifies the output against
  well-known vectors (empty, `"abc"`, ERC-20 `transfer(address,uint256)`
  selector).
- **Comparison** covers storage (over the union of pre/post slot keys),
  return-data, balance, and nonce. Logs are not yet compared in the harness
  (would need RLP encoding to compute the corpus's `logsHash`).
- **Classification.** A test with a `post` expects success; absence of `post`
  expects an exceptional halt. Out-of-gas / out-of-fuel cases that the evaluator
  can't reproduce under infinite gas are reported as `incon` rather than
  pass/fail. A worker `Task` that throws is reported as `crash` (a hard panic
  aborts the whole run instead).

## Known evaluator limitations surfaced by the suite
These are gaps in the evaluator (not the harness), in rough order of impact.

### INCONCLUSIVE — outside the evaluator's scope
- **OOG / fuel-exhausted tests** (`*MemExp`, `*OutOfGas*`,
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
  (`0x00` = STOP). Both `stepF` and the relation `Step` (via `StepRunning.stop`,
  wrapped by `Step.running`) treat running off the end of the code as a
  successful halt, so programs without an explicit trailing `STOP` (most
  push/dup/swap/jump tests) behave correctly.

## TODO / next steps
Ordered by impact on the suite. Each item lists the tests it would unlock.

### Evaluator fixes (turn crashes/fails into passes)
- [ ] **Enforce the 1024-deep stack limit** — add the cap to `stepF` **and**
      guard the `Step` success rules (`push0`/`pushN`/…), since neither side
      currently rules out an oversized push (see "StackOverflow not enforced"
      above).

### Evaluator: model dynamic gas costs (lift more tests into gas-checked mode)
Already modelled: memory expansion (Yellow-Paper quadratic),
`Gas.sstoreCost` (pre-EIP-1283 for `Constantinople` / EIP-2200 for `Cancun`),
`Gas.copyWordCost` (5 copy ops × per-word 3), `Gas.keccakWordCost`
(KECCAK256 per-word 6), `Gas.logDataCost` (LOG per-byte 8),
`Gas.expByteCost` (EXP per-byteLen — 10 for Frontier-flavoured
`Constantinople`, 50 for `Cancun`). Remaining gaps:

- [ ] **BALANCE / EXTCODESIZE / EXTCODECOPY / EXTCODEHASH** — EIP-2929
      cold/warm split (2600 / 100). Needs `accessedAccounts` in `Substate`.
      These four are the only ops still dropping tests into gas-ignored mode.
- [ ] **SSTORE refunds** (clearing a non-zero slot adds `15000` to the
      refund counter). Not modelled. The legacy Constantinople corpus reports
      `gas` without applying refunds, so this isn't currently a source of
      FAILs; would matter for post-Berlin corpora.
- [ ] **Modern SSTORE** (EIP-1283 / EIP-2200 / EIP-3529) for newer
      corpora — the `original` value is already threaded through
      `Substate.originalStorage`, so adding the modern schedule is a
      one-liner in `Gas.sstoreCost`. The `Cancun` branch already does
      EIP-2200; cold/warm surcharge still missing.

### Harness improvements
- [ ] **Log-hash comparison** — the corpus stores `logsHash` (a keccak over
      RLP-encoded log entries). An RLP encoder would close the loop and
      let us validate emitted logs end-to-end.
- [ ] **Storage extra-write detection** — comparison only checks the union of
      pre/post slot keys, so a write to a slot named in neither is invisible.
      Track written keys to close this blind spot.

### Scope expansion
- [ ] Once calls/transaction processing land, target **GeneralStateTests** (the
      current/maintained suite) in addition to the frozen legacy VMTests.
