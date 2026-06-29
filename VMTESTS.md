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
pass=601 fail=0 incon=8 crash=0
```

**StateTests `stCallCodes` (80 tests, run by `statetests`)**:
```
pass_full=328 pass_core=0 fail=0 incon=0 crash=0
```
The 328-test total comes from running *every* fork variant of every
file (Frontier / Homestead / EIP150 / EIP158 / Byzantium /
Constantinople / ConstantinopleFix), not just one. The
`State.finalizeTx` layer applies the SSTORE / SELFDESTRUCT refund
(capped at `gasUsed/2`), credits the unused gas back to the sender,
and pays the gas fee + per-fork block reward (5 / 3 / 2 ETH) to the
coinbase. The runner also handles top-level OOG by reconstructing
the rollback state (sender pays the full `gasLimit·gasPrice`, coinbase
receives that fee + block reward, everything else is `preState`) so
OOG tests can be compared against their expected `postState`. The
previously-INCON Constantinople-with-EIP-1283 deep-recursion tests
now pass: `AccountMap` and `Storage` are backed by `Std.HashMap` via
`@[implemented_by]` at runtime, replacing the O(N²) function-update
chain that pushed those tests past the 60s CI cap.
- `pass_full` = storage + nonce + code + balance match. Reaches the
  full count because the `State.finalizeTx` refund pipeline + fork-aware
  call surcharges line up with the corpus's accounting.
- **fail=0** — every with-`post` test that matches the storage / return-data
  comparison also matches the expected remaining-`gas` value. The schedule
  currently covers: every fixed-cost op, SLOAD / SSTORE (pre-EIP-1283),
  all five `*COPY` opcodes with per-word cost, KECCAK256 (base + per-word),
  LOG with per-byte cost, EXP with per-byte exponent cost, the CALL /
  SELFDESTRUCT / CREATE / CREATE2 dynamic pieces, and EIP-150's 63/64 gas
  forwarding.
- **Corpus fork note.** The legacy VMTests corpus uses Frontier-era
  gas across the board (SLOAD = 50, SELFDESTRUCT = 0, no `G_newaccount`
  surcharge, EXP per-byte = 10). The VMTests runner therefore selects
  `Fork.Frontier`. The Constantinople in the directory name is a corpus
  *revision* tag, not a fork tag.
- The 104 passes that don't compare gas are tests lacking a `post`
  block; they exit through the "expected an exception, got an exception"
  arm before any gas comparison happens. Every test still runs with its
  declared `exec.gas` budget.

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
- **Single execution mode.** Every test runs through `stepF` with its
  declared `exec.gas` budget. For tests with a `post` block the harness
  compares storage, return-data, balance, nonce, and the remaining `gas`
  value against the corpus — every opcode in our schedule
  (`Gas.baseCost` + the dynamic helpers: memory expansion, `sstoreCost`,
  `copyWordCost`, `keccakWordCost`, `logDataCost`, `expByteCost`,
  `Gas.create2HashCost`) has to produce the corpus's expected gas.
- **No opcodes are skipped.** All of CALL / CALLCODE / DELEGATECALL /
  STATICCALL / CREATE / CREATE2 / SELFDESTRUCT are implemented; the
  call family is also exercised by the separate `statetests` exe
  against the `stCall*` / `stCallCodes` BlockchainTests.
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
  EVM stops these via gas, but they run beyond the harness's
  `fuel = 2_000_000` cap inside our interpreter.

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

### Evaluator: model the remaining dynamic gas costs
Already modelled: memory expansion (Yellow-Paper quadratic),
`Gas.sstoreCost` (pre-EIP-1283 schedule for Frontier..Byzantium and
Petersburg; EIP-1283 net-metered for the original Constantinople;
EIP-2200 for Cancun), `Gas.copyWordCost` (5 copy ops × per-word 3),
`Gas.keccakWordCost` (KECCAK256 per-word 6), `Gas.logDataCost` (LOG
per-byte 8), `Gas.expByteCost` (EXP per-byteLen — 10 pre-Spurious-Dragon,
50 from EIP-158 onwards), `Gas.allButOneSixtyFourth` (no cap pre-EIP-150,
63/64 from EIP-150 onwards). Remaining gaps:

- [ ] **EIP-2929 cold/warm split** for `BALANCE` / `EXTCODESIZE` /
      `EXTCODECOPY` / `EXTCODEHASH` (cold 2600, warm 100). Needs an
      `accessedAccounts` set in `Substate`. Our `Cancun` fork currently
      pretends every access is warm; the pre-Cancun forks use the
      proper Frontier (20) / EIP-150 (400/700) values.
- [ ] **SSTORE refund counter is tracked but never applied** at end of
      transaction. Clearing a non-zero slot adds `15000` to
      `Substate.refundBalance`, but the runner doesn't subtract
      `min(refund, gas_used/2)` from the final `gas`. Wiring it in
      would let `pass_full` become reachable on tests with clearing
      SSTOREs.

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
