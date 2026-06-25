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
```
pass=490 (gas-checked=259) fail=71 skip=29 (unsup=6 keccak=23 gas=0) incon=19 crash=0
```
- **gas-checked=259** — tests whose bytecode uses only opcodes with a fixed
  or first-write-modelled gas cost (every fixed-cost op plus SLOAD at 200
  and SSTORE via `Gas.sstoreCost`'s EIP-1283 first-write rule). These run
  with the test's actual `exec.gas` budget and compare the remaining `gas`
  field against the corpus expectation.
- **fail=71** — tests where our gas accounting disagrees with the corpus
  by enough to either change a stored value (e.g. `GAS` opcode followed by
  `SSTORE`) or the final remaining-`gas` value. Causes: our SSTORE doesn't
  track `original` so second-write semantics differ from EIP-1283; refunds
  aren't modelled (the corpus's `gas` includes refunds for clearing slots);
  some op costs may still be off-by-fork (e.g. JUMPDEST vs G_jumpdest).
- **skip "gas" dropped 2 → 0**: tests that were previously skipped because
  they used the `GAS` opcode are now in gas-checked mode (their bytecode is
  fixed-cost-only, so the gas value `GAS` pushes is now honest).
- The remaining 231 non-gas-checked passes still run in gas-ignored mode
  because their bytecode contains an opcode with a still-unmodelled dynamic
  cost (KECCAK256, *COPY, LOG, EXP, BALANCE / EXT*, CALL family). See
  `Gas.cost` and `Gas.sstoreCost` in `EvmSemantics/EVM/Gas.lean`.

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
The current schedule has the right *base* cost for every opcode plus the
following dynamic costs already modelled: memory expansion (Yellow-Paper
quadratic) and SSTORE first-write (EIP-1283 approximation via
`Gas.sstoreCost`). The remaining gaps:

- [ ] **SSTORE original-tracking** (EIP-1283 fully / EIP-2200 / EIP-3529) —
      first-write is exact; second writes to the same slot over-charge
      (we use `current → new` not `original → current → new`). Needs a
      `originalStorage` snapshot at frame start. Should close the gap on
      most of the 71 current FAILs.
- [ ] **SSTORE refunds** — `gas` field in the corpus *includes* refunds
      (e.g. clearing a non-zero slot adds 15000). Not modelled. Contributes
      to current FAILs whenever a test clears a slot.
- [ ] **BALANCE / EXTCODESIZE / EXTCODECOPY / EXTCODEHASH** — EIP-2929
      cold/warm split (2600 / 100). Needs `accessedAccounts` in `Substate`.
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
