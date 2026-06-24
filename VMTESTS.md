# Running ethereum/tests against the evaluator — Phase 1

Harness: `VMRunner.lean` (exe `vmtests`). Drives the real verified `stepF`/`run`
over the legacy **VMTests** suite (the only suite matching a calls-free,
no-transaction, uniform-gas evaluator).

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
Each test runs in its own child process (`--file` mode) so an evaluator panic or
hang only loses that one test instead of aborting the whole run.

## Result (609 tests)
```
pass=491  fail=4  skip=31 (unsup=6 keccak=23 gas=2)  incon=28  crash=55
```
Of the 522 tests that aren't skipped/crashed, **491 pass (94%)**.

## Design decisions (per the agreed plan)
- **Ignore gas**: inject `gasAvailable = 2^63` so `OutOfGas` never fires; never
  compare the `gas` field. Gas model is uniform (`Gas.cost = 1`) anyway.
- **Skip GAS opcode (0x5a)** tests: the injected gas would poison the pushed
  value (→ wrong stored/returned data). 2 tests.
- **Skip unsupported opcodes** (CALL/CALLCODE/DELEGATECALL/STATICCALL/CREATE/
  CREATE2/SELFDESTRUCT) via a bytecode pre-scan. 6 tests.
- **Skip keccak** (KECCAK256 / EXTCODEHASH): `keccak256` is `opaque` and returns
  0 at runtime. 23 tests (all of vmSha3Test + a few others). Lift in phase 2.
- **Compare** storage (over pre∪post slot keys), return-data, balance, nonce.
  Logs not compared (need RLP + real keccak).
- **Implicit STOP**: previously `stepF` returned `InvalidInstruction` when `pc`
  ran past the end of the code, but the Yellow Paper halts there with a STOP
  (code is zero-padded; `0x00` = STOP). This is now **fixed in the evaluator**:
  `Decode.decodeAt` returns `(STOP, none)` for `pc ≥ code.size`, so both `stepF`
  and the relation `Step` (via `Step.stop`) agree. Without this, ~150
  otherwise-correct tests (most push/dup/swap/jump) failed.

## Findings — genuine evaluator issues surfaced

### FAIL (4) — signed-arithmetic semantics (`vmArithmeticTest`)
`SMOD`/`SDIV` disagree with the EVM by the sign convention of the result.
EVM truncates toward zero (result takes the dividend's sign); Lean's `Int` `%`/`/`
used in `UInt256.ofSignedInt (a.toSignedNat % b.toSignedNat)` (StepF.lean:61-64)
uses a different (Euclidean/T-division) convention.
- `smod0`, `smod2`: got `1`, expected `-2 mod 2^256`.
- `smod8_byZero`, `sdiv_dejavu`: off-by-sign / off-by-one.

### CRASH (55) — unbounded `Nat` allocation (process aborts)
- **`EXP` with a large exponent (38: exp* + loop-exp*)**: `UInt256.exp` computes
  `a.toNat ^ b.toNat` *fully* before `% 2^256` (UInt256.lean:45) → GMP
  "Nat.pow exponent is too big". Needs fast modular exponentiation.
- **Huge memory offset/size (17: calldatacopy/codecopy/calldataload/log*…TooHigh)**:
  `readPadded`/`writeBytes` allocate `size`/`offset+size` bytes with no bound, so
  a `2^256`-ish size OOMs/aborts. Needs a size guard (real EVM caps via gas).

### INCONCLUSIVE (28) — mostly not the evaluator's fault, but 11 are real
- **~11 jump-into-PUSH-data accepted** (`*InsidePushWithJumpDest`,
  `DynamicJumpPathologicalTest{1,2,3}`): real EVM rejects a JUMP whose target is a
  `0x5b` byte sitting *inside* PUSH immediate data (`BadJumpDestination`). `stepF`
  JUMP just re-decodes the target byte (StepF.lean:300) with no push-data-aware
  jumpdest analysis, so it accepts and halts Success. **Real soundness gap.**
- **~10 explicit out-of-gas / memory-expansion-gas** (`*MemExp`, `*OutOfGas*`,
  `loop_stacklimit_1021`): expect an OOG halt we can't reproduce with infinite gas.
- **7 fuel-exhausted** (`*foreverOutOfGas`, `loop-*`, `ackermann33`): infinite /
  very long loops the real EVM stops via gas.

### Fixed in this PR
- **End-of-code implicit STOP** (`Decode.decodeAt`): see above.

### Also note (not a failure here, but a known stepF gap)
`stepF` never raises `StackOverflow` (no 1024-depth cap; only the relation has it,
Step.lean:887). No VMTest in this run exercised it into a mismatch, but it remains
a divergence.

## Phase 2 (optional, not done)
Supply a concrete Keccak-256 via `@[implemented_by]` to unlock the 23 keccak
skips (esp. all of vmSha3Test) + log-hash comparison.
