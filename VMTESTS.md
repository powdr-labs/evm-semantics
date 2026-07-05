# Conformance harnesses

## Current status (all suites clean)

As of the committed CI baselines (`.github/*-expected-failures.txt`, kept in
lockstep with real runner output), **every suite has zero correctness failures
and zero crashes**. The only non-passing entries are long-standing report-only
VMTests incons, the same two performance walltimeout incons in the
blockchain/static suites, and one out-of-scope trie-iterator incon:

| Suite | Runner / CI job | fail | incon | crash | notes |
| --- | --- | --- | --- | --- | --- |
| Legacy **VMTests** | `vmtests` | 0 | **7** | 0 | report-only; single-frame evaluator gaps (see "Known evaluator limitations") |
| Legacy **GeneralStateTests** (curated 47-dir) | `statetests` | 0 | 0 | 0 | **gating**; 19 875 per-fork cases |
| Modern **GeneralStateTests** (`ethereum/tests` @ Prague) | `modgst` | 0 | 0 | 0 | non-gating (PR #120 took it to fail=0) |
| **EEST Osaka** state_tests | `eest` | 0 | 0 | 0 | non-gating |
| **EEST static + historical** state_tests | `eeststatic` | 0 | **2** | 0 | maintained ports of the full legacy corpus (Osaka fills incl.); same two `*_walltimeout` |
| **EEST** transaction_tests | `eest` | 0 | 0 | 0 | non-gating; decode+validate |
| **TransactionTests** (`ethereum/tests`) | `txtests` | 0 | 0 | 0 | non-gating; decode+validate |
| **EEST blockchain_tests** | `blockchaintests` | 0 | **2** | 0 | both `*_walltimeout` — perf, not correctness (see below) |
| **EEST blockchain_tests** (Engine API) | `blockchaintests_engine` | 0 | **2** | 0 | same chains as `newPayload` envelopes; same two `*_walltimeout` |
| **RLPTests** (`ethereum/tests`) | `trierlp` | 0 | 0 | 0 | non-gating; RLP codec conformance (encode + canonical-decode rejection) |
| **TrieTests** (`ethereum/tests`) | `trierlp` | 0 | **1** | 0 | non-gating; MPT root conformance; the incon is `trietestnextprev` (iterator semantics, out of scope) |

- The **7 VMTests incons** are report-only single-frame evaluator gaps
  (OOG/fuel-exhausted tests the interpreter can't reproduce under its fuel cap,
  plus a handful of arithmetic/jumpdest edge cases). They are documented, not
  regressions.
- The **2 blockchain incons** are `test_run_until_out_of_gas_walltimeout` and
  `test_valid_walltimeout`: the evaluator's ~5K steps/sec throughput trips the
  per-test wall-clock cap under CI load. `test_valid` passes standalone; these
  are baselined as expected. No correctness issue.
- Modern GST / EEST can show *transient* walltimeout incons under heavy CPU
  load on non-CI hardware; those are never baselined.

## Harnesses

Eight harnesses exercise the verified evaluator (`stepF` / `run`) and its
data-structure layers:

- **`tests/VMRunner.lean`** (executable `vmtests`) — runs the legacy ethereum/tests
  **VMTests** suite, the *single-frame* corpus (no inter-contract calls,
  no transaction processing — each test runs one bytecode through `stepF`
  with its declared `exec.gas` budget and compares the resulting
  storage/return-data/balance/nonce/gas against the corpus). Small (609
  tests) and single-frame, so it can't exercise the CALL / tx layers;
  the bulk of the current conformance coverage is in the two runners
  below.
- **`tests/StateTestRunner.lean`** (executable `statetests`) — runs the
  legacy `ethereum/legacytests` BlockchainTests **GeneralStateTests** (a
  curated 47-dir subset of the ~50 `st*` directories — the ones the
  evaluator currently passes cleanly; see the list near the bottom of
  this doc). Decodes each transaction, hands it to
  `EvmSemantics.Tx.execute`, and compares the resulting `AccountMap`
  against the test's `postState`. Storage comparison covers the union
  of pre/post slot keys (so cleared-to-zero slots are caught). CI runs
  it as a **gating** job (`--strict` regression check) against
  `.github/statetests-expected-failures.txt` — any tier regression
  (pass → INCON/FAIL/CRASH, INCON → FAIL/CRASH, FAIL → CRASH) fails
  the build.
- **`tests/GeneralStateTestRunner.lean`** (executable `gstatetests`) — runs
  the **maintained** `ethereum/tests` GeneralStateTests in the modern
  `state_test` fixture format (shipped as `fixtures_general_state_tests.tgz`).
  This is the "lift" onto the current upstream suite; the other two consume
  the frozen `ethereum/legacytests` snapshot. See the dedicated section
  ["Modern GeneralStateTests"](#modern-generalstatetests-gstatetests) below.
  Non-gating; expected failures in `.github/gstatetests-expected-failures.txt`.
- **`tests/TransactionTestRunner.lean`** (executable `txtests`) — decodes and
  validates transactions from `ethereum/tests` **TransactionTests** (and, in
  the `eest` CI job, the modern EEST `transaction_tests`, including EIP-7702
  set-code txs). No execution: it checks RLP decoding + validity against the
  expected verdict. Baselines: `.github/txtests-expected-failures.txt` and
  `.github/eest-txtests-expected-failures.txt`. Non-gating.
- **`tests/BlockchainTestRunner.lean`** (executable `blockchaintests`) — runs
  the EEST **blockchain_tests**: full chain execution (block-by-block tx
  application + consensus/header checks) against the expected post-state and
  block-validity verdict. Exercises the Prague/Osaka EIP set (4844, 2537,
  2935, 7918/BPO, 7702, 6780, …). Baseline:
  `.github/blockchaintests-expected-failures.txt`.
- **`tests/BlockchainEngineTestRunner.lean`** (executable
  `blockchaintests_engine`) — runs the EEST **blockchain_tests_engine**: the
  same chains as `blockchaintests`, but each block arrives as an Engine-API
  `engineNewPayload` envelope (`params = [executionPayload, versionedHashes,
  parentBeaconBlockRoot, executionRequests?]`) instead of a raw block `rlp`.
  The `executionPayload` carries transactions as opaque EIP-2718 RLP byte
  strings, so the runner RLP-decodes each (legacy / 2930 / 1559 / 4844 / 7702),
  **recovers the sender** from its signature and — for set-code txs — recovers
  each authorization's **authority** from `keccak(0x05 ‖ rlp([chainId, address,
  nonce]))`, then executes through the same `Tx.execute` core. A payload flagged
  `validationError` is rejected (Engine-API `INVALID`), mirroring how the plain
  runner treats a block flagged `expectException`. Output format is identical to
  `blockchaintests`, so the CI shard reuses `blockchaintests_{run,summary,check}.sh`
  via the `BLOCKCHAINTESTS_BIN` override. Baseline:
  `.github/blockchaintests-engine-expected-failures.txt`.
- **`tests/RlpTestRunner.lean`** (executable `rlptests`) — runs the
  `ethereum/tests` **RLPTests**: each vector's `in` value (string / scalar
  incl. `#`-bignums / nested list) must *encode* to the expected canonical
  bytes, `invalidRLPTest` vectors must be *rejected* by the canonical decoder,
  and `RandomRLPTests` VALID vectors must decode. Direct conformance for the
  RLP codec that every tx decode, MPT node encoding and CREATE-address
  derivation sits on. Emits the txtests output format (the CI shard reuses
  `txtests_run.sh` via `TXTESTS_BIN` + `txtests_summary.sh`). Baseline:
  `.github/rlptests-expected-failures.txt`.
- **`tests/TrieTestRunner.lean`** (executable `trietests`) — runs the
  `ethereum/tests` **TrieTests**: fold each fixture's key/value operations
  (ordered lists with `null`/empty deletes, or any-order objects; keys/values
  are hex when `0x`-prefixed, else UTF-8; the `*secureTrie*` fixtures keccak
  each key) and compare `Mpt.rootHash` against the expected root. Direct
  conformance for the MPT behind the `passRoot` tier of every state/blockchain
  runner. `trietestnextprev` (iterator semantics) is reported `INCON`. Same
  txtests-format reuse. Baseline: `.github/trietests-expected-failures.txt`.

The `eest` CI job additionally runs the **maintained EEST (execution-spec-tests)
Osaka `state_tests`** through the `gstatetests` binary — modern-fork fixtures
(EIP-7825/7823/7883/7939/…) that the Prague-frozen `ethereum/tests` corpus
doesn't carry — against `.github/eest-osaka-expected-failures.txt`.

## How to run
The **legacy** VMTests + curated GeneralStateTests share one corpus repo
(`ethereum/legacytests`, ~2.7 GB full checkout). Instructions for the
**modern** GeneralStateTests corpus (`ethereum/tests`, ~9 MB tarball) are in
[Modern GeneralStateTests](#modern-generalstatetests-gstatetests) below.

```
# one-time: fetch the legacy corpus at the pinned CORPUS_REV. Full clone if you
# want everything; a sparse checkout of Constantinople/{VMTests,BlockchainTests}
# is enough for CI-shape runs. `CORPUS_REV` must move together with the
# .github/*-expected-failures.txt files it was generated against.
REV=$(grep -m1 'CORPUS_REV:' .github/workflows/ci.yml | awk '{print $2}')
git clone https://github.com/ethereum/legacytests
git -C legacytests checkout "$REV"

lake build vmtests statetests

# --- VMTests (single-frame conformance, ~600 tests, ~5s) -----------------
./.lake/build/bin/vmtests legacytests/Constantinople/VMTests
# single test:
./.lake/build/bin/vmtests --file legacytests/Constantinople/VMTests/…/add0.json

# --- StateTests (curated 47-dir subset, ~20k per-fork cases) --------------
# CI shape — bash wrapper with per-file subprocess isolation + wall cap:
.github/scripts/statetests_run.sh \
  legacytests/Constantinople/BlockchainTests/GeneralStateTests 45 4
# Native runner directly (single in-process scheduler, faster locally):
./.lake/build/bin/statetests -v -j $(nproc) --timeout 45000 \
  legacytests/Constantinople/BlockchainTests/GeneralStateTests
# One dir at a time is the fastest debug loop:
./.lake/build/bin/statetests -v \
  legacytests/Constantinople/BlockchainTests/GeneralStateTests/stRevertTest
```

`vmtests` runs its tests as in-process Lean `Task`s across `jobs` workers (`-j`
/ `VMTESTS_JOBS`, default 8) — there is no subprocess isolation (a deliberate
~7× speedup over the old subprocess-per-file design), so a hard evaluator panic
aborts the whole run; a `Task` that merely throws is recorded as one `crash`.
Use `--file <one>.json` to run a single test in its own process for isolation.

CI drives `statetests` through the bash wrapper `statetests_run.sh` (invokes
`statetests -v` once per JSON file via `xargs -P`, wrapped in `timeout(1)`);
this gives per-file process isolation so a panic on one file can't sink the
whole run at the cost of ~34ms process startup × N files. The native runner
above is faster locally because it uses the in-process `Task` scheduler with
a soft `--timeout MS` cap (a stuck test is marked `INCON`, the scheduler
moves on, and the abandoned task keeps running in the background).

## Current results

**VMTests (609 tests)**:
```
pass=602 fail=0 incon=7 crash=0
```

**StateTests (curated 47-dir subset, 19875 per-fork test cases across
Frontier · Homestead · Tangerine Whistle · Spurious Dragon · Byzantium ·
Constantinople · ConstantinopleFix)**:
```
pass(root=19543 full+=327 core+=5) fail=0 incon=0 crash=0
```
Every test in the curated subset matches the corpus at least at the
`pass_core` tier (storage / nonce / code identical to Geth) with no
`fail`/`crash`; 19543 of 19875 also match at the world-state MPT root
level (bit-identical postState).
Three tiers, strongest-first (`pass_root ⊃ pass_full ⊃ pass_core`):
- `pass_root` = world MPT `stateRoot` matches the corpus's
  `blockHeader.stateRoot` (every byte of the post-state matches what
  Geth would produce).
- `pass_full` = every field the test's `postState` enumerates matches
  (storage, nonce, code, *and* balance), but the MPT root differs.
- `pass_core` = storage / nonce / code match but balance is off.
- `fail` — every precompile the curated corpus exercises is
  implemented: ECRECOVER (0x01), SHA-256 (0x02), RIPEMD-160 (0x03),
  IDENTITY (0x04), MODEXP (0x05, Byzantium+), ECADD (0x06), ECMUL
  (0x07), ECPAIRING (0x08), BLAKE2F (0x09, Istanbul+). A future
  pass -> fail transition against the pinned expected-failures file is a
  regression. Individual precompile modules also ship with unit-test
  executables (`ecrecover_test`, `sha256_test`, `ripemd160_test`,
  `ecadd_ecmul_test`, `ecpairing_test`, `blake2f_test`) that pin
  them to known-good test vectors independently of the end-to-end
  statetests.

The MPT comparison lives in `EvmSemantics.Data.Mpt`:
`AccountMap.stateRoot σ fork` builds the world-state trie (RLP-encoded
`[nonce, balance, storageRoot, codeHash]` keyed by `keccak256(address)`),
applying EIP-161 empty-account pruning from Spurious Dragon onwards.
End-of-tx cleanup in `Tx.execute` calls `applySelfDestructDeletions` to
erase `SELFDESTRUCT`ed entries from the map outright (pre-EIP-161 forks
don't run the empty-account filter, so a present-but-empty entry would
otherwise stay in the trie).
- **Corpus fork note.** Each test file ships a `network` field per variant
  (`_Frontier`, `_Homestead`, `_EIP150`, `_EIP158`, `_Byzantium`,
  `_Constantinople`, `_ConstantinopleFix`); the runner derives the fork
  from that suffix and configures the gas schedule accordingly. Variants
  whose network isn't yet activated are skipped silently and don't count
  toward the tally.
- **The 47 dirs in CI** (alphabetical):
  `stArgsZeroOneBalance`, `stAttackTest`, `stBadOpcode`, `stBugs`,
  `stCallCodes`, `stCallCreateCallCodeTest`,
  `stCallDelegateCodesCallCodeHomestead`,
  `stCallDelegateCodesHomestead`, `stChangedEIP150`, `stCodeCopyTest`,
  `stCodeSizeLimit`, `stCreateTest`, `stDelegatecallTestHomestead`,
  `stEIP150Specific`, `stEIP150singleCodeGasPrices`, `stEIP158Specific`,
  `stExample`, `stExtCodeHash`, `stHomesteadSpecific`, `stInitCodeTest`,
  `stLogTests`, `stMemExpandingEIP150Calls`, `stMemoryStressTest`,
  `stMemoryTest`, `stNonZeroCallsTest`, `stPreCompiledContracts`,
  `stPreCompiledContracts2`, `stQuadraticComplexityTest`, `stRandom`,
  `stRandom2`, `stRecursiveCreate`, `stRefundTest`, `stReturnDataTest`,
  `stRevertTest`, `stSStoreTest`, `stShift`, `stSolidityTest`,
  `stSpecialTest`, `stStackTests`, `stStaticCall`,
  `stSystemOperationsTest`, `stTransactionTest`, `stTransitionTest`,
  `stZeroCallsRevert`, `stZeroCallsTest`, `stZeroKnowledge`,
  `stZeroKnowledge2`.
  Add a directory to the sparse-checkout in
  `.github/workflows/ci.yml` and regenerate the expected-failures file once
  the evaluator passes every variant in that directory (`fail = 0`;
  `pass_full` / `pass_core` cases are still passes at a weaker tier
  and are allowed).

## CI regression checks
CI runs every suite on each PR as a separate job with its own expected-failures
list, gating discipline, and script pair (`<suite>_summary.sh`,
`<suite>_check.sh`):

| CI job | suite / corpus | expected failures | gating? |
| --- | --- | --- | --- |
| `vmtests` | legacy VMTests — `ethereum/legacytests` @ `CORPUS_REV` | `.github/vmtests-expected-failures.txt` | report-only |
| `statetests` | legacy StateTests (curated subset), same corpus | `.github/statetests-expected-failures.txt` | **gating** (`--strict`) — any tier regression fails the build |
| `modgst` | modern GeneralStateTests — `ethereum/tests` @ `TESTS_REV` | `.github/gstatetests-expected-failures.txt` | report-only |
| `eest` | EEST Osaka `state_tests` (`gstatetests` binary) | `.github/eest-osaka-expected-failures.txt` | report-only |
| `eest` | EEST `transaction_tests` (`txtests` binary) | `.github/eest-txtests-expected-failures.txt` | report-only |
| `txtests` | `ethereum/tests` TransactionTests | `.github/txtests-expected-failures.txt` | report-only |
| `blockchaintests` | EEST `blockchain_tests` @ `EEST_REV` | `.github/blockchaintests-expected-failures.txt` | report-only |
| `blockchaintests_engine` | EEST `blockchain_tests_engine` @ `EEST_REV` | `.github/blockchaintests-engine-expected-failures.txt` | report-only |
| `eeststatic` | EEST `state_tests` static + historical forks (`gstatetests` binary) @ `EEST_REV` | `.github/eest-static-expected-failures.txt` | report-only |
| `trierlp` | `ethereum/tests` RLPTests (`rlptests` binary) | `.github/rlptests-expected-failures.txt` | report-only |
| `trierlp` | `ethereum/tests` TrieTests (`trietests` binary) | `.github/trietests-expected-failures.txt` | report-only |

The EEST corpora (Osaka `state_tests`, the static + historical `state_tests`,
`transaction_tests`, `blockchain_tests`,
`blockchain_tests_engine`) are extracted from the `fixtures_develop.tar.gz` release asset pinned by
`EEST_REV`; the legacy corpora are pinned by `CORPUS_REV` and the modern
`ethereum/tests` GeneralStateTests/TransactionTests/RLPTests/TrieTests by `TESTS_REV`. A baseline
file and the corpus revision it was generated against must always move together.
The `eeststatic` corpus is `fixtures/state_tests` minus `osaka/` (run by the
`eest` shard against its own baseline) and minus
`static/state_tests/{stTimeConsuming,VMTests}` (the same two exclusions the
`modgst` shard applies to the ethereum/tests copy of this corpus).

All files use the same format: sorted `<test_id>: <FAIL|INCON|CRASH>`
lines, one per non-passing test, with no aggregate counts and no header. The
check is tier-aware (severity `pass < INCON < FAIL < CRASH`), so
`pass → INCON`, `INCON → FAIL`, and `FAIL → CRASH` all surface as regressions;
`FAIL → pass` and `INCON → pass` surface as improvements. Aggregate counts
for the human-facing table are read from the runner's raw output at check
time, not from any committed file — so branches that fix (or add) different
failing tests never touch a shared "counter" line and merges stay
conflict-free. Full output and normalized summary are uploaded as artifacts
on every run.

When an evaluator fix turns failures into passes, the report lists them as
improvements — refresh the affected expected-failures file so it tracks the
new floor:
```
# VMTests
./.lake/build/bin/vmtests <path>/legacytests/Constantinople/VMTests > raw.txt
.github/scripts/vmtests_summary.sh raw.txt \
  > .github/vmtests-expected-failures.txt

# Legacy StateTests
./.lake/build/bin/statetests -j $(nproc) --timeout 45000 \
  <path>/legacytests/Constantinople/BlockchainTests/GeneralStateTests > raw.txt
.github/scripts/statetests_summary.sh raw.txt \
  > .github/statetests-expected-failures.txt

# Modern GeneralStateTests — via the subprocess-isolation wrapper (see below):
.github/scripts/gstatetests_run.sh <path>/gstcorpus/GeneralStateTests 45 4 > raw.txt
.github/scripts/gstatetests_summary.sh raw.txt \
  > .github/gstatetests-expected-failures.txt

# EEST Osaka state_tests (reuses the gstatetests runner + summary script):
.github/scripts/gstatetests_run.sh eest/fixtures/state_tests/osaka 45 8 > raw.txt
.github/scripts/gstatetests_summary.sh raw.txt \
  > .github/eest-osaka-expected-failures.txt

# TransactionTests (ethereum/tests) and EEST transaction_tests:
.github/scripts/txtests_run.sh <path>/TransactionTests 8 > raw.txt
.github/scripts/txtests_summary.sh raw.txt > .github/txtests-expected-failures.txt
.github/scripts/txtests_run.sh eest/fixtures/transaction_tests 8 > raw.txt
.github/scripts/txtests_summary.sh raw.txt > .github/eest-txtests-expected-failures.txt

# EEST blockchain_tests:
.github/scripts/blockchaintests_run.sh eest/fixtures/blockchain_tests 45 8 > raw.txt
.github/scripts/blockchaintests_summary.sh raw.txt \
  > .github/blockchaintests-expected-failures.txt

# EEST blockchain_tests_engine (reuses the blockchaintests scripts via the
# BLOCKCHAINTESTS_BIN override):
BLOCKCHAINTESTS_BIN=./.lake/build/bin/blockchaintests_engine \
  .github/scripts/blockchaintests_run.sh eest/fixtures/blockchain_tests_engine 45 8 > raw.txt
.github/scripts/blockchaintests_summary.sh raw.txt \
  > .github/blockchaintests-engine-expected-failures.txt

# EEST static + historical state_tests (reuses the gstatetests runner + summary
# script; drop osaka/ + static/state_tests/{stTimeConsuming,VMTests} first —
# see the CI job):
.github/scripts/gstatetests_run.sh eest/fixtures/state_tests 45 8 > raw.txt
.github/scripts/gstatetests_summary.sh raw.txt \
  > .github/eest-static-expected-failures.txt

# RLPTests / TrieTests (reuse the txtests run + summary scripts via the
# TXTESTS_BIN override):
TXTESTS_BIN=./.lake/build/bin/rlptests \
  .github/scripts/txtests_run.sh <path>/RLPTests 8 > raw.txt
.github/scripts/txtests_summary.sh raw.txt > .github/rlptests-expected-failures.txt
TXTESTS_BIN=./.lake/build/bin/trietests \
  .github/scripts/txtests_run.sh <path>/TrieTests 8 > raw.txt
.github/scripts/txtests_summary.sh raw.txt > .github/trietests-expected-failures.txt
```
If you regenerate against a newer corpus, bump `CORPUS_REV` or `TESTS_REV`
in `.github/workflows/ci.yml` in the same commit — the expected-failures
file and the pinned corpus revision must always move together.

## How the VMTests harness works
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
  against the curated GeneralStateTests subset.
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

### StackOverflow enforced on both sides
`stepF` enforces the 1024-deep stack limit before dispatch (an op that would
leave more than 1024 items halts with `StackOverflow` without spending its
base cost), and the `Step` success rules that grow the stack (`push0`,
`pushN`, `dup`, `dupN`, and the nullary reads) carry a matching
`h_cap : s.stack.length < 1024` premise, so a near-full stack no longer
admits both a successful push and the `stackOverflow` successor.

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

### Block runners: independent tx-level invalid-block detection
- [ ] **Implement typed-transaction block-validity checks in the block
      runners** — today many invalid-block fixtures are rejected because the
      fixture metadata (`expectException` / `validationError`) says so, with
      independent detection covering only header-consensus rules. Fee-cap
      ordering, cap-priced affordability, fork activation, and blob-hash
      constraints are not detected independently, so those fixtures pass by
      trusting the oracle rather than exercising validation logic (flagged by
      the 2026-07 audit). Prefer shared tx-validity code over per-runner
      copies, and report flagged-but-undetected blocks separately.

### Evaluator: model the remaining dynamic gas costs
Already modelled: memory expansion (Yellow-Paper quadratic), `Gas.sstoreCost`
(pre-EIP-1283, EIP-1283 Constantinople, EIP-2200 Istanbul, EIP-2929/EIP-3529
London+ price table), `Gas.sstoreRefund` (all four fork-eras, capped by
`gasUsed / refundDenom` in `Tx.execute`), `Gas.copyWordCost`,
`Gas.keccakWordCost`, `Gas.logDataCost`, `Gas.expByteCost` (Frontier 10 /
Spurious-Dragon+ 50), and the **EIP-2929 cold/warm split** for `BALANCE` /
`EXTCODESIZE` / `EXTCODECOPY` / `EXTCODEHASH` / `SLOAD` / `SSTORE` / CALL-family
(cold 2600, warm 100), wired through the `accessedAccounts` /
`accessedStorageKeys` sets in `Substate` and warm-seeded per tx in `Tx.execute`
(EIP-2929 implemented in PR #86; it was the largest `fail` cluster on the modern
GeneralStateTests corpus, now closed). No dynamic-gas gaps remain that produce
correctness failures on the current corpora.

### Harness improvements
- [ ] **Log-hash comparison** — the corpus stores `logsHash` (a keccak over
      RLP-encoded log entries). An RLP encoder would close the loop and
      let us validate emitted logs end-to-end.
- [ ] **Storage extra-write detection** — comparison only checks the union of
      pre/post slot keys, so a write to a slot named in neither is invisible.
      Track written keys to close this blind spot.

# Modern GeneralStateTests (`gstatetests`)

`tests/GeneralStateTestRunner.lean` lifts the harness onto the **maintained**
`ethereum/tests` repository. Where the other two harnesses read the frozen
`ethereum/legacytests` snapshot, this one reads the current upstream
GeneralStateTests in the modern `state_test` fixture format.

## The `state_test` fixture format
Upstream no longer checks GeneralStateTests in as directories; it ships them as
`fixtures_general_state_tests.tgz` at the repo root. Each JSON file holds one or
more test objects keyed like
`GeneralStateTests/stExample/add11.json::add11-fork_[Cancun-Prague]-d0g0v0`,
each with:
- `env` — flat block context (`currentCoinbase`, `currentGasLimit`,
  `currentNumber`, `currentTimestamp`, `currentBaseFee`, `currentRandom`,
  `currentExcessBlobGas`).
- `pre` — `{ addr: {balance, code, nonce, storage} }`.
- `transaction` — a *template*: `data`/`gasLimit`/`value` are **arrays**, plus
  scalar `gasPrice`, `to`, and **`sender`** (given directly — no ECDSA recovery
  needed, unlike the legacy BlockchainTests runner).
- `post` — `{ ForkName: [ { indexes:{data,gas,value}, state, hash, logs,
  txbytes } ] }`. Each entry selects one tx variant via `indexes` and carries
  an **expanded `state`** (compared per-account) and a state-root **`hash`**
  (compared via the world MPT root).

## How the runner works
- `parseForkExact` maps a bare fork name (`"Cancun"`) to a `Fork` (skip if
  unmodelled). `decodeEnv` builds the `BlockHeader` — note `prevRandao ←
  currentRandom` (post-Merge), **not** the legacy `difficulty` mapping.
- For each `post[fork][i]`: select the `(data,gas,value)` variant, build a
  `Tx.Transaction`, run `Tx.execute`, and classify with the same tiered outcome
  as the legacy statetests runner (`passCore ⊂ passFull ⊂ passRoot`): `core` =
  storage/nonce/code match, `full` also exact balances, `root` also the world
  MPT `stateRoot` equals the fixture's `hash`.
- Result ids are `<base>_<Fork>_d<d>g<g>v<v>` (one per entry).

## Scope and known gaps (minimal framework)
- **Legacy transactions only.** Typed transactions (EIP-1559/2930/4844) are
  reported `INCON` and skipped (`isTypedTx` keys on the presence of
  `maxFeePerGas` / a non-empty access list / blob hashes). ~99% of the corpus
  is legacy `gasPrice`.
- **Cancun/Prague only** in the corpus. **EIP-2929** cold/warm access pricing
  *is* now modelled (SLOAD/SSTORE storage-slot warmth; BALANCE/EXTCODESIZE/
  EXTCODEHASH/EXTCODECOPY and the CALL family account warmth; tx pre-warming of
  sender/recipient/precompiles/coinbase; CREATE/CALL-target warming), which
  lifted ~6976 tests from `passCore` to `passFull` (exact balances). The main
  remaining reason tests stay at `passCore` rather than `passRoot` is that
  `Tx.execute` performs **no EIP-1559 base-fee burn** — London+ burns
  `baseFee * gasUsed`, so the coinbase balance (and the MPT root) differ
  whenever `currentBaseFee > 0`. **EIP-3651 warm-coinbase** is modelled;
  SSTORE gas refunds (EIP-3529) are not, so refund-sensitive balances can still
  differ. Storage/nonce/code are unaffected, so those cases land at `passCore`.
- **Transaction validity is only partially enforced.** The YP §6.2 intrinsic-gas
  gate *is* enforced: a tx with `g₀ > gasLimit` is rejected with zero state
  change (fixes the `INTRINSIC_GAS_TOO_LOW` `invalidTr` cases, which now pass at
  `passRoot`). The remaining validity conditions (upfront-balance affordability,
  `gasLimit ≤ block gasLimit`, nonce match) are not yet gated in `Tx.execute`;
  fixtures that hinge on those may still diverge.
- **Logs** (`logsHash`) are not compared (no RLP-of-logs encoder), same as the
  legacy statetests runner.
- **Two files crash (contained).** `Cancun/…/MCOPY_memory_expansion_cost` and
  `stRandom2/randomStatetest649` hit the evaluator's *unbounded* huge-offset
  memory allocation (`readPadded`/`writeBytes`) → `INTERNAL PANIC: out of
  memory`. Because `gstatetests` runs files as in-process `Task`s, a panic would
  abort the whole run — so CI drives it through the per-file subprocess-isolation
  wrapper `gstatetests_run.sh`, which contains each panic as a `crash` for that
  one file and keeps going. Fixing the allocation itself is a separate
  memory-model change.

## How to run
```
# Fetch just the ~9 MB GeneralStateTests tarball at the pinned rev, extract the
# whole tree, and drop the two dirs CI excludes (see below):
REV=$(grep -m1 'TESTS_REV:' .github/workflows/ci.yml | awk '{print $2}')
mkdir ethtests && cd ethtests && git init -q
git remote add origin https://github.com/ethereum/tests
git sparse-checkout init
git sparse-checkout set --no-cone fixtures_general_state_tests.tgz
git fetch --depth 1 --filter=blob:none origin "$REV" && git checkout -q FETCH_HEAD
mkdir -p ../gstcorpus
tar xzf fixtures_general_state_tests.tgz -C ../gstcorpus GeneralStateTests
rm -rf ../gstcorpus/GeneralStateTests/stTimeConsuming \
       ../gstcorpus/GeneralStateTests/VMTests
cd ..

lake build gstatetests
# Whole corpus, isolated per file (recommended — survives the OOM crashers):
.github/scripts/gstatetests_run.sh gstcorpus/GeneralStateTests 45 4
# Or in-process for a single dir/file (faster, but a panic aborts the batch):
./.lake/build/bin/gstatetests -v gstcorpus/GeneralStateTests/stExample  # -j N, --timeout MS
./.lake/build/bin/gstatetests --file .../add11.json                     # single file
```

## CI regression check
CI runs `gstatetests` over **(almost) the whole corpus** on every PR as a
**non-gating** step, via the per-file subprocess-isolation wrapper
`gstatetests_run.sh` (45s per-file wall cap, parallelism 4), and compares
against `.github/gstatetests-expected-failures.txt` — a sorted list of
`<test_id>: <FAIL|INCON|CRASH>` lines, no aggregate counts. A test now at a
*worse* tier than expected surfaces as a warning (`INCON → FAIL`,
`FAIL → CRASH`, `pass → any`); a slow-runner wall-timeout that flips
`pass → INCON` also surfaces (but does not fail the build in this non-gating
job). Ids are directory-qualified (`<dir>_<file>_<Fork>_dNgNvN`) so same-named
tests in different dirs don't collide. Refresh the file when an evaluator fix
turns FAILs into passes:
```
.github/scripts/gstatetests_run.sh <corpus>/GeneralStateTests 45 4 > raw.txt
.github/scripts/gstatetests_summary.sh raw.txt \
  > .github/gstatetests-expected-failures.txt
```
Only two dirs are excluded: `stTimeConsuming` (deliberately pathological
ackermann/loop tests) and the non-GeneralStateTests internal `VMTests` dir. Bump
`TESTS_REV` and the expected-failures file in the same commit — never one
alone.

Current results (whole corpus minus the two excluded dirs, Cancun + Prague;
~80s wall at `-P4`):
```
pass(root=46 full+=2446 core+=19727) fail=1709 incon=2180 crash=2 (total 26110)
```
The large `fail` count is expected and traces to the documented gaps, not to the
runner: the top failing dirs are `precompsEIP2929Cancun`, `modexpTests`,
`ecpairing`, `eip2929`, `CreateAddressWarmAfterFail` — i.e. EIP-2929 cold/warm
and precompile-gas cases where wrong gas changes the halt and hence the observed
storage/code. `incon` is overwhelmingly the skipped typed transactions.
