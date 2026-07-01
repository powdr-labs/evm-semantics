# Conformance harnesses

Three harnesses exercise the verified evaluator (`stepF` / `run`):

- **`tests/VMRunner.lean`** (executable `vmtests`) — runs the legacy ethereum/tests
  **VMTests** suite, the *single-frame* corpus (no inter-contract calls,
  no transaction processing — each test runs one bytecode through `stepF`
  with its declared `exec.gas` budget and compares the resulting
  storage/return-data/balance/nonce/gas against the corpus). It pre-dates
  the evaluator's inter-contract and transaction-level support, so it
  exercises a strict subset of what we now model. This is the bulk of
  the conformance coverage; the rest of this document is about it.
- **`tests/StateTestRunner.lean`** (executable `statetests`) — runs the
  BlockchainTests **GeneralStateTests** (a curated 47-dir subset of the
  ~50 `st*` directories — the ones the evaluator currently passes
  cleanly; see the list near the bottom of this doc). Decodes each
  transaction, hands it to `EvmSemantics.Tx.execute`, and compares the
  resulting `AccountMap` against the test's `postState`. Storage
  comparison covers the union of pre/post slot keys (so cleared-to-zero
  slots are caught). CI runs it as a separate, non-gating job against
  `.github/statetests-baseline.txt`.
- **`tests/GeneralStateTestRunner.lean`** (executable `gstatetests`) — runs
  the **maintained** `ethereum/tests` GeneralStateTests in the modern
  `state_test` fixture format (shipped as `fixtures_general_state_tests.tgz`).
  This is the "lift" onto the current upstream suite; the other two consume
  the frozen `ethereum/legacytests` snapshot. See the dedicated section
  ["Modern GeneralStateTests"](#modern-generalstatetests-gstatetests) below.
  Non-gating; baseline in `.github/gstatetests-baseline.txt`.

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
  pass -> fail transition against the pinned baseline is a
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
  `.github/workflows/ci.yml` and regenerate the baseline once the
  evaluator passes every variant in that directory (`fail = 0`;
  `pass_full` / `pass_core` cases are still passes at a weaker tier
  and are allowed).

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
`Gas.sstoreCost` (pre-EIP-1283 for `Constantinople` / EIP-2200 for `Cancun`),
`Gas.copyWordCost` (5 copy ops × per-word 3), `Gas.keccakWordCost`
(KECCAK256 per-word 6), `Gas.logDataCost` (LOG per-byte 8),
`Gas.expByteCost` (EXP per-byteLen — 10 for Frontier-flavoured
`Constantinople`, 50 for `Cancun`). Remaining gaps:

- [ ] **EIP-2929 cold/warm split** for `BALANCE` / `EXTCODESIZE` /
      `EXTCODECOPY` / `EXTCODEHASH` (cold 2600, warm 100). Needs an
      `accessedAccounts` set in `Substate`. Our `Cancun` fork currently
      pretends every access is warm; `Constantinople` uses the
      pre-EIP-2929 flat 400 / 700.
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
- [x] Target the maintained `ethereum/tests` **GeneralStateTests** in addition
      to the frozen legacy VMTests — done; see below (`gstatetests`).

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
- **Cancun/Prague only** in the corpus. Two structural reasons keep most tests
  at the **`passCore`** tier rather than `passFull`/`passRoot`:
  1. `Tx.execute` performs **no EIP-1559 base-fee burn** — London+ burns
     `baseFee * gasUsed`, so we overpay the coinbase and the sender/coinbase
     balances (and the MPT root) differ whenever `currentBaseFee > 0`.
  2. **EIP-2929 cold/warm** access costs and **EIP-3651 warm-coinbase** are not
     modelled (a pre-existing gas gap).
  Storage/nonce/code are unaffected by either, so `passCore` is the honest,
  expected tier. A passCore-heavy baseline is **not** a regression.
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
`gstatetests_run.sh` (45s per-file wall cap, parallelism 4), and compares against
`.github/gstatetests-baseline.txt` (keyed on the FAIL id set, so a pass → FAIL
surfaces as a warning; a wall-timeout flip to `incon`, or a new `crash`, does
not). Ids are directory-qualified (`<dir>_<file>_<Fork>_dNgNvN`) so same-named
tests in different dirs don't collide. Refresh the baseline when an evaluator fix
turns FAILs into passes:
```
.github/scripts/gstatetests_run.sh <corpus>/GeneralStateTests 45 4 > raw.txt
.github/scripts/gstatetests_summary.sh raw.txt > .github/gstatetests-baseline.txt
```
Only two dirs are excluded: `stTimeConsuming` (deliberately pathological
ackermann/loop tests) and the non-GeneralStateTests internal `VMTests` dir. Bump
`TESTS_REV` and the baseline in the same commit — never one alone.

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
