# Conformance harnesses

Two harnesses exercise the verified evaluator (`stepF` / `run`):

- **`tests/VMRunner.lean`** (executable `vmtests`) — runs the legacy ethereum/tests
  **VMTests** suite, the *single-frame* corpus (no inter-contract calls,
  no transaction processing — each test runs one bytecode through `stepF`
  with its declared `exec.gas` budget and compares the resulting
  storage/return-data/balance/nonce/gas against the corpus). It pre-dates
  the evaluator's inter-contract and transaction-level support, so it
  exercises a strict subset of what we now model. This is the bulk of
  the conformance coverage; the rest of this document is about it.
- **`tests/StateTestRunner.lean`** (executable `statetests`) — runs the
  BlockchainTests **GeneralStateTests** (a curated 32-dir subset of the
  ~50 `st*` directories — the ones the evaluator currently passes
  cleanly; see the list near the bottom of this doc). Decodes each
  transaction, hands it to `EvmSemantics.Tx.execute`, and compares the
  resulting `AccountMap` against the test's `postState`. Storage
  comparison covers the union of pre/post slot keys (so cleared-to-zero
  slots are caught). CI runs it as a separate, non-gating job against
  `.github/statetests-baseline.txt`.

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

**StateTests (curated 32-dir subset, 9664 per-fork test cases across
Frontier · Homestead · Tangerine Whistle · Spurious Dragon · Byzantium ·
Constantinople · ConstantinopleFix)**:
```
pass(root=8181 full+=2 core+=119) fail=1362 incon=0 crash=0
```
Three tiers, strongest-first (`pass_root ⊃ pass_full ⊃ pass_core`):
- `pass_root` = world MPT `stateRoot` matches the corpus's
  `blockHeader.stateRoot` (every byte of the post-state matches what
  Geth would produce). 8181 of 9664.
- `pass_full` = every field the test's `postState` enumerates matches
  (storage, nonce, code, *and* balance), but the MPT root differs —
  usually because some account our run touched isn't in the test's
  enumerated `postState`, or some slot we wrote to isn't in the
  enumerated storage. 39 of 9664. Includes the two
  `stAttackTest/ContractCreationSpam_d0g0v0` variants (`_Frontier`
  and `_Homestead`) that spam-create ~8500 accounts, where the
  divergence at scale hides a subtle CREATE-derivation or gas-cost
  off-by-one that only shows up after thousands of nested CREATEs.
- `pass_core` = storage / nonce / code match but balance is off. 119
  of 9664. Dominated by (i) contracts that invoke unimplemented
  precompiles (`0x05` MODEXP) — we treat the (empty) bytecode at
  those addresses as STOP rather than applying the precompile's
  gas-cost OOG, so the value transfer that the YP would have rolled
  back gets committed; (ii) repeated `SELFDESTRUCT` of the same
  account, where our `selfDestructSet` doesn't yet enforce "refund
  once per account" (the underlying `AddressSet` is a `Prop`
  predicate without decidable membership).
- `fail = 1362` — 1,356 `modexp*` variants in `stPreCompiledContracts`
  / `stPreCompiledContracts2` that exercise MODEXP (`sec80` included)
  directly, plus 6 `identity_to_{bigger,smaller}_d0g0v0` cases with
  an unrelated create-transaction nonce quirk. The MODEXP entries
  have expected outputs that depend on the corresponding precompile
  actually running; treating the address as empty-code STOP makes
  the post-state visibly mismatch (nonces, return-write regions).
  The set is pinned in the baseline so a *new* pass -> fail
  transition is a regression. ECRECOVER (0x01), SHA-256 (0x02),
  RIPEMD-160 (0x03), and IDENTITY (0x04) tests in these dirs all
  pass.
- **alt_bn128 precompiles (EIP-196 / EIP-197)** — `stZeroKnowledge`
  and `stZeroKnowledge2` in the sparse checkout add ~4300 more
  tests. ECADD (0x06), ECMUL (0x07), and ECPAIRING (0x08) all have
  passing unit-test suites against known-good vectors (geth's
  `chfast_add` / `chfast_mul` for the first two; the EIP-197
  `pairingTest_d0` vector for the third; see
  `tests/EcaddEcmulTest.lean` and `tests/EcpairingTest.lean`).
  Of the ~4300 additional statetests: ~1200 pass_root, ~4400 fail.
  Most of the fails are not a precompile-correctness issue — the
  runner uses a hardcoded canonical sender
  `0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b` but most
  `stZeroKnowledge2` fixtures are signed by a different key
  (recovering to `0x82a978b3f5962a5b0957d9ee9eef472ee55b42f1`), so
  the tx-level nonce/balance assertions never match. Deriving the
  sender via `ECRECOVER` from the tx's `(v, r, s)` is a separate
  runner change tracked as future work.

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
- **The 32 dirs in CI** (alphabetical):
  `stArgsZeroOneBalance`, `stAttackTest`, `stBadOpcode`, `stBugs`,
  `stCallCodes`, `stCallCreateCallCodeTest`,
  `stCallDelegateCodesCallCodeHomestead`,
  `stCallDelegateCodesHomestead`, `stChangedEIP150`, `stCodeCopyTest`,
  `stCodeSizeLimit`, `stDelegatecallTestHomestead`, `stEIP150Specific`,
  `stEIP150singleCodeGasPrices`, `stExample`, `stHomesteadSpecific`,
  `stInitCodeTest`, `stLogTests`, `stMemExpandingEIP150Calls`,
  `stPreCompiledContracts`, `stPreCompiledContracts2`,
  `stMemoryStressTest`, `stMemoryTest`, `stRandom`, `stRecursiveCreate`,
  `stRefundTest`, `stShift`, `stSpecialTest`, `stStackTests`,
  `stTransactionTest`, `stTransitionTest`, `stZeroCallsRevert`.
  Add a directory to the sparse-checkout in
  `.github/workflows/ci.yml` and regenerate the baseline once the
  evaluator passes every variant in that directory.

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
- [ ] Once calls/transaction processing land, target **GeneralStateTests** (the
      current/maintained suite) in addition to the frozen legacy VMTests.
