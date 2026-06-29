# EvmSemantics

A **relational small-step / big-step semantics of the Ethereum Virtual
Machine** in Lean 4, mirroring the structure of
[NethermindEth/EVMYulLean](https://github.com/NethermindEth/EVMYulLean)
but expressed as `Prop`-valued inductive relations rather than
executable functions, so that reasoning is more direct.

> **Provenance.** This package was mostly AI-generated (Claude) in
> collaboration with a human reviewer. Treat the design and proofs as a
> draft: the structure has been thought through, the build is green, the
> demo runs, and a substantial portion of the soundness lemmas are
> closed — but expect rough edges, especially in the deferred proof
> obligations. Not for production use.

## Status

What's in: foundation types, `Operation` ADT (incl. EIP-8024
`DUPN`/`SWAPN`/`EXCHANGE`) and bytecode decoder, halted-state flag +
`ExecutionResult`, small-step relation `Step` (success + exception
rules), big-step relation `Eval` + reflexive-transitive closure
`Steps`, executable shadow `stepF` with soundness theorem
`stepF s = .ok s' → Step s s'` (no `sorry`), real Keccak-256
(`Crypto/Keccak256.lean`, wired via `@[implemented_by]`), and the four
call-family opcodes `CALL` / `CALLCODE` / `DELEGATECALL` / `STATICCALL`
with a per-call-frame stack, EIP-150 forwarding, value stipend, and
static-mode guard on `CALL`.

**Demo (`Main.lean`)** runs `PUSH1 5 ; PUSH1 3 ; ADD ; STOP` through the
executable shadow, producing stack `[8]` and `halt = Success`. Confirms
the relation/executable pair is at least internally consistent on a
trivial program.

## Scope (locked-in decisions)

- **Multi-frame EVM:** all arithmetic, comparison/bitwise, KECCAK256,
  environmental reads, block-context reads, memory, storage (incl.
  transient), stack manipulation (POP, PUSH0–PUSH32, DUP1–16, SWAP1–16),
  control flow (JUMP, JUMPI, JUMPDEST, PC, GAS), halts (STOP, RETURN,
  REVERT, INVALID), logging (LOG0–LOG4), EIP-8024 (DUPN, SWAPN, EXCHANGE),
  and the four call-family opcodes **`CALL` / `CALLCODE` /
  `DELEGATECALL` / `STATICCALL`** with EIP-150 63/64 forwarding, value
  stipend (CALL/CALLCODE only), depth/balance pre-check, `returnData`
  clearing on pre-execution failure, and a list-backed call-frame stack
  with three resume rules (`callReturnSuccess` / `callReturnRevert` /
  `callReturnException`). The four kinds share a `CallKind`-parameterised
  callee-env / `enterCall` skeleton; per-kind axes (`address` /
  `caller` / `weiValue` / `permitStateMutation` / value transfer) live in
  `CallKind.calleeXxx` projections.
- **`SELFDESTRUCT`** is implemented: base `G_selfdestruct = 5000` +
  `Gas.selfDestructSurcharge` (25000 if the beneficiary is empty and
  self has non-zero balance), credit-then-debit transfer so a
  self-beneficiary correctly *burns* the balance, marks self in
  `Substate.selfDestructSet`, and adds the 24000 refund on Constantinople.
- **`CREATE` / `CREATE2`** are implemented: base `G_create = 32000`,
  memory expansion, depth + balance pre-check, EIP-150 63/64 forwarding,
  init-code execution in a new frame (`Frame.createAddr := some
  newAddr`), and code deposit at `G_codedeposit = 200` per deployed byte
  via the new `resumeCreateSuccess` rule (insufficient-deposit-gas →
  exception-rollback). CREATE derives `newAddr` from
  `keccak256(rlp([sender, sender.nonce]))[12:]` via a minimal RLP
  encoder (`EvmSemantics.Rlp`, items: `[20-byte address, uint nonce]`,
  short-list path only). CREATE2 derives `newAddr` from
  `keccak256(0xff || sender || salt || keccak256(initcode))[12:]` and
  additionally pays `Gas.create2HashCost = 6·⌈|initcode|/32⌉`.
  Address-collision detection is enforced via a `Bool`-valued
  `Account.isContract` helper (stricter than `isEmpty` — excludes
  balance), with a dedicated `Step.createCollision` /
  `Step.create2Collision` constructor pair (caller's nonce bumped,
  push 0, no transfer, no frame).
- **Not yet implemented:** transaction processing (`Υ`), block validation,
  precompiled contracts, full RLP (only `[address, nonce]` is encodable).
- **Gas:** parameterised by EVM hard fork (`EvmSemantics.Fork`,
  threaded through `ExecutionEnv.fork`). `Gas.baseCost fork op` returns
  the static Yellow-Paper fee per fork (`Constantinople` matches the
  legacy ethereum/tests corpus — Frontier-era SLOAD = 50, EXP per-byte = 10;
  `Cancun` uses the modern warm-priced reads and Spurious-Dragon EXP).
  All major **dynamic costs** are also modelled: memory expansion
  (`chargeMem` / `chargeMem2`, Yellow-Paper quadratic), `Gas.sstoreCost`
  (pre-EIP-1283 for Constantinople / EIP-2200 for Cancun, with the
  EIP-2200 stipend sentry via `Gas.sstoreSentry`), `Gas.copyWordCost`,
  `Gas.keccakWordCost`, `Gas.logDataCost`, `Gas.expByteCost`. The relational
  `StepRunning.outOfGas` is generalised to accept a `cost : Nat` witness with
  `Gas.baseCost ≤ cost`, so dynamic-cost OOG (memory expansion, sstoreCost,
  per-word/byte/topic charges) is expressible. The only remaining unmodelled
  costs are the EIP-2929 cold/warm split for `BALANCE` / `EXTCODESIZE` /
  `EXTCODECOPY` / `EXTCODEHASH` (stubbed pending an `accessedAccounts` set
  in `Substate`) and the dynamic CALL-family surcharge interactions
  across nested frames (kept non-gas-comparable pending an audit).
  `SELFDESTRUCT`, `CREATE`, and `CREATE2` are now gas-comparable:
  SELFDESTRUCT uses Frontier rules on the `Constantinople` fork (cost 0,
  no `G_newaccount` surcharge — same convention as our Frontier-rate
  SLOAD=50 and EXP=10), modern values on `Cancun`. The call family pays base fee + memory expansion + value
  surcharge via `Gas.callSurcharge` (CALL also pays the new-account
  portion when applicable; DELEGATECALL / STATICCALL pay zero
  surcharge) + 63/64 forwarding via `Gas.allButOneSixtyFourth`.
  Schedule changes need to stay in lockstep across `Step`, `stepF`, the
  soundness proof, and `VMRunner.gasComparableOpcode`.
- **World state:** modelled as plain functions, not hash maps —
  `Storage = UInt256 → UInt256`, `AccountMap = AccountAddress → Account`,
  address sets as `α → Prop`. This trades enumerability for clean
  algebraic reasoning (`Function.update`, extensionality, `simp`).
- **Address space:** `AccountAddress = Fin (2^160)` — the real 20-byte
  EVM address space.

## Layout

```
EvmSemantics.lean               -- root re-exports
Main.lean                       -- demo executable
EvmSemantics/
  Data/
    UInt256.lean                -- 256-bit words, modular arithmetic
                                --   (the operand stack is plain `List UInt256`)
  State/
    Account.lean                -- AccountAddress, Storage, Account, AccountMap
    BlockHeader.lean            -- block-context fields read by BLOCK ops
    ExecutionEnv.lean           -- per-frame execution environment I
    Substate.lean               -- accrued substate A (logs, accessed sets, refunds)
  Machine/
    MachineState.lean           -- machine state μ (gas, memory, returnData)
    SharedState.lean            -- world+machine bundle
  EVM/
    Operation.lean              -- 14-constructor Operation ADT, + EIP-8024
    Decode.lean                 -- byte → Operation + immediate decoder
    Gas.lean                    -- gas cost (real base fees; dynamic parts stubbed)
    Exception.lean              -- 8-variant ExecutionException
    State.lean                  -- EVM.State (pc, stack, halt, ...)
    Halted.lean                 -- ExecutionResult + State.toResult
    Step.lean                   -- Step wrapper + StepRunning/StepReturn rules
    BigStep.lean                -- reflexive-transitive Steps, big-step Eval
    StepF.lean                  -- executable shadow, split by Operation group
    Equiv.lean                  -- soundness lemmas (helper + headline)
```

## Build & run

```sh
lake build           # compile library + executable
.lake/build/bin/evm_semantics
```

A `lake exe cache get` is recommended after the first `lake update` to
fetch Mathlib's precompiled `.olean` artifacts. The cold build is
~10 minutes; cached, ~30 seconds.

## Linting

`lakefile.toml` registers Batteries' `runLinter` script as the project's
lint driver — the same one Mathlib uses for its own CI gate. Run it with:

```sh
lake lint
```

It runs the Batteries lint suite (missing doc-strings, `simpNF`, unused
arguments, dangerous instances, etc.) on every declaration under the
`EvmSemantics` namespace.

There is intentionally **no `scripts/nolints.json` allow-list file** —
all findings are addressed in source: short doc-strings everywhere, and
`@[nolint unusedArguments]` / `attribute [nolint ...]` annotations on
the handful of intentional exceptions (`Gas.sstoreCost`'s ignored `_original`,
`State.consumeGas`'s proof-witness `_h`, the auto-derived `Repr.repr`
declarations from `deriving Repr`, the trivial `Keccak.injEq` from a
single-constructor `deriving DecidableEq`, and the inner-loop helpers
generated by `let rec`).

CI (`.github/workflows/ci.yml`) runs both `lake build` (gated to fail
on any warning) and `lake lint` on every push and PR.

## Design overview

### Two semantics, one source of truth

- **`Step : EVM.State → EVM.State → Prop`** (small-step). A thin wrapper
  with two constructors — `running` (guards a `StepRunning` derivation
  with `s.halt = .Running`) and `returning` (wraps a `StepReturn`). The
  per-opcode logic lives in:
  - **`StepRunning`** — 90 constructors (81 success, one per opcode, +
    9 generic exception constructors parametric over the operation). No
    `h_running` premise on any of them; the guard is consumed once on
    the `Step.running` wrapper.
  - **`StepReturn`** — 3 `callReturn*` constructors for popping the
    caller frame when a child halts. Each pins the concrete halt kind
    and the non-empty call stack.
- **`Eval : EVM.State → ExecutionResult → Prop`** (big-step). Defined
  as the reflexive-transitive closure of `Step` ending in a halted
  state, projected via `State.toResult` to a flat
  `success | returned _ | reverted _ | exception _` sum.
- **`stepF : State → Except ExecutionException State`** (executable
  shadow). Mirrors `Step` opcode-by-opcode. Split into per-group
  helpers (`stepF.stopArith`, `stepF.compBit`, …) so each piece is
  small and individually reasoned about.

### Rule format

Most success constructors of `StepRunning` follow this anatomy (`stop` carries
only `h_op` — though `RETURN`/`REVERT` keep `h_gas`/`h_stack`/`h_mem` — and
stackless reads omit `h_stack`):

```lean
| add (s : State) (a b : UInt256) (rest : List UInt256)
      (h_op      : s.decodedOp = some .ADD)
      (h_gas     : Gas.baseCost s.fork .ADD ≤ s.gasAvailable)
      (h_stack   : s.stack = a :: b :: rest)
    : StepRunning s
        ((s.consumeGas (Gas.baseCost s.fork .ADD) h_gas).replaceStackAndIncrPC
          ((a + b) :: rest))
```

(`gasAvailable` is a `Nat`, so the gas premise is a plain `Nat` `≤`; the operand
stack is `List UInt256`. `s.decodedOp` is the op-only projection of `s.decoded`
— `pushN` is the one rule that uses the full `s.decoded`, since it consumes the
PUSH immediate.)

`consumeGas` takes the gas-sufficiency proof as an explicit argument so
the saturating Nat subtraction is provably safe — no truncation
case-splits in downstream proofs.

### Halt model

The `EVM.State` carries a `halt : HaltKind` field. The `Step.running`
wrapper carries `s.halt = .Running` as its precondition, and each
`StepReturn` constructor pins a concrete non-`Running` halt kind via
`h_halt`, so a *done* state (halted with empty call stack) has no
successors under `Step` (proven uniformly via `Step.not_from_done`).
This keeps `Step` as a plain binary relation while still letting `Eval`
emit a structured result.

### Soundness lemmas

`EVM/Equiv.lean` establishes `stepF_sound : stepF s = .ok s' → Step s s'`
**without any `sorry`**. The proof is layered:

- **Headline theorem `stepF_sound`** — unfolds `stepF`, splits on
  halt/decode/gas, then dispatches to the 14 per-helper soundness
  lemmas based on the top-level `Operation` constructor.
- **Per-helper soundness lemmas** — all 14 closed:
  `stopArith_sound`, `compBit_sound`, `keccak_sound`, `env_sound`,
  `block_sound`, `system_sound`, `stackMemFlow_sound`, `push_sound`,
  `log_sound`, `dup_sound`, `swap_sound`, `dupN_sound`, `swapN_sound`,
  `exchange_sound`.
- **Supporting lemma `popN_correct`** (in `StepF.lean`) — by induction
  on `k`, shows that if `popN stk k = some (topics, rest)` then
  `topics.length = k` and `stk = topics ++ rest`. Used by `log_sound`
  to recover the list-of-topics witness needed by `StepRunning.log`.

A small design tweak was needed to make the proof go through:
`StepRunning.pushN` now takes the immediate-width as an explicit parameter
(`immWidth : Nat`) rather than tying it to `k.val`, sidestepping a
decoder invariant that would otherwise need a separate lemma.

## Reference and credits

- The opcode list, state-record layout, and per-instruction semantics
  follow [NethermindEth/EVMYulLean](https://github.com/NethermindEth/EVMYulLean)
  closely. Anything ported verbatim should be attributed to that
  project.
- The Yellow Paper section numbers cited in comments correspond to the
  Cancun-era Ethereum spec.

## License

Apache2, as specified in LICENSE-APACHE2.
