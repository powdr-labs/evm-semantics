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

## Status — v1

| Phase | Description | State |
|---|---|---|
| 1 | Toolchain (Lean 4.31.0 + Mathlib v4.31.0) + foundation types | ✅ |
| 2 | `Operation` ADT (including EIP-8024 `DUPN`/`SWAPN`/`EXCHANGE`) and bytecode decoder | ✅ |
| 3 | Halted-state flag + `ExecutionResult` projection | ✅ |
| 4 | Small-step success rules (`Step`, 81 constructors) | ✅ |
| 5 | Small-step exception rules (`Step`, 9 generic constructors) | ✅ |
| 6 | Big-step relation (`Eval`) + reflexive-transitive closure `Steps` | ✅ |
| 7 | Executable shadow (`stepF`) + demo (`Main.lean`) | ✅ |
| 8 | Soundness `stepF s = .ok s' → Step s s'` | ✅ (no `sorry`) |

**Demo (`Main.lean`)** runs `PUSH1 5 ; PUSH1 3 ; ADD ; STOP` through the
executable shadow, producing stack `[8]` and `halt = Success`. Confirms
the relation/executable pair is at least internally consistent on a
trivial program.

## Scope (locked-in decisions)

- **Local-fragment EVM:** all arithmetic, comparison/bitwise, KECCAK256,
  environmental reads, block-context reads, memory, storage (incl.
  transient), stack manipulation (POP, PUSH0–PUSH32, DUP1–16, SWAP1–16),
  control flow (JUMP, JUMPI, JUMPDEST, PC, GAS), halts (STOP, RETURN,
  REVERT, INVALID), logging (LOG0–LOG4), and EIP-8024 (DUPN, SWAPN,
  EXCHANGE).
- **Excluded from v1:** `CALL` family, `CREATE`/`CREATE2`, `SELFDESTRUCT`,
  transaction processing (`Υ`), block validation, precompiled
  contracts, RLP encoding.
- **Gas:** uniform 1 unit per opcode. The shape of the `OutOfGas`
  exception rule is faithful; only the cost function is a stub. Replacing
  it with the Yellow Paper schedule is local to `EVM/Gas.lean`.
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
    Stack.lean                  -- list-backed stack with popₙ / exchange
    UInt256.lean                -- 256-bit words, modular arithmetic
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
    Gas.lean                    -- gas cost function (currently uniform 1)
    Exception.lean              -- 8-variant ExecutionException
    State.lean                  -- EVM.State (pc, stack, halt, ...)
    Halted.lean                 -- ExecutionResult + State.toResult
    Step.lean                   -- the small-step relation (90 constructors)
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
the handful of intentional exceptions (`Gas.cost`'s ignored `_op`,
`State.consumeGas`'s proof-witness `_h`, the auto-derived `Repr.repr`
declarations from `deriving Repr`, the trivial `Keccak.injEq` from a
single-constructor `deriving DecidableEq`, and the inner-loop helpers
generated by `let rec`).

CI (`.github/workflows/ci.yml`) runs both `lake build` (gated to fail
on any warning) and `lake lint` on every push and PR.

## Design overview

### Two semantics, one source of truth

- **`Step : EVM.State → EVM.State → Prop`** (small-step). One
  constructor per opcode for the success path, plus generic exception
  constructors parametric over the operation. Total: 89 constructors.
- **`Eval : EVM.State → ExecutionResult → Prop`** (big-step). Defined
  as the reflexive-transitive closure of `Step` ending in a halted
  state, projected via `State.toResult` to a flat
  `success | returned _ | reverted _ | exception _` sum.
- **`stepF : State → Except ExecutionException State`** (executable
  shadow). Mirrors `Step` opcode-by-opcode. Split into per-group
  helpers (`stepF.stopArith`, `stepF.compBit`, …) so each piece is
  small and individually reasoned about.

### Rule format

Every success constructor of `Step` follows this anatomy:

```lean
| add (s : State) (a b : UInt256) (rest : Stack UInt256)
      (h_op      : s.decoded = some (.ADD, none))
      (h_running : s.halt = .Running)
      (h_gas     : Gas.cost .ADD ≤ s.gasAvailable.toNat)
      (h_stack   : s.stack = a :: b :: rest)
    : Step s ((s.consumeGas (Gas.cost .ADD) h_gas).replaceStackAndIncrPC ((a + b) :: rest))
```

`consumeGas` takes the gas-sufficiency proof as an explicit argument so
the saturating Nat subtraction is provably safe — no truncation
case-splits in downstream proofs.

### Halt model

The `EVM.State` carries a `halt : HaltKind` field. Each `Step`
constructor has a `h_running : s.halt = .Running` premise, so halted
states have no successors (proven uniformly via `Step.not_from_halted`).
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
  to recover the list-of-topics witness needed by `Step.log`.

A small design tweak was needed to make the proof go through:
`Step.pushN` now takes the immediate-width as an explicit parameter
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
