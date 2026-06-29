# `GasFreeEVM` — design notes and completion plan

`EvmSemantics.GasFreeEVM` is a **gas-free parallel** to `EvmSemantics.EVM`,
intended to let users prove smart-contract correctness without threading
gas accounting through their proofs.

The user-facing object is `EvmSemantics.GasFreeEVM.Eval s r` (gas-free
big-step). The bridge to the gas-aware `EvmSemantics.EVM.Eval` (and
hence to `stepF`'s verified executable) lives in
`EvmSemantics/GasFreeEVM/Equiv.lean`. The intended top-level theorem is

```
EvmSemantics.GasFreeEVM.Eval s r → ∃ g, EvmSemantics.EVM.Eval { s with gasAvailable := g } r
```

i.e. "if your contract terminates with result `r` in the gas-free
semantics, then for some sufficient gas budget `g` it terminates with
`r` in the gas-aware semantics as well". This is **not yet proven** —
it's session 3+ work, sketched at the bottom of this document.

## Status as of this session

* **`StepNG.lean` and `BigStepNG.lean` are complete** (no `sorry`).
  - `StepRunning` (≈95 constructors) mirrors `EVM.StepRunning` with
    `h_gas` / `h_mem` / `h_dyn_gas` premises dropped and the
    corresponding `consumeGas` / `consumeMemExp` calls in the output
    replaced by the identity on gas (`s`) or `State.advanceMem` /
    `advanceMem2` (active-words advance, no gas).
  - `StepReturn` (3 constructors) is identical in shape to its
    gas-aware counterpart (the resume rules don't depend on `h_gas`).
  - `Step` is the two-constructor wrapper. `Eval` / `Steps` are the
    direct mirrors of `BigStep.lean`.
  - The `outOfGas` constructor is intentionally **absent** from
    `StepRunningNG` — the gas-free semantics has no notion of "running
    out of gas". The equivalence theorem surfaces this asymmetry via a
    `s' = s.haltWith .OutOfGas ∨ …` disjunction.

* **`Equiv.lean` is partial.** The easy direction
  `EVM.Step.to_NG : EVM.Step s s' → s' = s.haltWith .OutOfGas ∨ GasFreeEVM.Step s.dropGas s'.dropGas`
  is set up; its workhorse `StepRunning.to_NG_inner` closes **87 of the
  ~95 constructors** (every group except the five deferred ones below).
  All the `State`-level commutation lemmas (`dropGas` commutes with
  `consumeGas` / `consumeMemExp` / `replaceStackAndIncrPC` / `incrPC` /
  `haltWith` / `enterCall` / the three `resume*` helpers) are `@[simp]`
  and proved.

* **`EvalNG → ∃ g, Eval`** (the *hard* direction — the actually useful
  one for users) is **not yet attempted**.

## Deferred cases in `StepRunning.to_NG_inner`

The catch-all `| _ => sorry` in `to_NG_inner` covers five constructors.
Each is deferred for a different reason; here's the plan for each.

### 1. `GAS` — design question

The gas-aware `GAS` opcode pushes
`UInt256.ofNat (s.gasAvailable - baseCost s.fork .GAS)`. The gas-free
version (as currently written) pushes `UInt256.ofNat s.gasAvailable`.
These differ by exactly `baseCost s.fork .GAS`, and `dropGas` can't
reconcile them: it erases the gas *field* on the state but doesn't
reach into the pushed `UInt256` to undo the subtraction.

**Open question:** what should `GAS` push in a gas-free semantics?
Three options:

1. **Drop `GAS` from `StepRunningNG` entirely** (like `outOfGas`).
   Cleanest semantically — reading the remaining gas in a gas-free
   semantics doesn't mean anything. Cost: any contract that uses `GAS`
   becomes un-liftable to NG, so the equivalence theorem becomes
   conditional on "the contract doesn't use `GAS`".
2. **Make `GAS` non-deterministic in NG** — push an arbitrary value `g`.
   This requires existentially quantifying `g` in the constructor,
   which works in `Prop` but changes the inductive shape.
3. **Make `GAS` push `0`** (constant). Concrete and lift-able, but the
   pushed value is misleading.

Recommendation: option 1. The lift theorem becomes
`Eval s r → (some step used GAS) ∨ EvalNG s.dropGas r ∨ s'= …OutOfGas`.

### 2. `MLOAD` — `μ' : MachineState` mismatch

Both `EVM.StepRunning.mload` and `GasFreeEVM.StepRunning.mload` bind a
`μ' : MachineState` parameter and constrain it via `h_load`:

* EVM: `MachineState.mload (s.consumeMemExp off 32 h_mem).toMachineState off = (v, μ')`
* NG:  `MachineState.mload (s.advanceMem off 32).toMachineState off = (v, μ')`

These two `MachineState`s have the *same* memory and activeWords but
*different* `gasAvailable` (EVM has `s.gas - baseCost`, NG has `s.gas`).
So the `μ'` they bind to has different `gasAvailable` too. The `‹_›`
hypothesis lookup in `simpa using .mload _ _ _ _ _ ‹_› ‹_› ‹_›` fails
because the EVM-side `h_load` doesn't unify with the NG-shaped
hypothesis the constructor expects.

**Plan to fix:** either
- redesign `GasFreeEVM.StepRunning.mload` to take only the loaded value
  `v` (not `μ'`), inlining `mload` in the output expression; or
- prove a hand-rolled `have h_eq : { μ' with gasAvailable := 0 } = μ_ng`
  and rewrite before applying `.mload`.

The first is cleaner. Same fix applies to `MSTORE` / `MSTORE8` / `MCOPY`
if they hit the same issue (they didn't in this session, but the
fragility is worth noting).

### 3. `LOG` — `simp` recursion limit

`LOG`'s output threads a new log entry into the substate (`s.substate
:= s.substate.appendLog entry`) on top of the standard
memory-expansion + replaceStackAndIncrPC chain. `simpa` blows past the
default max-recursion limit chasing simp lemmas through the substate
update.

**Plan to fix:**
- `simp only [State.consumeMemExp_dropGas, State.replaceStackAndIncrPC_dropGas,
  State.dropGas]` (narrow simp set) instead of `simpa`; or
- a hand-rolled `have h_eq : (gas-aware output).dropGas = (gas-free output) := by …`
  using explicit `rfl` / `simp` steps.

### 4. `CALL` and `callFail` — gas-cascade intermediates

The EVM versions bind four intermediate states `s' s2 s3 s4` as explicit
parameters, each defined by a `consumeGas` / `consumeMemExp2` step.
The premises `h_take` (depth/balance check) and `h_fail` are stated
about `s3`, not `s`, and the output `s4.enterCall …` forwards
`forwarded` gas to the child. The gas-free versions collapse this:
`h_take` / `h_fail` are about `s` directly, and the child gets `0`
forwarded gas.

The values of the relevant fields (`executionEnv.depth`, account
balances) are the same on `s` and `s3` because `consumeGas` /
`consumeMemExp` only touch `gasAvailable` and `activeWords` — neither
of which appears in the depth/balance check. But the *types* of the
hypotheses are syntactically different (referring to `s3` not `s`),
so `‹_›` lookup fails.

**Plan to fix:** unfold `s'`, `s2`, `s3`, `s4` by hand via the binding
equations `h_s'`, `h_s2`, `h_s3`, `h_s4`, then use `simp` to reduce
`s3.executionEnv.depth` to `s.executionEnv.depth` and similarly for the
balance lookup. Roughly:

```lean
| call gasArg toArg value argsOff argsLen retOff retLen rest
    s' s2 s3 s4 forwarded h_op _ h_stack
    h_s' _ h_s2 _ h_s3 h_take h_fwd _ h_s4 =>
  subst h_s4; subst h_s3; subst h_s2; subst h_s'
  -- now `h_take` is about `s.consumeGas … |>.consumeMemExp2 … |>.consumeGas …`
  -- which simp can collapse to `s.executionEnv.depth` etc.
  simpa using .call _ _ _ _ _ _ _ _ _ _ _ ‹_› ‹_› (by simpa using h_take)
```

Same approach for `callFail`. Probably 20–30 lines per case rather
than the 1 line the easy cases get.

### 5. `outOfGas` — handled by `h_not_oog`

Not really deferred — the `outOfGas` constructor produces
`s.haltWith .OutOfGas`, which is exactly what `h_not_oog : s' ≠
s.haltWith .OutOfGas` refutes. The current code dispatches via
`exact absurd rfl h_not_oog`.

## Plan for the hard direction (sessions 3+)

The user-facing theorem is

```
theorem GasFreeEVM.Eval.gas_witness :
    GasFreeEVM.Eval s r → ∃ g, EvmSemantics.EVM.Eval { s with gasAvailable := g } r
```

Each `GasFreeEVM.Eval s r` derivation is a finite syntactic object — a
tree of `StepNG` transitions ending in a `halted` leaf — so by
structural induction we can extract a *computable* gas bound. The
recipe:

1. **Per-constructor cost function** `StepRunning.cost : StepRunning s s'
   → Nat` returning the gas the gas-aware version would consume for
   this one step (static base + dynamic surcharge for memory expansion,
   copy, etc.). About 95 lines (one per constructor), mostly mechanical.

2. **Per-derivation cost** `Eval.cost : Eval s r → Nat` summing the per-step
   costs along the trace. For CALL nodes, the parent's cost is
   `localCost(s) + 64/63 · childCost`, accounting for EIP-150 forwarding.

3. **Witness construction** `Eval.witness : (h : Eval s r) → State` that
   returns `{ s with gasAvailable := Eval.cost h }`. Show that this state
   has enough gas at every step.

4. **The lift theorem itself** — by induction on `h : Eval s r`,
   construct the matching `EVM.Eval { s with gasAvailable := Eval.cost h } r`.
   The non-OOG `StepRunning` constructors map cleanly (each gas-free rule
   has a matching gas-aware rule); the resume / done cases are mechanical.

The trickiest part is the CALL forwarding arithmetic: if a child subtree
needs `c_child` gas, the parent needs at least `pre_call_cost + ⌈64/63 ·
c_child⌉ + post_call_cost` gas at the CALL site so that after EIP-150
forwarding the child receives ≥ `c_child`. The bound is computable but
the algebra needs care (especially around the `min(gasArg, …)` clamp).

## Files

* `Step.lean` — the three inductives `StepRunning`, `StepReturn`,
  `Step`. Defines `State.advanceMem` / `advanceMem2` in the
  `EvmSemantics.EVM.State` namespace.
* `BigStep.lean` — `Steps`, `Eval`, `Steps.append/snoc`,
  `Eval.iff_steps_halted/of_halted`, `StepNG.not_from_done`.
* `Equiv.lean` — `dropGas` projection on `State`/`Frame`, ten
  `@[simp]` commutation lemmas, `StepReturn.to_NG`, `Step.to_NG` (both
  fully closed), `StepRunning.to_NG_inner` (87/95 cases closed, 1
  `sorry` for the catch-all).
* `PLAN.md` — this file.

The default `lake build` does not pull in `Equiv.lean` (it's not
re-exported from the root `EvmSemantics.lean`), so the remaining
`sorry` doesn't surface as a CI warning. To build `Equiv.lean`
explicitly: `lake build EvmSemantics.GasFreeEVM.Equiv`.
