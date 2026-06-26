module

public import EvmSemantics.EVM.Step
public import EvmSemantics.EVM.StepF
public import EvmSemantics.EVM.BigStep

/-!
`Equiv` — soundness of `stepF` with respect to the relational `Step`.

**Statement.** `stepF_sound : stepF s = .ok s' → Step s s'`. Every state
transition produced by the *executable* `stepF` is also a valid
derivation of the relational small-step `Step`. The theorem is **closed**
(no `sorry`).

**Structure.** `stepF` is split into per-`Operation`-constructor
helpers (`stepF.stopArith`, `stepF.compBit`, …) in `StepF.lean`.
Soundness is proven in two layers:

1. **Per-helper soundness** (`stopArith_sound`, `compBit_sound`,
   `keccak_sound`, `env_sound`, `block_sound`, `stackMemFlow_sound`,
   `push_sound`, `log_sound`, `dup_sound`, `swap_sound`, `dupN_sound`,
   `swapN_sound`, `exchange_sound`, `system_sound`) — each helper is
   inverted by `unfold` + `match` on the operation kind and stack
   shape, then closes its leaves by either applying the matching
   `Step` constructor or by deriving a contradiction from `h : … = .ok _`
   when `stepF` returned `.error`.
2. **Top-level `stepF_sound`** — unfolds `stepF`, splits on
   `s.halt` / `s.decoded` / the gas check / the operation kind, and
   dispatches each `Operation` constructor to the corresponding
   helper lemma.

We also export `Eval.halted_inv` (a halted state's only `Eval`
derivation is `Eval.halted`), which doesn't depend on `stepF`.
-/

@[expose] public section

namespace EvmSemantics
namespace EVM

----------------------------------------------------------------------------
-- Lemmas about `Eval` that don't go through `stepF`.
----------------------------------------------------------------------------

/-- A *done* state's (halted, empty call stack) only `Eval` derivation is
    `Eval.halted`. -/
theorem Eval.halted_inv {s : State} {r : ExecutionResult}
    (h_halt : s.halt ≠ .Running) (h_cs : s.callStack = []) (h_eval : Eval s r) :
    r = s.toResult := by
  cases h_eval with
  | halted _ _ => rfl
  | stepThen st _ => exact absurd (Step.not_from_done st h_halt h_cs) (fun h => h)

----------------------------------------------------------------------------
-- Helper soundness lemmas.
--
-- Each lemma proves that calling a `stepF.*` helper with sufficient gas
-- yields a valid `StepRunning` derivation. The proof destructures the
-- helper's `match`, then applies the relevant `StepRunning` constructor.
-- The headline `stepF_sound` wraps the result with `Step.running`,
-- supplying the `s.halt = .Running` hypothesis once at the outer
-- dispatcher.
----------------------------------------------------------------------------

namespace stepF

theorem stopArith_sound (s : State) (op : Operation.StopArithOps)
    (h_dec : s.decodedOp = some (.StopArith op))
    (h_gas : Gas.baseCost s.fork (.StopArith op) ≤ s.gasAvailable)
    {sf : State}
    (h : stepF.stopArith s (s.consumeGas (Gas.baseCost s.fork (.StopArith op)) h_gas) op
           = .ok sf) :
    StepRunning s sf := by
  unfold stepF.stopArith at h
  cases op with
  | STOP =>
    -- Note STOP's success doesn't depend on h_gas in the StepRunning constructor.
    cases h; exact .stop s h_dec
  | ADD =>
    match h_stack : s.stack, h with
    | a :: b :: rest, h => cases h; exact .add s a b rest h_dec h_gas h_stack
    | [], h           => nomatch h
    | [_], h          => nomatch h
  | MUL =>
    match h_stack : s.stack, h with
    | a :: b :: rest, h => cases h; exact .mul s a b rest h_dec h_gas h_stack
    | [], h           => nomatch h
    | [_], h          => nomatch h
  | SUB =>
    match h_stack : s.stack, h with
    | a :: b :: rest, h => cases h; exact .sub s a b rest h_dec h_gas h_stack
    | [], h           => nomatch h
    | [_], h          => nomatch h
  | DIV =>
    match h_stack : s.stack, h with
    | a :: b :: rest, h => cases h; exact .div s a b rest h_dec h_gas h_stack
    | [], h           => nomatch h
    | [_], h          => nomatch h
  | SDIV =>
    match h_stack : s.stack, h with
    | a :: b :: rest, h => cases h; exact .sdiv s a b rest h_dec h_gas h_stack
    | [], h           => nomatch h
    | [_], h          => nomatch h
  | MOD =>
    match h_stack : s.stack, h with
    | a :: b :: rest, h => cases h; exact .mod s a b rest h_dec h_gas h_stack
    | [], h           => nomatch h
    | [_], h          => nomatch h
  | SMOD =>
    match h_stack : s.stack, h with
    | a :: b :: rest, h => cases h; exact .smod s a b rest h_dec h_gas h_stack
    | [], h           => nomatch h
    | [_], h          => nomatch h
  | ADDMOD =>
    match h_stack : s.stack, h with
    | a :: b :: n :: rest, h =>
      cases h; exact .addmod s a b n rest h_dec h_gas h_stack
    | [], h           => nomatch h
    | [_], h          => nomatch h
    | [_, _], h       => nomatch h
  | MULMOD =>
    match h_stack : s.stack, h with
    | a :: b :: n :: rest, h =>
      cases h; exact .mulmod s a b n rest h_dec h_gas h_stack
    | [], h           => nomatch h
    | [_], h          => nomatch h
    | [_, _], h       => nomatch h
  | EXP =>
    match h_stack : s.stack, h with
    | a :: b :: rest, h =>
        by_cases h_dyn : Gas.expByteCost s.fork b
                          ≤ (s.consumeGas (Gas.baseCost s.fork (.StopArith .EXP))
                                h_gas).gasAvailable
        · simp [h_dyn] at h
          cases h
          -- `stepF` uses the fast modular-exponentiation `expFast`; the relation
          -- `StepRunning.exp` uses the `exp` specification. They agree (`expFast_eq_exp`).
          rw [UInt256.expFast_eq_exp]
          exact .exp s a b rest h_dec h_gas h_stack h_dyn
        · simp [h_dyn] at h
    | [], h           => nomatch h
    | [_], h          => nomatch h
  | SIGNEXTEND =>
    match h_stack : s.stack, h with
    | a :: b :: rest, h =>
      cases h; exact .signextend s a b rest h_dec h_gas h_stack
    | [], h           => nomatch h
    | [_], h          => nomatch h

theorem compBit_sound (s : State) (op : Operation.CompareBitwiseOps)
    (h_dec : s.decodedOp = some (.CompBit op))
    (h_gas : Gas.baseCost s.fork (.CompBit op) ≤ s.gasAvailable)
    {sf : State}
    (h : stepF.compBit s (s.consumeGas (Gas.baseCost s.fork (.CompBit op)) h_gas) op = .ok sf) :
    StepRunning s sf := by
  unfold stepF.compBit at h
  cases op with
  | LT =>
    match h_stack : s.stack, h with
    | a :: b :: rest, h => cases h; exact .lt s a b rest h_dec h_gas h_stack
    | [], h           => nomatch h
    | [_], h          => nomatch h
  | GT =>
    match h_stack : s.stack, h with
    | a :: b :: rest, h => cases h; exact .gt s a b rest h_dec h_gas h_stack
    | [], h           => nomatch h
    | [_], h          => nomatch h
  | SLT =>
    match h_stack : s.stack, h with
    | a :: b :: rest, h => cases h; exact .slt s a b rest h_dec h_gas h_stack
    | [], h           => nomatch h
    | [_], h          => nomatch h
  | SGT =>
    match h_stack : s.stack, h with
    | a :: b :: rest, h => cases h; exact .sgt s a b rest h_dec h_gas h_stack
    | [], h           => nomatch h
    | [_], h          => nomatch h
  | EQ =>
    match h_stack : s.stack, h with
    | a :: b :: rest, h => cases h; exact .eq s a b rest h_dec h_gas h_stack
    | [], h           => nomatch h
    | [_], h          => nomatch h
  | ISZERO =>
    match h_stack : s.stack, h with
    | a :: rest, h => cases h; exact .iszero s a rest h_dec h_gas h_stack
    | [], h       => nomatch h
  | AND =>
    match h_stack : s.stack, h with
    | a :: b :: rest, h => cases h; exact .and s a b rest h_dec h_gas h_stack
    | [], h           => nomatch h
    | [_], h          => nomatch h
  | OR =>
    match h_stack : s.stack, h with
    | a :: b :: rest, h => cases h; exact .or s a b rest h_dec h_gas h_stack
    | [], h           => nomatch h
    | [_], h          => nomatch h
  | XOR =>
    match h_stack : s.stack, h with
    | a :: b :: rest, h => cases h; exact .xor_ s a b rest h_dec h_gas h_stack
    | [], h           => nomatch h
    | [_], h          => nomatch h
  | NOT =>
    match h_stack : s.stack, h with
    | a :: rest, h => cases h; exact .not s a rest h_dec h_gas h_stack
    | [], h       => nomatch h
  | BYTE =>
    match h_stack : s.stack, h with
    | i :: x :: rest, h => cases h; exact .byte_ s i x rest h_dec h_gas h_stack
    | [], h           => nomatch h
    | [_], h          => nomatch h
  | SHL =>
    match h_stack : s.stack, h with
    | sh :: v :: rest, h => cases h; exact .shl s sh v rest h_dec h_gas h_stack
    | [], h           => nomatch h
    | [_], h          => nomatch h
  | SHR =>
    match h_stack : s.stack, h with
    | sh :: v :: rest, h => cases h; exact .shr s sh v rest h_dec h_gas h_stack
    | [], h           => nomatch h
    | [_], h          => nomatch h
  | SAR =>
    match h_stack : s.stack, h with
    | sh :: v :: rest, h => cases h; exact .sar s sh v rest h_dec h_gas h_stack
    | [], h           => nomatch h
    | [_], h          => nomatch h

theorem keccak_sound (s : State) (op : Operation.KeccakOps)
    (h_dec : s.decodedOp = some (.Keccak op))
    (h_gas : Gas.baseCost s.fork (.Keccak op) ≤ s.gasAvailable)
    {sf : State}
    (h : stepF.keccak s (s.consumeGas (Gas.baseCost s.fork (.Keccak op)) h_gas) op = .ok sf) :
    StepRunning s sf := by
  unfold stepF.keccak at h
  cases op with
  | KECCAK256 =>
    match h_stack : s.stack, h with
    | offset :: size :: rest, h =>
      unfold chargeMem at h
      by_cases h_mem :
          (s.consumeGas (Gas.baseCost s.fork (.Keccak .KECCAK256)) h_gas).canExpandMemory
            offset.toNat size.toNat
      · simp [h_mem] at h
        by_cases h_dyn : Gas.keccakWordCost size ≤
            ((s.consumeGas (Gas.baseCost s.fork (.Keccak .KECCAK256))
                            h_gas).consumeMemExp offset.toNat size.toNat h_mem).gasAvailable
        · simp [h_dyn] at h
          cases h
          exact .keccak256 s offset size rest h_dec h_gas h_stack h_mem h_dyn
        · simp [h_dyn] at h
      · simp [h_mem] at h
    | [], h           => nomatch h
    | [_], h          => nomatch h

theorem block_sound (s : State) (op : Operation.BlockOps)
    (h_dec : s.decodedOp = some (.Block op))
    (h_gas : Gas.baseCost s.fork (.Block op) ≤ s.gasAvailable)
    {sf : State}
    (h : stepF.block s (s.consumeGas (Gas.baseCost s.fork (.Block op)) h_gas) op = .ok sf) :
    StepRunning s sf := by
  unfold stepF.block at h
  cases op with
  | BLOCKHASH =>
    match h_stack : s.stack, h with
    | n :: rest, h => cases h; exact .blockhash s n rest h_dec h_gas h_stack
    | [], h       => nomatch h
  | COINBASE    => cases h; exact .coinbase s h_dec h_gas
  | TIMESTAMP   => cases h; exact .timestamp s h_dec h_gas
  | NUMBER      => cases h; exact .number s h_dec h_gas
  | PREVRANDAO  => cases h; exact .prevrandao s h_dec h_gas
  | GASLIMIT    => cases h; exact .gaslimit s h_dec h_gas
  | CHAINID     => cases h; exact .chainid s h_dec h_gas
  | SELFBALANCE => cases h; exact .selfbalance s h_dec h_gas
  | BASEFEE     => cases h; exact .basefee s h_dec h_gas
  | BLOBBASEFEE => cases h; exact .blobbasefee s h_dec h_gas
  | BLOBHASH =>
    match h_stack : s.stack, h with
    | i :: rest, h =>
      -- BLOBHASH always returns ok (lookup defaults to 0) — use in-bounds or oob rule
      cases h_lookup : s.executionEnv.blobVersionedHashes[i.toNat]? with
      | some bh =>
        simp [h_lookup] at h; cases h
        exact .blobhash s i rest bh h_dec h_gas h_stack h_lookup
      | none =>
        simp [h_lookup] at h; cases h
        exact .blobhash_oob s i rest h_dec h_gas h_stack h_lookup
    | [], h => nomatch h

theorem system_sound (s : State) (op : Operation.SystemOps)
    (h_dec : s.decodedOp = some (.System op))
    (h_gas : Gas.baseCost s.fork (.System op) ≤ s.gasAvailable)
    {sf : State}
    (h : stepF.system s (s.consumeGas (Gas.baseCost s.fork (.System op)) h_gas) op = .ok sf) :
    StepRunning s sf := by
  unfold stepF.system at h
  cases op with
  | RETURN =>
    match h_stack : s.stack, h with
    | offset :: size :: rest, h =>
      unfold chargeMem at h
      by_cases h_mem :
          (s.consumeGas (Gas.baseCost s.fork (.System .RETURN)) h_gas).canExpandMemory
                         offset.toNat size.toNat
      · simp [h_mem] at h
        cases h
        exact .return_ s offset size rest h_dec h_gas h_stack h_mem
      · simp [h_mem] at h
    | [], h           => nomatch h
    | [_], h          => nomatch h
  | REVERT =>
    match h_stack : s.stack, h with
    | offset :: size :: rest, h =>
      unfold chargeMem at h
      by_cases h_mem :
          (s.consumeGas (Gas.baseCost s.fork (.System .REVERT)) h_gas).canExpandMemory
                         offset.toNat size.toNat
      · simp [h_mem] at h
        cases h
        exact .revert s offset size rest h_dec h_gas h_stack h_mem
      · simp [h_mem] at h
    | [], h           => nomatch h
    | [_], h          => nomatch h
  | INVALID =>
    -- stepF.system returns .error on INVALID; no .ok possible
    nomatch h
  | CALL =>
    match h_stack : s.stack, h with
    | gasArg :: toArg :: value :: argsOff :: argsLen :: retOff :: retLen :: rest, h =>
      -- First dispatch the static-mode value-transfer check (`stepF` rejects
      -- a value-transferring CALL in a static frame before doing anything):
      -- the true branch returns `.error`, contradicting `h : … = .ok sf`.
      by_cases h_static : ¬ s.executionEnv.permitStateMutation ∧ value.toNat ≠ 0
      · simp only [if_pos h_static, static] at h
        cases h
      · simp only [if_neg h_static] at h
        unfold chargeMem2 at h
        by_cases h_mem :
            (s.consumeGas (Gas.baseCost s.fork (.System .CALL)) h_gas).canExpandMemory2
              argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat
        · -- memory expansion affordable; reduce the chargeMem2 match, then split
          -- the remaining surcharge / depth-balance / forwarding branches.
          simp only [h_mem, dif_pos] at h
          split at h
          · rename_i h_sc
            split at h
            · -- depth limit or insufficient balance ⇒ not taken
              rename_i h_fail
              cases h
              exact .callFail s gasArg toArg value argsOff argsLen retOff retLen rest
                _ _ _ h_dec h_gas h_stack rfl h_mem rfl h_sc rfl h_fail
            · -- taken
              rename_i h_take
              split at h
              · rename_i h_fw
                cases h
                exact .call s gasArg toArg value argsOff argsLen retOff retLen rest
                  _ _ _ _ _ h_dec h_gas h_stack rfl h_mem rfl h_sc rfl
                  h_take rfl h_fw rfl
              · nomatch h
          · nomatch h
        · simp [h_mem] at h
    | [], h                                  => nomatch h
    | [_], h                                 => nomatch h
    | [_, _], h                              => nomatch h
    | [_, _, _], h                           => nomatch h
    | [_, _, _, _], h                        => nomatch h
    | [_, _, _, _, _], h                     => nomatch h
    | [_, _, _, _, _, _], h                  => nomatch h
  | CALLCODE =>
    match h_stack : s.stack, h with
    | gasArg :: toArg :: value :: argsOff :: argsLen :: retOff :: retLen :: rest, h =>
      unfold chargeMem2 at h
      by_cases h_mem :
          (s.consumeGas (Gas.baseCost s.fork (.System .CALLCODE)) h_gas).canExpandMemory2
            argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat
      · simp only [h_mem, dif_pos] at h
        split at h
        · rename_i h_sc
          split at h
          · rename_i h_fail
            cases h
            exact .callcodeFail s gasArg toArg value argsOff argsLen retOff retLen rest
              _ _ _ h_dec h_gas h_stack rfl h_mem rfl h_sc rfl h_fail
          · rename_i h_take
            split at h
            · rename_i h_fw
              cases h
              exact .callcode s gasArg toArg value argsOff argsLen retOff retLen rest
                _ _ _ _ _ h_dec h_gas h_stack rfl h_mem rfl h_sc rfl
                h_take rfl h_fw rfl
            · nomatch h
        · nomatch h
      · simp [h_mem] at h
    | [], h                                  => nomatch h
    | [_], h                                 => nomatch h
    | [_, _], h                              => nomatch h
    | [_, _, _], h                           => nomatch h
    | [_, _, _, _], h                        => nomatch h
    | [_, _, _, _, _], h                     => nomatch h
    | [_, _, _, _, _, _], h                  => nomatch h
  -- Out-of-scope ops: stepF returns .error
  | CREATE | CREATE2 | DELEGATECALL | STATICCALL | SELFDESTRUCT =>
    nomatch h

theorem dup_sound (s : State) (op : Operation.DupOp)
    (h_dec : s.decodedOp = some (.Dup op))
    (h_gas : Gas.baseCost s.fork (.Dup op) ≤ s.gasAvailable)
    {sf : State}
    (h : stepF.dup s (s.consumeGas (Gas.baseCost s.fork (.Dup op)) h_gas) op = .ok sf) :
    StepRunning s sf := by
  unfold stepF.dup at h
  match h_get : s.stack[op.idx.val]?, h with
  | some v, h => cases h
                 obtain ⟨idx⟩ := op
                 exact .dup s idx v h_dec h_gas h_get
  | none, h   => nomatch h

theorem swap_sound (s : State) (op : Operation.SwapOp)
    (h_dec : s.decodedOp = some (.Swap op))
    (h_gas : Gas.baseCost s.fork (.Swap op) ≤ s.gasAvailable)
    {sf : State}
    (h : stepF.swap s (s.consumeGas (Gas.baseCost s.fork (.Swap op)) h_gas) op = .ok sf) :
    StepRunning s sf := by
  unfold stepF.swap at h
  match h_ex : s.stack.exchange 0 (op.idx.val + 1), h with
  | some stk', h => cases h
                    obtain ⟨idx⟩ := op
                    exact .swap s idx stk' h_dec h_gas h_ex
  | none, h      => nomatch h

theorem dupN_sound (s : State) (op : Operation.DupNOp)
    (h_dec : s.decodedOp = some (.DupN op))
    (h_gas : Gas.baseCost s.fork (.DupN op) ≤ s.gasAvailable)
    {sf : State}
    (h : stepF.dupN s (s.consumeGas (Gas.baseCost s.fork (.DupN op)) h_gas) op = .ok sf) :
    StepRunning s sf := by
  unfold stepF.dupN at h
  match h_get : s.stack[op.n.val]?, h with
  | some v, h => cases h
                 obtain ⟨n⟩ := op
                 exact .dupN s n v h_dec h_gas h_get
  | none, h   => nomatch h

theorem swapN_sound (s : State) (op : Operation.SwapNOp)
    (h_dec : s.decodedOp = some (.SwapN op))
    (h_gas : Gas.baseCost s.fork (.SwapN op) ≤ s.gasAvailable)
    {sf : State}
    (h : stepF.swapN s (s.consumeGas (Gas.baseCost s.fork (.SwapN op)) h_gas) op = .ok sf) :
    StepRunning s sf := by
  unfold stepF.swapN at h
  match h_ex : s.stack.exchange 0 (op.n.val + 1), h with
  | some stk', h => cases h
                    obtain ⟨n⟩ := op
                    exact .swapN s n stk' h_dec h_gas h_ex
  | none, h      => nomatch h

theorem exchange_sound (s : State) (op : Operation.ExchangeOp)
    (h_dec : s.decodedOp = some (.Exchange op))
    (h_gas : Gas.baseCost s.fork (.Exchange op) ≤ s.gasAvailable)
    {sf : State}
    (h : stepF.exchange s (s.consumeGas (Gas.baseCost s.fork (.Exchange op)) h_gas) op = .ok sf) :
    StepRunning s sf := by
  unfold stepF.exchange at h
  match h_ex : s.stack.exchange (op.n + 1) (op.m + 1), h with
  | some stk', h => cases h
                    obtain ⟨b⟩ := op
                    exact .exchange s b stk' h_dec h_gas h_ex
  | none, h      => nomatch h

theorem env_sound (s : State) (op : Operation.EnvOps)
    (h_dec : s.decodedOp = some (.Env op))
    (h_gas : Gas.baseCost s.fork (.Env op) ≤ s.gasAvailable)
    {sf : State}
    (h : stepF.env s (s.consumeGas (Gas.baseCost s.fork (.Env op)) h_gas) op = .ok sf) :
    StepRunning s sf := by
  unfold stepF.env at h
  cases op with
  | ADDRESS         => cases h; exact .address s h_dec h_gas
  | ORIGIN          => cases h; exact .origin s h_dec h_gas
  | CALLER          => cases h; exact .caller s h_dec h_gas
  | CALLVALUE       => cases h; exact .callvalue s h_dec h_gas
  | CALLDATASIZE    => cases h; exact .calldatasize s h_dec h_gas
  | CODESIZE        => cases h; exact .codesize s h_dec h_gas
  | GASPRICE        => cases h; exact .gasprice s h_dec h_gas
  | RETURNDATASIZE  => cases h; exact .returndatasize s h_dec h_gas
  | BALANCE =>
    match h_stack : s.stack, h with
    | a :: rest, h => cases h; exact .balance s a rest h_dec h_gas h_stack
    | [], h       => nomatch h
  | CALLDATALOAD =>
    match h_stack : s.stack, h with
    | i :: rest, h => cases h; exact .calldataload s i rest h_dec h_gas h_stack
    | [], h       => nomatch h
  | EXTCODESIZE =>
    match h_stack : s.stack, h with
    | a :: rest, h => cases h; exact .extcodesize s a rest h_dec h_gas h_stack
    | [], h       => nomatch h
  | EXTCODEHASH =>
    match h_stack : s.stack, h with
    | a :: rest, h => cases h; exact .extcodehash s a rest h_dec h_gas h_stack
    | [], h       => nomatch h
  | CALLDATACOPY =>
    match h_stack : s.stack, h with
    | dOff :: sOff :: sz :: rest, h =>
      unfold chargeMem at h
      by_cases h_mem :
          (s.consumeGas (Gas.baseCost s.fork (.Env .CALLDATACOPY)) h_gas).canExpandMemory
                         dOff.toNat sz.toNat
      · simp [h_mem] at h
        by_cases h_dyn : Gas.copyWordCost sz ≤
            ((s.consumeGas (Gas.baseCost s.fork (.Env .CALLDATACOPY))
                            h_gas).consumeMemExp dOff.toNat sz.toNat h_mem).gasAvailable
        · simp [h_dyn] at h
          cases h
          exact .calldatacopy s dOff sOff sz rest h_dec h_gas h_stack h_mem h_dyn
        · simp [h_dyn] at h
      · simp [h_mem] at h
    | [], h     => nomatch h
    | [_], h    => nomatch h
    | [_, _], h => nomatch h
  | CODECOPY =>
    match h_stack : s.stack, h with
    | dOff :: sOff :: sz :: rest, h =>
      unfold chargeMem at h
      by_cases h_mem :
          (s.consumeGas (Gas.baseCost s.fork (.Env .CODECOPY)) h_gas).canExpandMemory
                         dOff.toNat sz.toNat
      · simp [h_mem] at h
        by_cases h_dyn : Gas.copyWordCost sz ≤
            ((s.consumeGas (Gas.baseCost s.fork (.Env .CODECOPY))
                            h_gas).consumeMemExp dOff.toNat sz.toNat h_mem).gasAvailable
        · simp [h_dyn] at h
          cases h
          exact .codecopy s dOff sOff sz rest h_dec h_gas h_stack h_mem h_dyn
        · simp [h_dyn] at h
      · simp [h_mem] at h
    | [], h     => nomatch h
    | [_], h    => nomatch h
    | [_, _], h => nomatch h
  | EXTCODECOPY =>
    match h_stack : s.stack, h with
    | a :: dOff :: sOff :: sz :: rest, h =>
      unfold chargeMem at h
      by_cases h_mem :
          (s.consumeGas (Gas.baseCost s.fork (.Env .EXTCODECOPY)) h_gas).canExpandMemory
                         dOff.toNat sz.toNat
      · simp [h_mem] at h
        by_cases h_dyn : Gas.copyWordCost sz ≤
            ((s.consumeGas (Gas.baseCost s.fork (.Env .EXTCODECOPY))
                            h_gas).consumeMemExp dOff.toNat sz.toNat h_mem).gasAvailable
        · simp [h_dyn] at h
          cases h
          exact .extcodecopy s a dOff sOff sz rest h_dec h_gas h_stack h_mem h_dyn
        · simp [h_dyn] at h
      · simp [h_mem] at h
    | [], h        => nomatch h
    | [_], h       => nomatch h
    | [_, _], h    => nomatch h
    | [_, _, _], h => nomatch h
  | RETURNDATACOPY =>
    match h_stack : s.stack, h with
    | dOff :: sOff :: sz :: rest, h =>
      by_cases h_oob : sOff.toNat + sz.toNat > s.returnData.size
      · simp [h_oob] at h
      · simp [h_oob] at h
        unfold chargeMem at h
        by_cases h_mem :
            (s.consumeGas (Gas.baseCost s.fork (.Env .RETURNDATACOPY)) h_gas).canExpandMemory
                           dOff.toNat sz.toNat
        · simp [h_mem] at h
          by_cases h_dyn : Gas.copyWordCost sz ≤
              ((s.consumeGas (Gas.baseCost s.fork (.Env .RETURNDATACOPY))
                              h_gas).consumeMemExp dOff.toNat sz.toNat h_mem).gasAvailable
          · simp [h_dyn] at h
            cases h
            exact .returndatacopy s dOff sOff sz rest h_dec h_gas h_stack
                    (Nat.le_of_not_lt h_oob) h_mem h_dyn
          · simp [h_dyn] at h
        · simp [h_mem] at h
    | [], h     => nomatch h
    | [_], h    => nomatch h
    | [_, _], h => nomatch h

set_option maxRecDepth 1024 in
theorem stackMemFlow_sound (s : State) (op : Operation.StackMemFlowOps)
    (h_dec : s.decodedOp = some (.StackMemFlow op))
    (h_gas : Gas.baseCost s.fork (.StackMemFlow op) ≤ s.gasAvailable)
    {sf : State} (h : stepF.stackMemFlow s
                        (s.consumeGas (Gas.baseCost s.fork (.StackMemFlow op)) h_gas) op = .ok sf) :
    StepRunning s sf := by
  unfold stepF.stackMemFlow at h
  cases op with
  | POP =>
    match h_stack : s.stack, h with
    | a :: rest, h => cases h; exact .pop s a rest h_dec h_gas h_stack
    | [], h       => nomatch h
  | MLOAD =>
    match h_stack : s.stack, h with
    | offset :: rest, h =>
      unfold chargeMem at h
      by_cases h_mem :
          (s.consumeGas (Gas.baseCost s.fork (.StackMemFlow .MLOAD)) h_gas).canExpandMemory
                         offset.toNat 32
      · simp [h_mem] at h
        cases h_load : MachineState.mload
                         ((s.consumeGas (Gas.baseCost s.fork (.StackMemFlow .MLOAD))
                              h_gas).consumeMemExp
                            offset.toNat 32 h_mem).toMachineState offset with
        | mk v μ' =>
          simp [h_load] at h; cases h
          exact .mload s offset rest v μ' h_dec h_gas h_stack h_mem h_load
      · simp [h_mem] at h
    | [], h => nomatch h
  | MSTORE =>
    match h_stack : s.stack, h with
    | offset :: value :: rest, h =>
      unfold chargeMem at h
      by_cases h_mem :
          (s.consumeGas (Gas.baseCost s.fork (.StackMemFlow .MSTORE)) h_gas).canExpandMemory
                         offset.toNat 32
      · simp [h_mem] at h
        cases h
        exact .mstore s offset value rest h_dec h_gas h_stack h_mem
      · simp [h_mem] at h
    | [], h     => nomatch h
    | [_], h    => nomatch h
  | MSTORE8 =>
    match h_stack : s.stack, h with
    | offset :: value :: rest, h =>
      unfold chargeMem at h
      by_cases h_mem :
          (s.consumeGas (Gas.baseCost s.fork (.StackMemFlow .MSTORE8)) h_gas).canExpandMemory
                         offset.toNat 1
      · simp [h_mem] at h
        cases h
        exact .mstore8 s offset value rest h_dec h_gas h_stack h_mem
      · simp [h_mem] at h
    | [], h     => nomatch h
    | [_], h    => nomatch h
  | SLOAD =>
    match h_stack : s.stack, h with
    | key :: rest, h => cases h; exact .sload s key rest h_dec h_gas h_stack
    | [], h         => nomatch h
  | SSTORE =>
    by_cases h_perm : ¬ s.executionEnv.permitStateMutation
    · -- stepF returns static violation; no .ok
      simp [h_perm] at h
      unfold static at h; cases h
    · simp [h_perm] at h
      match h_sentry : Gas.sstoreSentry s.fork
          (s.consumeGas (Gas.baseCost s.fork (.StackMemFlow .SSTORE))
             h_gas).gasAvailable with
      | true =>
        -- EIP-2200 sentry fires → stepF returns OutOfGas, no .ok
        simp [h_sentry] at h
      | false =>
        simp [h_sentry] at h
        match h_stack : s.stack, h with
        | key :: value :: rest, h =>
          by_cases h_dyn :
            Gas.sstoreCost s.fork
                (s.substate.originalStorage s.executionEnv.codeOwner key)
                ((s.accountMap s.executionEnv.codeOwner).storage key) value
              ≤ (s.consumeGas (Gas.baseCost s.fork (.StackMemFlow .SSTORE))
                    h_gas).gasAvailable
          · simp [h_dyn] at h
            cases h
            exact .sstore s key value rest h_dec
                    (by simp at h_perm; exact h_perm) h_gas h_stack h_sentry h_dyn
          · simp [h_dyn] at h
        | [], h     => nomatch h
        | [_], h    => nomatch h
  | JUMP =>
    match h_stack : s.stack, h with
    | dest :: rest, h =>
      match h_valid : Decode.isValidJumpDest s.executionEnv.code dest.toNat, h with
      | true, h =>
        simp [h_valid] at h
        cases h
        exact .jump s dest rest h_dec h_gas h_stack h_valid
      | false, h => simp [h_valid] at h
    | [], h => nomatch h
  | JUMPI =>
    match h_stack : s.stack, h with
    | dest :: cond :: rest, h =>
      by_cases h_cond : cond.toNat = 0
      · -- cond = 0: not-taken branch
        simp [h_cond] at h
        cases h
        apply StepRunning.jumpi_notTaken s dest cond rest h_dec h_gas h_stack
        intro hh; exact hh h_cond
      · -- cond ≠ 0: taken-or-bad-jump branch
        simp [h_cond] at h
        match h_valid : Decode.isValidJumpDest s.executionEnv.code dest.toNat, h with
        | true, h =>
          simp at h
          cases h
          exact .jumpi_taken s dest cond rest h_dec h_gas h_stack h_cond h_valid
        | false, h => simp at h
    | [], h => nomatch h
    | [_], h => nomatch h
  | PC       => cases h; exact .pc s h_dec h_gas
  | JUMPDEST => cases h; exact .jumpdest s h_dec h_gas
  | MSIZE    => cases h; exact .msize s h_dec h_gas
  | GAS      => cases h; exact .gas s h_dec h_gas
  | TLOAD =>
    match h_stack : s.stack, h with
    | key :: rest, h => cases h; exact .tload s key rest h_dec h_gas h_stack
    | [], h         => nomatch h
  | TSTORE =>
    by_cases h_perm : ¬ s.executionEnv.permitStateMutation
    · simp [h_perm] at h
      unfold static at h; cases h
    · simp [h_perm] at h
      match h_stack : s.stack, h with
      | key :: value :: rest, h =>
        cases h
        exact .tstore s key value rest h_dec
                (by simp at h_perm; exact h_perm) h_gas h_stack
      | [], h     => nomatch h
      | [_], h    => nomatch h
  | MCOPY =>
    match h_stack : s.stack, h with
    | dOff :: sOff :: sz :: rest, h =>
      unfold chargeMem2 at h
      by_cases h_mem :
          (s.consumeGas (Gas.baseCost s.fork (.StackMemFlow .MCOPY)) h_gas).canExpandMemory2
            dOff.toNat sz.toNat sOff.toNat sz.toNat
      · simp [h_mem] at h
        by_cases h_dyn : Gas.copyWordCost sz ≤
            ((s.consumeGas (Gas.baseCost s.fork (.StackMemFlow .MCOPY)) h_gas).consumeMemExp2
                dOff.toNat sz.toNat sOff.toNat sz.toNat h_mem).gasAvailable
        · simp [h_dyn] at h
          cases h
          exact .mcopy s dOff sOff sz rest h_dec h_gas h_stack h_mem h_dyn
        · simp [h_dyn] at h
      · simp [h_mem] at h
    | [], h     => nomatch h
    | [_], h    => nomatch h
    | [_, _], h => nomatch h

theorem push_sound (s : State) (op : Operation.PushOp) (argOpt : Option (UInt256 × Nat))
    (h_dec : s.decoded = some (.Push op, argOpt))
    (h_gas : Gas.baseCost s.fork (.Push op) ≤ s.gasAvailable)
    {sf : State}
    (h : stepF.push s
           (s.consumeGas (Gas.baseCost s.fork (.Push op)) h_gas) op argOpt = .ok sf) :
    StepRunning s sf := by
  unfold stepF.push at h
  -- Destructure op into its width Fin field.
  obtain ⟨⟨w, hw⟩⟩ := op
  -- Case-split on the width's Nat value; we include `h_gas` in the match so
  -- its type gets refined alongside the pattern (the dependent gas cost
  -- differs between `Push ⟨0,_⟩` and `Push ⟨_+1,_⟩`).
  match w, hw, h_dec, h_gas, h with
  | 0, _, h_dec, h_gas, h =>
    -- PUSH0 case: stepF returns .ok (push 0). argOpt is unused.
    simp at h
    cases h
    exact StepRunning.push0 s (State.decoded_to_op h_dec) h_gas
  | k+1, hw, h_dec, h_gas, h =>
    -- PUSHk case: width is k+1, argOpt determines whether we succeed.
    match h_arg : argOpt, h with
    | some (d, n), h =>
      simp at h
      cases h
      exact StepRunning.pushN s ⟨k+1, hw⟩ d n (Nat.succ_pos k) h_dec h_gas
    | none, h => simp at h

theorem log_sound (s : State) (op : Operation.LogOp)
    (h_dec : s.decodedOp = some (.Log op))
    (h_gas : Gas.baseCost s.fork (.Log op) ≤ s.gasAvailable)
    {sf : State}
    (h : stepF.log s (s.consumeGas (Gas.baseCost s.fork (.Log op)) h_gas) op = .ok sf) :
    StepRunning s sf := by
  unfold stepF.log at h
  by_cases h_perm : ¬ s.executionEnv.permitStateMutation
  · simp [h_perm] at h
    unfold static at h
    cases h
  · simp [h_perm] at h
    match h_stack : s.stack, h with
    | offset :: size :: rest, h =>
      unfold chargeMem at h
      by_cases h_mem :
          (s.consumeGas (Gas.baseCost s.fork (.Log op)) h_gas).canExpandMemory
                         offset.toNat size.toNat
      · simp [h_mem] at h
        by_cases h_dyn : Gas.logDataCost size ≤
            ((s.consumeGas (Gas.baseCost s.fork (.Log op))
                            h_gas).consumeMemExp offset.toNat size.toNat h_mem).gasAvailable
        · simp [h_dyn] at h
          cases h_pop : stepF.popN rest op.topics.val with
          | some p =>
            obtain ⟨topics, rest'⟩ := p
            simp [h_pop] at h
            cases h
            obtain ⟨n⟩ := op
            have ⟨h_len, h_split⟩ := stepF.popN_correct rest n.val topics rest' h_pop
            have h_perm' : s.executionEnv.permitStateMutation = true := by
              simp at h_perm; exact h_perm
            have h_stack' : s.stack = offset :: size :: topics ++ rest' := by
              rw [h_stack, h_split]; rfl
            exact StepRunning.log s n offset size topics rest' h_dec h_perm'
                           h_gas h_len h_stack' h_mem h_dyn
          | none =>
            simp [h_pop] at h
            unfold underflow at h
            cases h
        · simp [h_dyn] at h
      · simp [h_mem] at h
    | [], h     => nomatch h
    | [_], h    => nomatch h

end stepF

----------------------------------------------------------------------------
-- The headline theorem: assembled from the helper-soundness lemmas above.
-- Every `Operation` top-level constructor dispatches to its `*_sound`
-- companion. The outer halt / decode / gas branches that don't reach
-- a helper contradict `h : … = .ok s'` directly.
----------------------------------------------------------------------------

/-- Soundness of `stepF`'s resume path: resuming a halted active frame that
    still has suspended callers produces a `StepReturn` (one of the
    `callReturn*` rules). The `.Running` arm of `resumeByHalt` is excluded
    by `h_nr`. `stepF_sound` wraps the result with `Step.returning`. -/
theorem resume_sound (s : State) (f : Frame) (rest : List Frame)
    (h_nr : s.halt ≠ .Running) (h_stack : s.callStack = f :: rest) :
    StepReturn s (s.resumeByHalt f rest) := by
  unfold State.resumeByHalt
  split
  · exact absurd ‹s.halt = .Running› h_nr
  · exact .callReturnSuccess s f rest (Or.inl ‹_›) h_stack
  · exact .callReturnSuccess s f rest (Or.inr ‹_›) h_stack
  · exact .callReturnRevert s f rest ‹_› h_stack
  · exact .callReturnException s f rest _ ‹_› h_stack

/-- **Soundness of the executable shadow.** Every `.ok` outcome of `stepF`
    corresponds to a derivation of the relational small-step `Step`.

    The outer dispatch (halt → decode → gas → operation) is unfolded by
    `split at h`. The boring branches (already-halted source, decode
    failure, gas-check failure) all contradict `h : … = .ok s'`. The
    interesting branches dispatch to the 14 per-helper soundness lemmas
    proven above (wrapped with `Step.running h_running`) plus the resume
    path via `resume_sound` (wrapped with `Step.returning`). The
    `h_running` hypothesis is consumed exactly once here, at the
    `Step.running` wrap site — not threaded through the ninety
    `StepRunning` constructors. -/
theorem stepF_sound (s s' : State) (h : stepF s = .ok s') : Step s s' := by
  unfold stepF at h
  simp only [Id.run] at h
  -- Split on s.halt.
  split at h
  · -- s.halt = .Running
    rename_i h_running
    -- Split on s.decoded.
    split at h
    · -- decoded = none
      nomatch h
    · -- decoded = some (op, argOpt)
      rename_i op argOpt h_dec
      -- Split on the gas check.
      split at h
      · -- gas ≥ cost
        rename_i h_gas
        -- Split on the operation kind.
        cases op with
        | StopArith op =>
          exact .running h_running (stepF.stopArith_sound s op (State.decoded_to_op h_dec) h_gas h)
        | CompBit op =>
          exact .running h_running (stepF.compBit_sound s op (State.decoded_to_op h_dec) h_gas h)
        | Keccak op =>
          exact .running h_running (stepF.keccak_sound s op (State.decoded_to_op h_dec) h_gas h)
        | Env op =>
          exact .running h_running (stepF.env_sound s op (State.decoded_to_op h_dec) h_gas h)
        | Block op =>
          exact .running h_running (stepF.block_sound s op (State.decoded_to_op h_dec) h_gas h)
        | StackMemFlow op =>
          exact .running h_running
            (stepF.stackMemFlow_sound s op (State.decoded_to_op h_dec) h_gas h)
        | Push op =>
          exact .running h_running (stepF.push_sound s op argOpt h_dec h_gas h)
        | Dup op =>
          exact .running h_running (stepF.dup_sound s op (State.decoded_to_op h_dec) h_gas h)
        | Swap op =>
          exact .running h_running (stepF.swap_sound s op (State.decoded_to_op h_dec) h_gas h)
        | DupN op =>
          exact .running h_running (stepF.dupN_sound s op (State.decoded_to_op h_dec) h_gas h)
        | SwapN op =>
          exact .running h_running (stepF.swapN_sound s op (State.decoded_to_op h_dec) h_gas h)
        | Exchange op =>
          exact .running h_running (stepF.exchange_sound s op (State.decoded_to_op h_dec) h_gas h)
        | Log op =>
          exact .running h_running (stepF.log_sound s op (State.decoded_to_op h_dec) h_gas h)
        | System op =>
          exact .running h_running (stepF.system_sound s op (State.decoded_to_op h_dec) h_gas h)
      · -- gas < cost
        nomatch h
  -- Non-Running halts: `stepF` either reports `.error` (empty call stack —
  -- the execution is done) or resumes the top caller (`.ok`, via the
  -- `callReturn*` rules). Discharge both for each halt kind.
  all_goals
    split at h
    · nomatch h
    · rename_i f rest h_cs
      injection h with h_eq
      subst h_eq
      exact .returning (resume_sound s f rest (by simp_all) h_cs)

end EVM
end EvmSemantics
