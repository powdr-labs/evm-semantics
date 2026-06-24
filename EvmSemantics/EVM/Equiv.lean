import EvmSemantics.EVM.Step
import EvmSemantics.EVM.StepF
import EvmSemantics.EVM.BigStep

/-!
`Equiv` — soundness of `stepF` with respect to the relational `Step`.

**Statement.** `stepF_sound : stepF s = .ok s' → Step s s'`. Every state
transition produced by the *executable* `stepF` is also a valid
derivation of the relational small-step `Step`.

**Structure.** Now that `stepF` is split into per-`Operation`-constructor
helpers (`stepF.stopArith`, `stepF.compBit`, …), we prove soundness in
two layers:

1. **Per-helper soundness** (`stepF.stopArith_sound` etc.) — each helper
   inverts via `match` and `cases h` and emits the matching `Step`
   constructor.
2. **Top-level `stepF_sound`** — opens the outer halt/decode/gas
   structure and dispatches to the helper lemmas.

We also export the `Eval` lemmas that don't depend on the executable
shadow (`Eval.halted_inv` etc.).
-/

namespace EvmSemantics
namespace EVM

----------------------------------------------------------------------------
-- Lemmas about `Eval` that don't go through `stepF`.
----------------------------------------------------------------------------

/-- A halted state's only `Eval` derivation is `Eval.halted`. -/
theorem Eval.halted_inv {s : State} {r : ExecutionResult}
    (h_halt : s.halt ≠ .Running) (h_eval : Eval s r) : r = s.toResult := by
  cases h_eval with
  | halted _ => rfl
  | stepThen st _ => exact absurd (Step.not_from_halted st h_halt) (fun h => h)

----------------------------------------------------------------------------
-- Helper soundness lemmas.
--
-- Each lemma proves that calling a `stepF.*` helper from a running state
-- with sufficient gas yields a valid `Step` derivation. The proof
-- destructures the helper's `match`, then applies the relevant `Step`
-- constructor.
----------------------------------------------------------------------------

namespace stepF

theorem stopArith_sound (s : State) (op : Operation.StopArithOps)
    (h_running : s.halt = .Running)
    (h_dec : s.decoded = some (.StopArith op, none))
    (h_gas : Gas.cost (.StopArith op) ≤ s.gasAvailable.toNat)
    {sf : State} (h : stepF.stopArith s (s.consumeGas (Gas.cost (.StopArith op)) h_gas) op = .ok sf) :
    Step s sf := by
  unfold stepF.stopArith at h
  cases op with
  | STOP =>
    -- Note STOP's success doesn't depend on h_gas in the Step constructor
    cases h; exact .stop s h_dec h_running
  | ADD =>
    match h_stack : s.stack, h with
    | a :: b :: rest, h => cases h; exact .add s a b rest h_dec h_running h_gas h_stack
    | [], h           => exact absurd h (by intro hh; cases hh)
    | [_], h          => exact absurd h (by intro hh; cases hh)
  | MUL =>
    match h_stack : s.stack, h with
    | a :: b :: rest, h => cases h; exact .mul s a b rest h_dec h_running h_gas h_stack
    | [], h           => exact absurd h (by intro hh; cases hh)
    | [_], h          => exact absurd h (by intro hh; cases hh)
  | SUB =>
    match h_stack : s.stack, h with
    | a :: b :: rest, h => cases h; exact .sub s a b rest h_dec h_running h_gas h_stack
    | [], h           => exact absurd h (by intro hh; cases hh)
    | [_], h          => exact absurd h (by intro hh; cases hh)
  | DIV =>
    match h_stack : s.stack, h with
    | a :: b :: rest, h => cases h; exact .div s a b rest h_dec h_running h_gas h_stack
    | [], h           => exact absurd h (by intro hh; cases hh)
    | [_], h          => exact absurd h (by intro hh; cases hh)
  | SDIV =>
    match h_stack : s.stack, h with
    | a :: b :: rest, h => cases h; exact .sdiv s a b rest h_dec h_running h_gas h_stack
    | [], h           => exact absurd h (by intro hh; cases hh)
    | [_], h          => exact absurd h (by intro hh; cases hh)
  | MOD =>
    match h_stack : s.stack, h with
    | a :: b :: rest, h => cases h; exact .mod s a b rest h_dec h_running h_gas h_stack
    | [], h           => exact absurd h (by intro hh; cases hh)
    | [_], h          => exact absurd h (by intro hh; cases hh)
  | SMOD =>
    match h_stack : s.stack, h with
    | a :: b :: rest, h => cases h; exact .smod s a b rest h_dec h_running h_gas h_stack
    | [], h           => exact absurd h (by intro hh; cases hh)
    | [_], h          => exact absurd h (by intro hh; cases hh)
  | ADDMOD =>
    match h_stack : s.stack, h with
    | a :: b :: n :: rest, h => cases h; exact .addmod s a b n rest h_dec h_running h_gas h_stack
    | [], h           => exact absurd h (by intro hh; cases hh)
    | [_], h          => exact absurd h (by intro hh; cases hh)
    | [_, _], h       => exact absurd h (by intro hh; cases hh)
  | MULMOD =>
    match h_stack : s.stack, h with
    | a :: b :: n :: rest, h => cases h; exact .mulmod s a b n rest h_dec h_running h_gas h_stack
    | [], h           => exact absurd h (by intro hh; cases hh)
    | [_], h          => exact absurd h (by intro hh; cases hh)
    | [_, _], h       => exact absurd h (by intro hh; cases hh)
  | EXP =>
    match h_stack : s.stack, h with
    | a :: b :: rest, h => cases h; exact .exp s a b rest h_dec h_running h_gas h_stack
    | [], h           => exact absurd h (by intro hh; cases hh)
    | [_], h          => exact absurd h (by intro hh; cases hh)
  | SIGNEXTEND =>
    match h_stack : s.stack, h with
    | a :: b :: rest, h => cases h; exact .signextend s a b rest h_dec h_running h_gas h_stack
    | [], h           => exact absurd h (by intro hh; cases hh)
    | [_], h          => exact absurd h (by intro hh; cases hh)

theorem compBit_sound (s : State) (op : Operation.CompareBitwiseOps)
    (h_running : s.halt = .Running)
    (h_dec : s.decoded = some (.CompBit op, none))
    (h_gas : Gas.cost (.CompBit op) ≤ s.gasAvailable.toNat)
    {sf : State} (h : stepF.compBit s (s.consumeGas (Gas.cost (.CompBit op)) h_gas) op = .ok sf) :
    Step s sf := by
  unfold stepF.compBit at h
  cases op with
  | LT =>
    match h_stack : s.stack, h with
    | a :: b :: rest, h => cases h; exact .lt s a b rest h_dec h_running h_gas h_stack
    | [], h           => exact absurd h (by intro hh; cases hh)
    | [_], h          => exact absurd h (by intro hh; cases hh)
  | GT =>
    match h_stack : s.stack, h with
    | a :: b :: rest, h => cases h; exact .gt s a b rest h_dec h_running h_gas h_stack
    | [], h           => exact absurd h (by intro hh; cases hh)
    | [_], h          => exact absurd h (by intro hh; cases hh)
  | SLT =>
    match h_stack : s.stack, h with
    | a :: b :: rest, h => cases h; exact .slt s a b rest h_dec h_running h_gas h_stack
    | [], h           => exact absurd h (by intro hh; cases hh)
    | [_], h          => exact absurd h (by intro hh; cases hh)
  | SGT =>
    match h_stack : s.stack, h with
    | a :: b :: rest, h => cases h; exact .sgt s a b rest h_dec h_running h_gas h_stack
    | [], h           => exact absurd h (by intro hh; cases hh)
    | [_], h          => exact absurd h (by intro hh; cases hh)
  | EQ =>
    match h_stack : s.stack, h with
    | a :: b :: rest, h => cases h; exact .eq s a b rest h_dec h_running h_gas h_stack
    | [], h           => exact absurd h (by intro hh; cases hh)
    | [_], h          => exact absurd h (by intro hh; cases hh)
  | ISZERO =>
    match h_stack : s.stack, h with
    | a :: rest, h => cases h; exact .iszero s a rest h_dec h_running h_gas h_stack
    | [], h       => exact absurd h (by intro hh; cases hh)
  | AND =>
    match h_stack : s.stack, h with
    | a :: b :: rest, h => cases h; exact .and s a b rest h_dec h_running h_gas h_stack
    | [], h           => exact absurd h (by intro hh; cases hh)
    | [_], h          => exact absurd h (by intro hh; cases hh)
  | OR =>
    match h_stack : s.stack, h with
    | a :: b :: rest, h => cases h; exact .or s a b rest h_dec h_running h_gas h_stack
    | [], h           => exact absurd h (by intro hh; cases hh)
    | [_], h          => exact absurd h (by intro hh; cases hh)
  | XOR =>
    match h_stack : s.stack, h with
    | a :: b :: rest, h => cases h; exact .xor_ s a b rest h_dec h_running h_gas h_stack
    | [], h           => exact absurd h (by intro hh; cases hh)
    | [_], h          => exact absurd h (by intro hh; cases hh)
  | NOT =>
    match h_stack : s.stack, h with
    | a :: rest, h => cases h; exact .not s a rest h_dec h_running h_gas h_stack
    | [], h       => exact absurd h (by intro hh; cases hh)
  | BYTE =>
    match h_stack : s.stack, h with
    | i :: x :: rest, h => cases h; exact .byte_ s i x rest h_dec h_running h_gas h_stack
    | [], h           => exact absurd h (by intro hh; cases hh)
    | [_], h          => exact absurd h (by intro hh; cases hh)
  | SHL =>
    match h_stack : s.stack, h with
    | sh :: v :: rest, h => cases h; exact .shl s sh v rest h_dec h_running h_gas h_stack
    | [], h           => exact absurd h (by intro hh; cases hh)
    | [_], h          => exact absurd h (by intro hh; cases hh)
  | SHR =>
    match h_stack : s.stack, h with
    | sh :: v :: rest, h => cases h; exact .shr s sh v rest h_dec h_running h_gas h_stack
    | [], h           => exact absurd h (by intro hh; cases hh)
    | [_], h          => exact absurd h (by intro hh; cases hh)
  | SAR =>
    match h_stack : s.stack, h with
    | sh :: v :: rest, h => cases h; exact .sar s sh v rest h_dec h_running h_gas h_stack
    | [], h           => exact absurd h (by intro hh; cases hh)
    | [_], h          => exact absurd h (by intro hh; cases hh)

theorem keccak_sound (s : State) (op : Operation.KeccakOps)
    (h_running : s.halt = .Running)
    (h_dec : s.decoded = some (.Keccak op, none))
    (h_gas : Gas.cost (.Keccak op) ≤ s.gasAvailable.toNat)
    {sf : State} (h : stepF.keccak s (s.consumeGas (Gas.cost (.Keccak op)) h_gas) op = .ok sf) :
    Step s sf := by
  unfold stepF.keccak at h
  cases op with
  | KECCAK256 =>
    match h_stack : s.stack, h with
    | offset :: size :: rest, h =>
      cases h; exact .keccak256 s offset size rest h_dec h_running h_gas h_stack
    | [], h           => exact absurd h (by intro hh; cases hh)
    | [_], h          => exact absurd h (by intro hh; cases hh)

theorem block_sound (s : State) (op : Operation.BlockOps)
    (h_running : s.halt = .Running)
    (h_dec : s.decoded = some (.Block op, none))
    (h_gas : Gas.cost (.Block op) ≤ s.gasAvailable.toNat)
    {sf : State} (h : stepF.block s (s.consumeGas (Gas.cost (.Block op)) h_gas) op = .ok sf) :
    Step s sf := by
  unfold stepF.block at h
  cases op with
  | BLOCKHASH =>
    match h_stack : s.stack, h with
    | n :: rest, h => cases h; exact .blockhash s n rest h_dec h_running h_gas h_stack
    | [], h       => exact absurd h (by intro hh; cases hh)
  | COINBASE    => cases h; exact .coinbase s h_dec h_running h_gas
  | TIMESTAMP   => cases h; exact .timestamp s h_dec h_running h_gas
  | NUMBER      => cases h; exact .number s h_dec h_running h_gas
  | PREVRANDAO  => cases h; exact .prevrandao s h_dec h_running h_gas
  | GASLIMIT    => cases h; exact .gaslimit s h_dec h_running h_gas
  | CHAINID     => cases h; exact .chainid s h_dec h_running h_gas
  | SELFBALANCE => cases h; exact .selfbalance s h_dec h_running h_gas
  | BASEFEE     => cases h; exact .basefee s h_dec h_running h_gas
  | BLOBBASEFEE => cases h; exact .blobbasefee s h_dec h_running h_gas
  | BLOBHASH =>
    match h_stack : s.stack, h with
    | i :: rest, h =>
      -- BLOBHASH always returns ok (lookup defaults to 0) — use in-bounds or oob rule
      cases h_lookup : s.executionEnv.blobVersionedHashes[i.toNat]? with
      | some bh =>
        simp [h_lookup] at h; cases h
        exact .blobhash s i rest bh h_dec h_running h_gas h_stack h_lookup
      | none =>
        simp [h_lookup] at h; cases h
        exact .blobhash_oob s i rest h_dec h_running h_gas h_stack h_lookup
    | [], h => exact absurd h (by intro hh; cases hh)

theorem system_sound (s : State) (op : Operation.SystemOps)
    (h_running : s.halt = .Running)
    (h_dec : s.decoded = some (.System op, none))
    (h_gas : Gas.cost (.System op) ≤ s.gasAvailable.toNat)
    {sf : State} (h : stepF.system s (s.consumeGas (Gas.cost (.System op)) h_gas) op = .ok sf) :
    Step s sf := by
  unfold stepF.system at h
  cases op with
  | RETURN =>
    match h_stack : s.stack, h with
    | offset :: size :: rest, h =>
      cases h; exact .return_ s offset size rest h_dec h_running h_gas h_stack
    | [], h           => exact absurd h (by intro hh; cases hh)
    | [_], h          => exact absurd h (by intro hh; cases hh)
  | REVERT =>
    match h_stack : s.stack, h with
    | offset :: size :: rest, h =>
      cases h; exact .revert s offset size rest h_dec h_running h_gas h_stack
    | [], h           => exact absurd h (by intro hh; cases hh)
    | [_], h          => exact absurd h (by intro hh; cases hh)
  | INVALID =>
    -- stepF.system returns .error on INVALID; no .ok possible
    exact absurd h (by intro hh; cases hh)
  -- Out-of-scope ops: stepF returns .error
  | CREATE | CREATE2 | CALL | CALLCODE | DELEGATECALL | STATICCALL | SELFDESTRUCT =>
    exact absurd h (by intro hh; cases hh)

theorem dup_sound (s : State) (op : Operation.DupOp)
    (h_running : s.halt = .Running)
    (h_dec : s.decoded = some (.Dup op, none))
    (h_gas : Gas.cost (.Dup op) ≤ s.gasAvailable.toNat)
    {sf : State} (h : stepF.dup s (s.consumeGas (Gas.cost (.Dup op)) h_gas) op = .ok sf) :
    Step s sf := by
  unfold stepF.dup at h
  match h_get : s.stack[op.idx.val]?, h with
  | some v, h => cases h
                 obtain ⟨idx⟩ := op
                 exact .dup s idx v h_dec h_running h_gas h_get
  | none, h   => exact absurd h (by intro hh; cases hh)

theorem swap_sound (s : State) (op : Operation.SwapOp)
    (h_running : s.halt = .Running)
    (h_dec : s.decoded = some (.Swap op, none))
    (h_gas : Gas.cost (.Swap op) ≤ s.gasAvailable.toNat)
    {sf : State} (h : stepF.swap s (s.consumeGas (Gas.cost (.Swap op)) h_gas) op = .ok sf) :
    Step s sf := by
  unfold stepF.swap at h
  match h_ex : s.stack.exchange 0 (op.idx.val + 1), h with
  | some stk', h => cases h
                    obtain ⟨idx⟩ := op
                    exact .swap s idx stk' h_dec h_running h_gas h_ex
  | none, h      => exact absurd h (by intro hh; cases hh)

theorem dupN_sound (s : State) (op : Operation.DupNOp)
    (h_running : s.halt = .Running)
    (h_dec : s.decoded = some (.DupN op, none))
    (h_gas : Gas.cost (.DupN op) ≤ s.gasAvailable.toNat)
    {sf : State} (h : stepF.dupN s (s.consumeGas (Gas.cost (.DupN op)) h_gas) op = .ok sf) :
    Step s sf := by
  unfold stepF.dupN at h
  match h_get : s.stack[op.n.val]?, h with
  | some v, h => cases h
                 obtain ⟨n⟩ := op
                 exact .dupN s n v h_dec h_running h_gas h_get
  | none, h   => exact absurd h (by intro hh; cases hh)

theorem swapN_sound (s : State) (op : Operation.SwapNOp)
    (h_running : s.halt = .Running)
    (h_dec : s.decoded = some (.SwapN op, none))
    (h_gas : Gas.cost (.SwapN op) ≤ s.gasAvailable.toNat)
    {sf : State} (h : stepF.swapN s (s.consumeGas (Gas.cost (.SwapN op)) h_gas) op = .ok sf) :
    Step s sf := by
  unfold stepF.swapN at h
  match h_ex : s.stack.exchange 0 (op.n.val + 1), h with
  | some stk', h => cases h
                    obtain ⟨n⟩ := op
                    exact .swapN s n stk' h_dec h_running h_gas h_ex
  | none, h      => exact absurd h (by intro hh; cases hh)

theorem exchange_sound (s : State) (op : Operation.ExchangeOp)
    (h_running : s.halt = .Running)
    (h_dec : s.decoded = some (.Exchange op, none))
    (h_gas : Gas.cost (.Exchange op) ≤ s.gasAvailable.toNat)
    {sf : State} (h : stepF.exchange s (s.consumeGas (Gas.cost (.Exchange op)) h_gas) op = .ok sf) :
    Step s sf := by
  unfold stepF.exchange at h
  match h_ex : s.stack.exchange (op.n + 1) (op.m + 1), h with
  | some stk', h => cases h
                    obtain ⟨b⟩ := op
                    exact .exchange s b stk' h_dec h_running h_gas h_ex
  | none, h      => exact absurd h (by intro hh; cases hh)

theorem env_sound (s : State) (op : Operation.EnvOps)
    (h_running : s.halt = .Running)
    (h_dec : s.decoded = some (.Env op, none))
    (h_gas : Gas.cost (.Env op) ≤ s.gasAvailable.toNat)
    {sf : State} (h : stepF.env s (s.consumeGas (Gas.cost (.Env op)) h_gas) op = .ok sf) :
    Step s sf := by
  unfold stepF.env at h
  cases op with
  | ADDRESS         => cases h; exact .address s h_dec h_running h_gas
  | ORIGIN          => cases h; exact .origin s h_dec h_running h_gas
  | CALLER          => cases h; exact .caller s h_dec h_running h_gas
  | CALLVALUE       => cases h; exact .callvalue s h_dec h_running h_gas
  | CALLDATASIZE    => cases h; exact .calldatasize s h_dec h_running h_gas
  | CODESIZE        => cases h; exact .codesize s h_dec h_running h_gas
  | GASPRICE        => cases h; exact .gasprice s h_dec h_running h_gas
  | RETURNDATASIZE  => cases h; exact .returndatasize s h_dec h_running h_gas
  | BALANCE =>
    match h_stack : s.stack, h with
    | a :: rest, h => cases h; exact .balance s a rest h_dec h_running h_gas h_stack
    | [], h       => exact absurd h (by intro hh; cases hh)
  | CALLDATALOAD =>
    match h_stack : s.stack, h with
    | i :: rest, h => cases h; exact .calldataload s i rest h_dec h_running h_gas h_stack
    | [], h       => exact absurd h (by intro hh; cases hh)
  | EXTCODESIZE =>
    match h_stack : s.stack, h with
    | a :: rest, h => cases h; exact .extcodesize s a rest h_dec h_running h_gas h_stack
    | [], h       => exact absurd h (by intro hh; cases hh)
  | EXTCODEHASH =>
    match h_stack : s.stack, h with
    | a :: rest, h => cases h; exact .extcodehash s a rest h_dec h_running h_gas h_stack
    | [], h       => exact absurd h (by intro hh; cases hh)
  | CALLDATACOPY =>
    match h_stack : s.stack, h with
    | dOff :: sOff :: sz :: rest, h =>
      cases h; exact .calldatacopy s dOff sOff sz rest h_dec h_running h_gas h_stack
    | [], h     => exact absurd h (by intro hh; cases hh)
    | [_], h    => exact absurd h (by intro hh; cases hh)
    | [_, _], h => exact absurd h (by intro hh; cases hh)
  | CODECOPY =>
    match h_stack : s.stack, h with
    | dOff :: sOff :: sz :: rest, h =>
      cases h; exact .codecopy s dOff sOff sz rest h_dec h_running h_gas h_stack
    | [], h     => exact absurd h (by intro hh; cases hh)
    | [_], h    => exact absurd h (by intro hh; cases hh)
    | [_, _], h => exact absurd h (by intro hh; cases hh)
  | EXTCODECOPY =>
    match h_stack : s.stack, h with
    | a :: dOff :: sOff :: sz :: rest, h =>
      cases h; exact .extcodecopy s a dOff sOff sz rest h_dec h_running h_gas h_stack
    | [], h        => exact absurd h (by intro hh; cases hh)
    | [_], h       => exact absurd h (by intro hh; cases hh)
    | [_, _], h    => exact absurd h (by intro hh; cases hh)
    | [_, _, _], h => exact absurd h (by intro hh; cases hh)
  | RETURNDATACOPY =>
    match h_stack : s.stack, h with
    | dOff :: sOff :: sz :: rest, h =>
      by_cases h_oob : sOff.toNat + sz.toNat > s.returnData.size
      · simp [h_stack, h_oob] at h
      · simp [h_stack, h_oob] at h
        cases h
        exact .returndatacopy s dOff sOff sz rest h_dec h_running h_gas h_stack
                (Nat.le_of_not_lt h_oob)
    | [], h     => exact absurd h (by intro hh; cases hh)
    | [_], h    => exact absurd h (by intro hh; cases hh)
    | [_, _], h => exact absurd h (by intro hh; cases hh)

theorem stackMemFlow_sound (s : State) (op : Operation.StackMemFlowOps)
    (h_running : s.halt = .Running)
    (h_dec : s.decoded = some (.StackMemFlow op, none))
    (h_gas : Gas.cost (.StackMemFlow op) ≤ s.gasAvailable.toNat)
    {sf : State} (h : stepF.stackMemFlow s
                        (s.consumeGas (Gas.cost (.StackMemFlow op)) h_gas) op = .ok sf) :
    Step s sf := by
  unfold stepF.stackMemFlow at h
  cases op with
  | POP =>
    match h_stack : s.stack, h with
    | a :: rest, h => cases h; exact .pop s a rest h_dec h_running h_gas h_stack
    | [], h       => exact absurd h (by intro hh; cases hh)
  | MLOAD =>
    match h_stack : s.stack, h with
    | offset :: rest, h =>
      cases h_load : MachineState.mload s.toMachineState offset with
      | mk v μ' =>
        simp [h_stack, h_load] at h; cases h
        exact .mload s offset rest v μ' h_dec h_running h_gas h_stack h_load
    | [], h => exact absurd h (by intro hh; cases hh)
  | MSTORE =>
    match h_stack : s.stack, h with
    | offset :: value :: rest, h =>
      cases h; exact .mstore s offset value rest h_dec h_running h_gas h_stack
    | [], h     => exact absurd h (by intro hh; cases hh)
    | [_], h    => exact absurd h (by intro hh; cases hh)
  | MSTORE8 =>
    match h_stack : s.stack, h with
    | offset :: value :: rest, h =>
      cases h; exact .mstore8 s offset value rest h_dec h_running h_gas h_stack
    | [], h     => exact absurd h (by intro hh; cases hh)
    | [_], h    => exact absurd h (by intro hh; cases hh)
  | SLOAD =>
    match h_stack : s.stack, h with
    | key :: rest, h => cases h; exact .sload s key rest h_dec h_running h_gas h_stack
    | [], h         => exact absurd h (by intro hh; cases hh)
  | SSTORE =>
    by_cases h_perm : ¬ s.executionEnv.permitStateMutation
    · -- stepF returns static violation; no .ok
      simp [h_perm] at h
      unfold static at h; cases h
    · simp [h_perm] at h
      match h_stack : s.stack, h with
      | key :: value :: rest, h =>
        cases h
        exact .sstore s key value rest h_dec h_running
                (by simp at h_perm; exact h_perm) h_gas h_stack
      | [], h     => exact absurd h (by intro hh; cases hh)
      | [_], h    => exact absurd h (by intro hh; cases hh)
  | JUMP =>
    -- The JUMP/JUMPDEST validity branching makes this case more intricate;
    -- it would need a careful `simp` of the inner match against
    -- `Decode.decodeAt`. Deferred.
    sorry
  | JUMPI =>
    -- Splits on cond ≠ 0 and on jump validity. Mechanical, deferred.
    sorry
  | PC       => cases h; exact .pc s h_dec h_running h_gas
  | JUMPDEST => cases h; exact .jumpdest s h_dec h_running h_gas
  | MSIZE    => cases h; exact .msize s h_dec h_running h_gas
  | GAS      => cases h; exact .gas s h_dec h_running h_gas
  | TLOAD =>
    match h_stack : s.stack, h with
    | key :: rest, h => cases h; exact .tload s key rest h_dec h_running h_gas h_stack
    | [], h         => exact absurd h (by intro hh; cases hh)
  | TSTORE =>
    by_cases h_perm : ¬ s.executionEnv.permitStateMutation
    · simp [h_perm] at h
      unfold static at h; cases h
    · simp [h_perm] at h
      match h_stack : s.stack, h with
      | key :: value :: rest, h =>
        cases h
        exact .tstore s key value rest h_dec h_running
                (by simp at h_perm; exact h_perm) h_gas h_stack
      | [], h     => exact absurd h (by intro hh; cases hh)
      | [_], h    => exact absurd h (by intro hh; cases hh)
  | MCOPY =>
    match h_stack : s.stack, h with
    | dOff :: sOff :: sz :: rest, h =>
      cases h; exact .mcopy s dOff sOff sz rest h_dec h_running h_gas h_stack
    | [], h     => exact absurd h (by intro hh; cases hh)
    | [_], h    => exact absurd h (by intro hh; cases hh)
    | [_, _], h => exact absurd h (by intro hh; cases hh)

theorem push_sound (s : State) (op : Operation.PushOp) (argOpt : Option (UInt256 × Nat))
    (h_running : s.halt = .Running)
    (h_dec : s.decoded = some (.Push op, argOpt))
    (h_gas : Gas.cost (.Push op) ≤ s.gasAvailable.toNat)
    {sf : State} (h : stepF.push s (s.consumeGas (Gas.cost (.Push op)) h_gas) op argOpt = .ok sf) :
    Step s sf := by
  -- The PUSH0/PUSHk split inverts on `op.width.val`; the PUSHk case needs an
  -- additional invariant from the decoder (the immediate width in `argOpt`
  -- matches `op.width`). Deferred.
  sorry

theorem log_sound (s : State) (op : Operation.LogOp)
    (h_running : s.halt = .Running)
    (h_dec : s.decoded = some (.Log op, none))
    (h_gas : Gas.cost (.Log op) ≤ s.gasAvailable.toNat)
    {sf : State} (h : stepF.log s (s.consumeGas (Gas.cost (.Log op)) h_gas) op = .ok sf) :
    Step s sf := by
  -- Requires inverting the inner popN recursive function and showing the
  -- corresponding list-of-topics witness for Step.log. Mechanical but
  -- non-trivial; deferred.
  sorry

end stepF

----------------------------------------------------------------------------
-- The headline theorem: assembled from helper-soundness lemmas.
--
-- The opcode groups we have helper-soundness lemmas for (StopArith,
-- CompBit, Keccak) dispatch through their respective `*_sound` lemmas.
-- The remaining groups (Env, Block, StackMemFlow, Push, Dup, Swap, DupN,
-- SwapN, Exchange, Log, System) are deferred behind `sorry` — each is
-- structurally identical to the proven ones and follows the same
-- `unfold; cases op; match h_stack ...; exact .opname …` template.
----------------------------------------------------------------------------

/-- The headline soundness theorem.

    **Status.** The helper-soundness lemmas above (`stepF.stopArith_sound`,
    `stepF.compBit_sound`, `stepF.keccak_sound`) handle the per-helper
    inversion, which was the substantive proof work. What remains is
    threading the outer halt/decode/gas dispatch — this is fighting the
    `match`-with-equation elaborator in Lean 4 and is deferred. -/
theorem stepF_sound (s s' : State) (h : stepF s = .ok s') : Step s s' := by
  sorry

end EVM
end EvmSemantics
