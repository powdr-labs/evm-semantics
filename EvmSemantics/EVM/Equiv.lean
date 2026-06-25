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
    (argOpt : Option (UInt256 × Nat))
    (h_dec : s.decoded = some (.StopArith op, argOpt))
    (h_gas : Gas.cost (.StopArith op) ≤ s.gasAvailable)
    {sf : State} (h : stepF.stopArith s (s.consumeGas (Gas.cost (.StopArith op)) h_gas) op = .ok sf) :
    Step s sf := by
  unfold stepF.stopArith at h
  cases op with
  | STOP =>
    -- Note STOP's success doesn't depend on h_gas in the Step constructor
    cases h; exact .stop s argOpt h_dec h_running
  | ADD =>
    match h_stack : s.stack, h with
    | a :: b :: rest, h => cases h; exact .add s a b rest argOpt h_dec h_running h_gas h_stack
    | [], h           => exact absurd h (by intro hh; cases hh)
    | [_], h          => exact absurd h (by intro hh; cases hh)
  | MUL =>
    match h_stack : s.stack, h with
    | a :: b :: rest, h => cases h; exact .mul s a b rest argOpt h_dec h_running h_gas h_stack
    | [], h           => exact absurd h (by intro hh; cases hh)
    | [_], h          => exact absurd h (by intro hh; cases hh)
  | SUB =>
    match h_stack : s.stack, h with
    | a :: b :: rest, h => cases h; exact .sub s a b rest argOpt h_dec h_running h_gas h_stack
    | [], h           => exact absurd h (by intro hh; cases hh)
    | [_], h          => exact absurd h (by intro hh; cases hh)
  | DIV =>
    match h_stack : s.stack, h with
    | a :: b :: rest, h => cases h; exact .div s a b rest argOpt h_dec h_running h_gas h_stack
    | [], h           => exact absurd h (by intro hh; cases hh)
    | [_], h          => exact absurd h (by intro hh; cases hh)
  | SDIV =>
    match h_stack : s.stack, h with
    | a :: b :: rest, h => cases h; exact .sdiv s a b rest argOpt h_dec h_running h_gas h_stack
    | [], h           => exact absurd h (by intro hh; cases hh)
    | [_], h          => exact absurd h (by intro hh; cases hh)
  | MOD =>
    match h_stack : s.stack, h with
    | a :: b :: rest, h => cases h; exact .mod s a b rest argOpt h_dec h_running h_gas h_stack
    | [], h           => exact absurd h (by intro hh; cases hh)
    | [_], h          => exact absurd h (by intro hh; cases hh)
  | SMOD =>
    match h_stack : s.stack, h with
    | a :: b :: rest, h => cases h; exact .smod s a b rest argOpt h_dec h_running h_gas h_stack
    | [], h           => exact absurd h (by intro hh; cases hh)
    | [_], h          => exact absurd h (by intro hh; cases hh)
  | ADDMOD =>
    match h_stack : s.stack, h with
    | a :: b :: n :: rest, h => cases h; exact .addmod s a b n rest argOpt h_dec h_running h_gas h_stack
    | [], h           => exact absurd h (by intro hh; cases hh)
    | [_], h          => exact absurd h (by intro hh; cases hh)
    | [_, _], h       => exact absurd h (by intro hh; cases hh)
  | MULMOD =>
    match h_stack : s.stack, h with
    | a :: b :: n :: rest, h => cases h; exact .mulmod s a b n rest argOpt h_dec h_running h_gas h_stack
    | [], h           => exact absurd h (by intro hh; cases hh)
    | [_], h          => exact absurd h (by intro hh; cases hh)
    | [_, _], h       => exact absurd h (by intro hh; cases hh)
  | EXP =>
    match h_stack : s.stack, h with
    | a :: b :: rest, h =>
        cases h
        -- `stepF` uses the fast modular-exponentiation `expFast`; the relation
        -- `Step.exp` uses the `exp` specification. They agree (`expFast_eq_exp`).
        rw [UInt256.expFast_eq_exp]
        exact .exp s a b rest argOpt h_dec h_running h_gas h_stack
    | [], h           => exact absurd h (by intro hh; cases hh)
    | [_], h          => exact absurd h (by intro hh; cases hh)
  | SIGNEXTEND =>
    match h_stack : s.stack, h with
    | a :: b :: rest, h => cases h; exact .signextend s a b rest argOpt h_dec h_running h_gas h_stack
    | [], h           => exact absurd h (by intro hh; cases hh)
    | [_], h          => exact absurd h (by intro hh; cases hh)

theorem compBit_sound (s : State) (op : Operation.CompareBitwiseOps)
    (h_running : s.halt = .Running)
    (argOpt : Option (UInt256 × Nat))
    (h_dec : s.decoded = some (.CompBit op, argOpt))
    (h_gas : Gas.cost (.CompBit op) ≤ s.gasAvailable)
    {sf : State} (h : stepF.compBit s (s.consumeGas (Gas.cost (.CompBit op)) h_gas) op = .ok sf) :
    Step s sf := by
  unfold stepF.compBit at h
  cases op with
  | LT =>
    match h_stack : s.stack, h with
    | a :: b :: rest, h => cases h; exact .lt s a b rest argOpt h_dec h_running h_gas h_stack
    | [], h           => exact absurd h (by intro hh; cases hh)
    | [_], h          => exact absurd h (by intro hh; cases hh)
  | GT =>
    match h_stack : s.stack, h with
    | a :: b :: rest, h => cases h; exact .gt s a b rest argOpt h_dec h_running h_gas h_stack
    | [], h           => exact absurd h (by intro hh; cases hh)
    | [_], h          => exact absurd h (by intro hh; cases hh)
  | SLT =>
    match h_stack : s.stack, h with
    | a :: b :: rest, h => cases h; exact .slt s a b rest argOpt h_dec h_running h_gas h_stack
    | [], h           => exact absurd h (by intro hh; cases hh)
    | [_], h          => exact absurd h (by intro hh; cases hh)
  | SGT =>
    match h_stack : s.stack, h with
    | a :: b :: rest, h => cases h; exact .sgt s a b rest argOpt h_dec h_running h_gas h_stack
    | [], h           => exact absurd h (by intro hh; cases hh)
    | [_], h          => exact absurd h (by intro hh; cases hh)
  | EQ =>
    match h_stack : s.stack, h with
    | a :: b :: rest, h => cases h; exact .eq s a b rest argOpt h_dec h_running h_gas h_stack
    | [], h           => exact absurd h (by intro hh; cases hh)
    | [_], h          => exact absurd h (by intro hh; cases hh)
  | ISZERO =>
    match h_stack : s.stack, h with
    | a :: rest, h => cases h; exact .iszero s a rest argOpt h_dec h_running h_gas h_stack
    | [], h       => exact absurd h (by intro hh; cases hh)
  | AND =>
    match h_stack : s.stack, h with
    | a :: b :: rest, h => cases h; exact .and s a b rest argOpt h_dec h_running h_gas h_stack
    | [], h           => exact absurd h (by intro hh; cases hh)
    | [_], h          => exact absurd h (by intro hh; cases hh)
  | OR =>
    match h_stack : s.stack, h with
    | a :: b :: rest, h => cases h; exact .or s a b rest argOpt h_dec h_running h_gas h_stack
    | [], h           => exact absurd h (by intro hh; cases hh)
    | [_], h          => exact absurd h (by intro hh; cases hh)
  | XOR =>
    match h_stack : s.stack, h with
    | a :: b :: rest, h => cases h; exact .xor_ s a b rest argOpt h_dec h_running h_gas h_stack
    | [], h           => exact absurd h (by intro hh; cases hh)
    | [_], h          => exact absurd h (by intro hh; cases hh)
  | NOT =>
    match h_stack : s.stack, h with
    | a :: rest, h => cases h; exact .not s a rest argOpt h_dec h_running h_gas h_stack
    | [], h       => exact absurd h (by intro hh; cases hh)
  | BYTE =>
    match h_stack : s.stack, h with
    | i :: x :: rest, h => cases h; exact .byte_ s i x rest argOpt h_dec h_running h_gas h_stack
    | [], h           => exact absurd h (by intro hh; cases hh)
    | [_], h          => exact absurd h (by intro hh; cases hh)
  | SHL =>
    match h_stack : s.stack, h with
    | sh :: v :: rest, h => cases h; exact .shl s sh v rest argOpt h_dec h_running h_gas h_stack
    | [], h           => exact absurd h (by intro hh; cases hh)
    | [_], h          => exact absurd h (by intro hh; cases hh)
  | SHR =>
    match h_stack : s.stack, h with
    | sh :: v :: rest, h => cases h; exact .shr s sh v rest argOpt h_dec h_running h_gas h_stack
    | [], h           => exact absurd h (by intro hh; cases hh)
    | [_], h          => exact absurd h (by intro hh; cases hh)
  | SAR =>
    match h_stack : s.stack, h with
    | sh :: v :: rest, h => cases h; exact .sar s sh v rest argOpt h_dec h_running h_gas h_stack
    | [], h           => exact absurd h (by intro hh; cases hh)
    | [_], h          => exact absurd h (by intro hh; cases hh)

theorem keccak_sound (s : State) (op : Operation.KeccakOps)
    (h_running : s.halt = .Running)
    (argOpt : Option (UInt256 × Nat))
    (h_dec : s.decoded = some (.Keccak op, argOpt))
    (h_gas : Gas.cost (.Keccak op) ≤ s.gasAvailable)
    {sf : State} (h : stepF.keccak s (s.consumeGas (Gas.cost (.Keccak op)) h_gas) op = .ok sf) :
    Step s sf := by
  unfold stepF.keccak at h
  cases op with
  | KECCAK256 =>
    match h_stack : s.stack, h with
    | offset :: size :: rest, h =>
      unfold chargeMem at h
      by_cases h_mem : (s.consumeGas (Gas.cost (.Keccak .KECCAK256)) h_gas).canExpandMemory
                         offset.toNat size.toNat
      · simp [h_mem] at h
        cases h
        exact .keccak256 s offset size rest argOpt h_dec h_running h_gas h_stack h_mem
      · simp [h_mem] at h
    | [], h           => exact absurd h (by intro hh; cases hh)
    | [_], h          => exact absurd h (by intro hh; cases hh)

theorem block_sound (s : State) (op : Operation.BlockOps)
    (h_running : s.halt = .Running)
    (argOpt : Option (UInt256 × Nat))
    (h_dec : s.decoded = some (.Block op, argOpt))
    (h_gas : Gas.cost (.Block op) ≤ s.gasAvailable)
    {sf : State} (h : stepF.block s (s.consumeGas (Gas.cost (.Block op)) h_gas) op = .ok sf) :
    Step s sf := by
  unfold stepF.block at h
  cases op with
  | BLOCKHASH =>
    match h_stack : s.stack, h with
    | n :: rest, h => cases h; exact .blockhash s n rest argOpt h_dec h_running h_gas h_stack
    | [], h       => exact absurd h (by intro hh; cases hh)
  | COINBASE    => cases h; exact .coinbase s argOpt h_dec h_running h_gas
  | TIMESTAMP   => cases h; exact .timestamp s argOpt h_dec h_running h_gas
  | NUMBER      => cases h; exact .number s argOpt h_dec h_running h_gas
  | PREVRANDAO  => cases h; exact .prevrandao s argOpt h_dec h_running h_gas
  | GASLIMIT    => cases h; exact .gaslimit s argOpt h_dec h_running h_gas
  | CHAINID     => cases h; exact .chainid s argOpt h_dec h_running h_gas
  | SELFBALANCE => cases h; exact .selfbalance s argOpt h_dec h_running h_gas
  | BASEFEE     => cases h; exact .basefee s argOpt h_dec h_running h_gas
  | BLOBBASEFEE => cases h; exact .blobbasefee s argOpt h_dec h_running h_gas
  | BLOBHASH =>
    match h_stack : s.stack, h with
    | i :: rest, h =>
      -- BLOBHASH always returns ok (lookup defaults to 0) — use in-bounds or oob rule
      cases h_lookup : s.executionEnv.blobVersionedHashes[i.toNat]? with
      | some bh =>
        simp [h_lookup] at h; cases h
        exact .blobhash s i rest bh argOpt h_dec h_running h_gas h_stack h_lookup
      | none =>
        simp [h_lookup] at h; cases h
        exact .blobhash_oob s i rest argOpt h_dec h_running h_gas h_stack h_lookup
    | [], h => exact absurd h (by intro hh; cases hh)

theorem system_sound (s : State) (op : Operation.SystemOps)
    (h_running : s.halt = .Running)
    (argOpt : Option (UInt256 × Nat))
    (h_dec : s.decoded = some (.System op, argOpt))
    (h_gas : Gas.cost (.System op) ≤ s.gasAvailable)
    {sf : State} (h : stepF.system s (s.consumeGas (Gas.cost (.System op)) h_gas) op = .ok sf) :
    Step s sf := by
  unfold stepF.system at h
  cases op with
  | RETURN =>
    match h_stack : s.stack, h with
    | offset :: size :: rest, h =>
      unfold chargeMem at h
      by_cases h_mem : (s.consumeGas (Gas.cost (.System .RETURN)) h_gas).canExpandMemory
                         offset.toNat size.toNat
      · simp [h_mem] at h
        cases h
        exact .return_ s offset size rest argOpt h_dec h_running h_gas h_stack h_mem
      · simp [h_mem] at h
    | [], h           => exact absurd h (by intro hh; cases hh)
    | [_], h          => exact absurd h (by intro hh; cases hh)
  | REVERT =>
    match h_stack : s.stack, h with
    | offset :: size :: rest, h =>
      unfold chargeMem at h
      by_cases h_mem : (s.consumeGas (Gas.cost (.System .REVERT)) h_gas).canExpandMemory
                         offset.toNat size.toNat
      · simp [h_mem] at h
        cases h
        exact .revert s offset size rest argOpt h_dec h_running h_gas h_stack h_mem
      · simp [h_mem] at h
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
    (argOpt : Option (UInt256 × Nat))
    (h_dec : s.decoded = some (.Dup op, argOpt))
    (h_gas : Gas.cost (.Dup op) ≤ s.gasAvailable)
    {sf : State} (h : stepF.dup s (s.consumeGas (Gas.cost (.Dup op)) h_gas) op = .ok sf) :
    Step s sf := by
  unfold stepF.dup at h
  match h_get : s.stack[op.idx.val]?, h with
  | some v, h => cases h
                 obtain ⟨idx⟩ := op
                 exact .dup s idx v argOpt h_dec h_running h_gas h_get
  | none, h   => exact absurd h (by intro hh; cases hh)

theorem swap_sound (s : State) (op : Operation.SwapOp)
    (h_running : s.halt = .Running)
    (argOpt : Option (UInt256 × Nat))
    (h_dec : s.decoded = some (.Swap op, argOpt))
    (h_gas : Gas.cost (.Swap op) ≤ s.gasAvailable)
    {sf : State} (h : stepF.swap s (s.consumeGas (Gas.cost (.Swap op)) h_gas) op = .ok sf) :
    Step s sf := by
  unfold stepF.swap at h
  match h_ex : s.stack.exchange 0 (op.idx.val + 1), h with
  | some stk', h => cases h
                    obtain ⟨idx⟩ := op
                    exact .swap s idx stk' argOpt h_dec h_running h_gas h_ex
  | none, h      => exact absurd h (by intro hh; cases hh)

theorem dupN_sound (s : State) (op : Operation.DupNOp)
    (h_running : s.halt = .Running)
    (argOpt : Option (UInt256 × Nat))
    (h_dec : s.decoded = some (.DupN op, argOpt))
    (h_gas : Gas.cost (.DupN op) ≤ s.gasAvailable)
    {sf : State} (h : stepF.dupN s (s.consumeGas (Gas.cost (.DupN op)) h_gas) op = .ok sf) :
    Step s sf := by
  unfold stepF.dupN at h
  match h_get : s.stack[op.n.val]?, h with
  | some v, h => cases h
                 obtain ⟨n⟩ := op
                 exact .dupN s n v argOpt h_dec h_running h_gas h_get
  | none, h   => exact absurd h (by intro hh; cases hh)

theorem swapN_sound (s : State) (op : Operation.SwapNOp)
    (h_running : s.halt = .Running)
    (argOpt : Option (UInt256 × Nat))
    (h_dec : s.decoded = some (.SwapN op, argOpt))
    (h_gas : Gas.cost (.SwapN op) ≤ s.gasAvailable)
    {sf : State} (h : stepF.swapN s (s.consumeGas (Gas.cost (.SwapN op)) h_gas) op = .ok sf) :
    Step s sf := by
  unfold stepF.swapN at h
  match h_ex : s.stack.exchange 0 (op.n.val + 1), h with
  | some stk', h => cases h
                    obtain ⟨n⟩ := op
                    exact .swapN s n stk' argOpt h_dec h_running h_gas h_ex
  | none, h      => exact absurd h (by intro hh; cases hh)

theorem exchange_sound (s : State) (op : Operation.ExchangeOp)
    (h_running : s.halt = .Running)
    (argOpt : Option (UInt256 × Nat))
    (h_dec : s.decoded = some (.Exchange op, argOpt))
    (h_gas : Gas.cost (.Exchange op) ≤ s.gasAvailable)
    {sf : State} (h : stepF.exchange s (s.consumeGas (Gas.cost (.Exchange op)) h_gas) op = .ok sf) :
    Step s sf := by
  unfold stepF.exchange at h
  match h_ex : s.stack.exchange (op.n + 1) (op.m + 1), h with
  | some stk', h => cases h
                    obtain ⟨b⟩ := op
                    exact .exchange s b stk' argOpt h_dec h_running h_gas h_ex
  | none, h      => exact absurd h (by intro hh; cases hh)

theorem env_sound (s : State) (op : Operation.EnvOps)
    (h_running : s.halt = .Running)
    (argOpt : Option (UInt256 × Nat))
    (h_dec : s.decoded = some (.Env op, argOpt))
    (h_gas : Gas.cost (.Env op) ≤ s.gasAvailable)
    {sf : State} (h : stepF.env s (s.consumeGas (Gas.cost (.Env op)) h_gas) op = .ok sf) :
    Step s sf := by
  unfold stepF.env at h
  cases op with
  | ADDRESS         => cases h; exact .address s argOpt h_dec h_running h_gas
  | ORIGIN          => cases h; exact .origin s argOpt h_dec h_running h_gas
  | CALLER          => cases h; exact .caller s argOpt h_dec h_running h_gas
  | CALLVALUE       => cases h; exact .callvalue s argOpt h_dec h_running h_gas
  | CALLDATASIZE    => cases h; exact .calldatasize s argOpt h_dec h_running h_gas
  | CODESIZE        => cases h; exact .codesize s argOpt h_dec h_running h_gas
  | GASPRICE        => cases h; exact .gasprice s argOpt h_dec h_running h_gas
  | RETURNDATASIZE  => cases h; exact .returndatasize s argOpt h_dec h_running h_gas
  | BALANCE =>
    match h_stack : s.stack, h with
    | a :: rest, h => cases h; exact .balance s a rest argOpt h_dec h_running h_gas h_stack
    | [], h       => exact absurd h (by intro hh; cases hh)
  | CALLDATALOAD =>
    match h_stack : s.stack, h with
    | i :: rest, h => cases h; exact .calldataload s i rest argOpt h_dec h_running h_gas h_stack
    | [], h       => exact absurd h (by intro hh; cases hh)
  | EXTCODESIZE =>
    match h_stack : s.stack, h with
    | a :: rest, h => cases h; exact .extcodesize s a rest argOpt h_dec h_running h_gas h_stack
    | [], h       => exact absurd h (by intro hh; cases hh)
  | EXTCODEHASH =>
    match h_stack : s.stack, h with
    | a :: rest, h => cases h; exact .extcodehash s a rest argOpt h_dec h_running h_gas h_stack
    | [], h       => exact absurd h (by intro hh; cases hh)
  | CALLDATACOPY =>
    match h_stack : s.stack, h with
    | dOff :: sOff :: sz :: rest, h =>
      unfold chargeMem at h
      by_cases h_mem : (s.consumeGas (Gas.cost (.Env .CALLDATACOPY)) h_gas).canExpandMemory
                         dOff.toNat sz.toNat
      · simp [h_mem] at h
        cases h
        exact .calldatacopy s dOff sOff sz rest argOpt h_dec h_running h_gas h_stack h_mem
      · simp [h_mem] at h
    | [], h     => exact absurd h (by intro hh; cases hh)
    | [_], h    => exact absurd h (by intro hh; cases hh)
    | [_, _], h => exact absurd h (by intro hh; cases hh)
  | CODECOPY =>
    match h_stack : s.stack, h with
    | dOff :: sOff :: sz :: rest, h =>
      unfold chargeMem at h
      by_cases h_mem : (s.consumeGas (Gas.cost (.Env .CODECOPY)) h_gas).canExpandMemory
                         dOff.toNat sz.toNat
      · simp [h_mem] at h
        cases h
        exact .codecopy s dOff sOff sz rest argOpt h_dec h_running h_gas h_stack h_mem
      · simp [h_mem] at h
    | [], h     => exact absurd h (by intro hh; cases hh)
    | [_], h    => exact absurd h (by intro hh; cases hh)
    | [_, _], h => exact absurd h (by intro hh; cases hh)
  | EXTCODECOPY =>
    match h_stack : s.stack, h with
    | a :: dOff :: sOff :: sz :: rest, h =>
      unfold chargeMem at h
      by_cases h_mem : (s.consumeGas (Gas.cost (.Env .EXTCODECOPY)) h_gas).canExpandMemory
                         dOff.toNat sz.toNat
      · simp [h_mem] at h
        cases h
        exact .extcodecopy s a dOff sOff sz rest argOpt h_dec h_running h_gas h_stack h_mem
      · simp [h_mem] at h
    | [], h        => exact absurd h (by intro hh; cases hh)
    | [_], h       => exact absurd h (by intro hh; cases hh)
    | [_, _], h    => exact absurd h (by intro hh; cases hh)
    | [_, _, _], h => exact absurd h (by intro hh; cases hh)
  | RETURNDATACOPY =>
    match h_stack : s.stack, h with
    | dOff :: sOff :: sz :: rest, h =>
      by_cases h_oob : sOff.toNat + sz.toNat > s.returnData.size
      · simp [h_oob] at h
      · simp [h_oob] at h
        unfold chargeMem at h
        by_cases h_mem : (s.consumeGas (Gas.cost (.Env .RETURNDATACOPY)) h_gas).canExpandMemory
                           dOff.toNat sz.toNat
        · simp [h_mem] at h
          cases h
          exact .returndatacopy s dOff sOff sz rest argOpt h_dec h_running h_gas h_stack
                  (Nat.le_of_not_lt h_oob) h_mem
        · simp [h_mem] at h
    | [], h     => exact absurd h (by intro hh; cases hh)
    | [_], h    => exact absurd h (by intro hh; cases hh)
    | [_, _], h => exact absurd h (by intro hh; cases hh)

set_option maxRecDepth 1024 in
theorem stackMemFlow_sound (s : State) (op : Operation.StackMemFlowOps)
    (h_running : s.halt = .Running)
    (argOpt : Option (UInt256 × Nat))
    (h_dec : s.decoded = some (.StackMemFlow op, argOpt))
    (h_gas : Gas.cost (.StackMemFlow op) ≤ s.gasAvailable)
    {sf : State} (h : stepF.stackMemFlow s
                        (s.consumeGas (Gas.cost (.StackMemFlow op)) h_gas) op = .ok sf) :
    Step s sf := by
  unfold stepF.stackMemFlow at h
  cases op with
  | POP =>
    match h_stack : s.stack, h with
    | a :: rest, h => cases h; exact .pop s a rest argOpt h_dec h_running h_gas h_stack
    | [], h       => exact absurd h (by intro hh; cases hh)
  | MLOAD =>
    match h_stack : s.stack, h with
    | offset :: rest, h =>
      unfold chargeMem at h
      by_cases h_mem : (s.consumeGas (Gas.cost (.StackMemFlow .MLOAD)) h_gas).canExpandMemory
                         offset.toNat 32
      · simp [h_mem] at h
        cases h_load : MachineState.mload
                         ((s.consumeGas (Gas.cost (.StackMemFlow .MLOAD)) h_gas).consumeMemExp
                            offset.toNat 32 h_mem).toMachineState offset with
        | mk v μ' =>
          simp [h_load] at h; cases h
          exact .mload s offset rest v μ' argOpt h_dec h_running h_gas h_stack h_mem h_load
      · simp [h_mem] at h
    | [], h => exact absurd h (by intro hh; cases hh)
  | MSTORE =>
    match h_stack : s.stack, h with
    | offset :: value :: rest, h =>
      unfold chargeMem at h
      by_cases h_mem : (s.consumeGas (Gas.cost (.StackMemFlow .MSTORE)) h_gas).canExpandMemory
                         offset.toNat 32
      · simp [h_mem] at h
        cases h
        exact .mstore s offset value rest argOpt h_dec h_running h_gas h_stack h_mem
      · simp [h_mem] at h
    | [], h     => exact absurd h (by intro hh; cases hh)
    | [_], h    => exact absurd h (by intro hh; cases hh)
  | MSTORE8 =>
    match h_stack : s.stack, h with
    | offset :: value :: rest, h =>
      unfold chargeMem at h
      by_cases h_mem : (s.consumeGas (Gas.cost (.StackMemFlow .MSTORE8)) h_gas).canExpandMemory
                         offset.toNat 1
      · simp [h_mem] at h
        cases h
        exact .mstore8 s offset value rest argOpt h_dec h_running h_gas h_stack h_mem
      · simp [h_mem] at h
    | [], h     => exact absurd h (by intro hh; cases hh)
    | [_], h    => exact absurd h (by intro hh; cases hh)
  | SLOAD =>
    match h_stack : s.stack, h with
    | key :: rest, h => cases h; exact .sload s key rest argOpt h_dec h_running h_gas h_stack
    | [], h         => exact absurd h (by intro hh; cases hh)
  | SSTORE =>
    by_cases h_perm : ¬ s.executionEnv.permitStateMutation
    · -- stepF returns static violation; no .ok
      simp [h_perm] at h
      unfold static at h; cases h
    · simp [h_perm] at h
      match h_stack : s.stack, h with
      | key :: value :: rest, h =>
        by_cases h_dyn :
          Gas.sstoreCost ((s.accountMap s.executionEnv.codeOwner).storage key) value
            ≤ (s.consumeGas (Gas.cost (.StackMemFlow .SSTORE)) h_gas).gasAvailable
        · simp [h_dyn] at h
          cases h
          exact .sstore s key value rest argOpt h_dec h_running
                  (by simp at h_perm; exact h_perm) h_gas h_stack h_dyn
        · simp [h_dyn] at h
      | [], h     => exact absurd h (by intro hh; cases hh)
      | [_], h    => exact absurd h (by intro hh; cases hh)
  | JUMP =>
    match h_stack : s.stack, h with
    | dest :: rest, h =>
      match h_target : Decode.decodeAt s.executionEnv.code dest.toNat, h with
      | some (.JUMPDEST, none), h =>
        simp [h_target] at h
        cases h
        exact .jump s dest rest argOpt h_dec h_running h_gas h_stack h_target
      | some (op', some _), h =>
        simp [h_target] at h
      | some (.StopArith _, none), h
      | some (.CompBit _, none), h
      | some (.Keccak _, none), h
      | some (.Env _, none), h
      | some (.Block _, none), h
      | some (.StackMemFlow .POP, none), h
      | some (.StackMemFlow .MLOAD, none), h
      | some (.StackMemFlow .MSTORE, none), h
      | some (.StackMemFlow .MSTORE8, none), h
      | some (.StackMemFlow .SLOAD, none), h
      | some (.StackMemFlow .SSTORE, none), h
      | some (.StackMemFlow .JUMP, none), h
      | some (.StackMemFlow .JUMPI, none), h
      | some (.StackMemFlow .PC, none), h
      | some (.StackMemFlow .MSIZE, none), h
      | some (.StackMemFlow .GAS, none), h
      | some (.StackMemFlow .TLOAD, none), h
      | some (.StackMemFlow .TSTORE, none), h
      | some (.StackMemFlow .MCOPY, none), h
      | some (.Push _, none), h
      | some (.Dup _, none), h
      | some (.Swap _, none), h
      | some (.DupN _, none), h
      | some (.SwapN _, none), h
      | some (.Exchange _, none), h
      | some (.Log _, none), h
      | some (.System _, none), h => simp [h_target] at h
      | none, h => simp [h_target] at h
    | [], h => exact absurd h (by intro hh; cases hh)
  | JUMPI =>
    match h_stack : s.stack, h with
    | dest :: cond :: rest, h =>
      by_cases h_cond : cond.toNat = 0
      · -- cond = 0: not-taken branch
        simp [h_cond] at h
        cases h
        apply Step.jumpi_notTaken s dest cond rest argOpt h_dec h_running h_gas h_stack
        intro hh; exact hh h_cond
      · -- cond ≠ 0: taken-or-bad-jump branch
        simp [h_cond] at h
        match h_target : Decode.decodeAt s.executionEnv.code dest.toNat, h with
        | some (.JUMPDEST, none), h =>
          simp at h
          cases h
          apply Step.jumpi_taken s dest cond rest argOpt h_dec h_running h_gas h_stack
          · exact h_cond
          · exact h_target
        | some (op', some _), h => simp at h
        | some (.StopArith _, none), h
        | some (.CompBit _, none), h
        | some (.Keccak _, none), h
        | some (.Env _, none), h
        | some (.Block _, none), h
        | some (.StackMemFlow .POP, none), h
        | some (.StackMemFlow .MLOAD, none), h
        | some (.StackMemFlow .MSTORE, none), h
        | some (.StackMemFlow .MSTORE8, none), h
        | some (.StackMemFlow .SLOAD, none), h
        | some (.StackMemFlow .SSTORE, none), h
        | some (.StackMemFlow .JUMP, none), h
        | some (.StackMemFlow .JUMPI, none), h
        | some (.StackMemFlow .PC, none), h
        | some (.StackMemFlow .MSIZE, none), h
        | some (.StackMemFlow .GAS, none), h
        | some (.StackMemFlow .TLOAD, none), h
        | some (.StackMemFlow .TSTORE, none), h
        | some (.StackMemFlow .MCOPY, none), h
        | some (.Push _, none), h
        | some (.Dup _, none), h
        | some (.Swap _, none), h
        | some (.DupN _, none), h
        | some (.SwapN _, none), h
        | some (.Exchange _, none), h
        | some (.Log _, none), h
        | some (.System _, none), h => simp at h
        | none, h => simp at h
    | [], h => exact absurd h (by intro hh; cases hh)
    | [_], h => exact absurd h (by intro hh; cases hh)
  | PC       => cases h; exact .pc s argOpt h_dec h_running h_gas
  | JUMPDEST => cases h; exact .jumpdest s argOpt h_dec h_running h_gas
  | MSIZE    => cases h; exact .msize s argOpt h_dec h_running h_gas
  | GAS      => cases h; exact .gas s argOpt h_dec h_running h_gas
  | TLOAD =>
    match h_stack : s.stack, h with
    | key :: rest, h => cases h; exact .tload s key rest argOpt h_dec h_running h_gas h_stack
    | [], h         => exact absurd h (by intro hh; cases hh)
  | TSTORE =>
    by_cases h_perm : ¬ s.executionEnv.permitStateMutation
    · simp [h_perm] at h
      unfold static at h; cases h
    · simp [h_perm] at h
      match h_stack : s.stack, h with
      | key :: value :: rest, h =>
        cases h
        exact .tstore s key value rest argOpt h_dec h_running
                (by simp at h_perm; exact h_perm) h_gas h_stack
      | [], h     => exact absurd h (by intro hh; cases hh)
      | [_], h    => exact absurd h (by intro hh; cases hh)
  | MCOPY =>
    match h_stack : s.stack, h with
    | dOff :: sOff :: sz :: rest, h =>
      unfold chargeMem2 at h
      by_cases h_mem : (s.consumeGas (Gas.cost (.StackMemFlow .MCOPY)) h_gas).canExpandMemory2
                         dOff.toNat sz.toNat sOff.toNat sz.toNat
      · simp [h_mem] at h
        cases h
        exact .mcopy s dOff sOff sz rest argOpt h_dec h_running h_gas h_stack h_mem
      · simp [h_mem] at h
    | [], h     => exact absurd h (by intro hh; cases hh)
    | [_], h    => exact absurd h (by intro hh; cases hh)
    | [_, _], h => exact absurd h (by intro hh; cases hh)

theorem push_sound (s : State) (op : Operation.PushOp) (argOpt : Option (UInt256 × Nat))
    (h_running : s.halt = .Running)
    (h_dec : s.decoded = some (.Push op, argOpt))
    (h_gas : Gas.cost (.Push op) ≤ s.gasAvailable)
    {sf : State} (h : stepF.push s (s.consumeGas (Gas.cost (.Push op)) h_gas) op argOpt = .ok sf) :
    Step s sf := by
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
    exact Step.push0 s argOpt h_dec h_running h_gas
  | k+1, hw, h_dec, h_gas, h =>
    -- PUSHk case: width is k+1, argOpt determines whether we succeed.
    match h_arg : argOpt, h with
    | some (d, n), h =>
      simp at h
      cases h
      exact Step.pushN s ⟨k+1, hw⟩ d n (Nat.succ_pos k) h_dec h_running h_gas
    | none, h => simp at h

theorem log_sound (s : State) (op : Operation.LogOp)
    (h_running : s.halt = .Running)
    (argOpt : Option (UInt256 × Nat))
    (h_dec : s.decoded = some (.Log op, argOpt))
    (h_gas : Gas.cost (.Log op) ≤ s.gasAvailable)
    {sf : State} (h : stepF.log s (s.consumeGas (Gas.cost (.Log op)) h_gas) op = .ok sf) :
    Step s sf := by
  unfold stepF.log at h
  by_cases h_perm : ¬ s.executionEnv.permitStateMutation
  · simp [h_perm] at h
    unfold static at h
    cases h
  · simp [h_perm] at h
    match h_stack : s.stack, h with
    | offset :: size :: rest, h =>
      unfold chargeMem at h
      by_cases h_mem : (s.consumeGas (Gas.cost (.Log op)) h_gas).canExpandMemory
                         offset.toNat size.toNat
      · simp [h_mem] at h
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
          exact Step.log s n offset size topics rest' argOpt h_dec h_running h_perm'
                         h_gas h_len h_stack' h_mem
        | none =>
          simp [h_pop] at h
          unfold underflow at h
          cases h
      · simp [h_mem] at h
    | [], h     => exact absurd h (by intro hh; cases hh)
    | [_], h    => exact absurd h (by intro hh; cases hh)

end stepF

----------------------------------------------------------------------------
-- The headline theorem: assembled from the helper-soundness lemmas above.
-- Every `Operation` top-level constructor dispatches to its `*_sound`
-- companion. The outer halt / decode / gas branches that don't reach
-- a helper contradict `h : … = .ok s'` directly.
----------------------------------------------------------------------------

/-- **Soundness of the executable shadow.** Every `.ok` outcome of `stepF`
    corresponds to a derivation of the relational small-step `Step`.

    The outer dispatch (halt → decode → gas → operation) is unfolded by
    `split at h`. The boring branches (already-halted source, decode
    failure, gas-check failure) all contradict `h : … = .ok s'`. The
    interesting branches dispatch to the 14 per-helper soundness lemmas
    proven above, one per top-level `Operation` constructor. -/
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
      exact absurd h (by intro hh; cases hh)
    · -- decoded = some (op, argOpt)
      rename_i op argOpt h_dec
      -- Split on the gas check.
      split at h
      · -- gas ≥ cost
        rename_i h_gas
        -- Split on the operation kind.
        cases op with
        | StopArith op =>
          exact stepF.stopArith_sound s op h_running argOpt h_dec h_gas h
        | CompBit op =>
          exact stepF.compBit_sound s op h_running argOpt h_dec h_gas h
        | Keccak op =>
          exact stepF.keccak_sound s op h_running argOpt h_dec h_gas h
        | Env op =>
          exact stepF.env_sound s op h_running argOpt h_dec h_gas h
        | Block op =>
          exact stepF.block_sound s op h_running argOpt h_dec h_gas h
        | StackMemFlow op =>
          exact stepF.stackMemFlow_sound s op h_running argOpt h_dec h_gas h
        | Push op =>
          exact stepF.push_sound s op argOpt h_running h_dec h_gas h
        | Dup op =>
          exact stepF.dup_sound s op h_running argOpt h_dec h_gas h
        | Swap op =>
          exact stepF.swap_sound s op h_running argOpt h_dec h_gas h
        | DupN op =>
          exact stepF.dupN_sound s op h_running argOpt h_dec h_gas h
        | SwapN op =>
          exact stepF.swapN_sound s op h_running argOpt h_dec h_gas h
        | Exchange op =>
          exact stepF.exchange_sound s op h_running argOpt h_dec h_gas h
        | Log op =>
          exact stepF.log_sound s op h_running argOpt h_dec h_gas h
        | System op =>
          exact stepF.system_sound s op h_running argOpt h_dec h_gas h
      · -- gas < cost
        exact absurd h (by intro hh; cases hh)
  all_goals exact absurd h (by intro hh; cases hh)

end EVM
end EvmSemantics
