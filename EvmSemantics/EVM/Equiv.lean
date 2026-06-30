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

**Bridging chained vs bundled gas.** `stepF` charges gas in chained form
(via `consumeGas` and `consumeMemExp`/`consumeMemExp2`), while
`StepRunning` uses a single bundled `Gas.<op>Total` total in both its
pre-condition and post-state. For each `chargeMem`-style helper, the
proof:

1. Builds the bundled `h_total : Gas.<op>Total s … ≤ s.gasAvailable`
   from the chained `h_gas`/`h_mem`/`h_dyn` hypotheses with
   `simp` + `omega` (using `set` to consolidate the recurring atoms
   `base` and `memDelta` and avoid the `s.fork` / `s.fork`
   abbrev mismatch confusing omega).
2. Proves a `post_eq` lemma showing the chained `stepF` post-state
   equals the bundled constructor post-state. The two states agree on
   every field except `gasAvailable`, where chained
   `((g - base) - memDelta) - kwc` and bundled `g - (base + memDelta +
   kwc)` are equal by `Nat.sub_add_eq` (closed by `grind`).
3. Rewrites with `post_eq` and applies the matching constructor.

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
          -- Combine `h_gas` (base ≤ gas) and `h_dyn` (dyn ≤ gas - base)
          -- into the single hypothesis `base + dyn ≤ gas` that the
          -- record-update `.exp` rule expects.
          have h_total :
              Gas.baseCost s.fork (.StopArith .EXP) + Gas.expByteCost s.fork b
                ≤ s.gasAvailable := by
            unfold State.consumeGas at h_dyn
            simp at h_dyn
            omega
          exact .exp s a b rest h_dec h_total h_stack
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
          -- Bundle h_gas + h_mem + h_dyn into `Gas.keccakTotal s offset size`.
          -- Abstract the recurring `Gas.baseCost s.fork .KECCAK256` and the
          -- memory-expansion delta to single atoms first; otherwise omega sees
          -- multiple syntactic forms (via the `s.fork` abbrev and the
          -- `Operation.KECCAK256` match-pattern abbrev) and can't relate them.
          set base := Gas.baseCost s.fork (.Keccak .KECCAK256) with hbase
          set md := MachineState.memCost (MachineState.activeWordsAfter
                      s.activeWords.toNat offset.toNat size.toNat)
                    - MachineState.memCost s.activeWords.toNat with hmd
          have h_total : Gas.keccakTotal s offset size ≤ s.gasAvailable := by
            show base + md + Gas.keccakWordCost size ≤ s.gasAvailable
            simp only [State.canExpandMemory, State.consumeGas, State.consumeMemExp,
                       MachineState.memExpansionDelta, ← hbase, ← hmd] at h_mem h_dyn
            omega
          -- The `stepF` post-state agrees with the constructor's post-state on
          -- all fields except `gasAvailable`, where stepF accumulates the gas
          -- charges in *chained* form `((g - base) - md) - kwc` and the
          -- constructor uses *bundled* form `g - (base + md + kwc)`. Prove the
          -- two states equal, then rewrite the goal.
          have state_eq :
              ((((s.consumeGas base h_gas).consumeMemExp offset.toNat size.toNat
                  h_mem).consumeGas (Gas.keccakWordCost size) h_dyn).replaceStackAndIncrPC
                (EvmSemantics.keccak256
                  (MachineState.readPadded s.memory offset.toNat size.toNat) :: rest))
              = ({ s with
                    stack := EvmSemantics.keccak256
                              (MachineState.readPadded s.memory offset.toNat size.toNat) :: rest
                    pc := s.pc.succ
                    gasAvailable := s.gasAvailable - Gas.keccakTotal s offset size
                    activeWords := s.activeWordsAfterUInt256 offset.toNat size.toNat
                  } : State) := by
            simp [State.consumeGas, State.consumeMemExp,
                  State.replaceStackAndIncrPC, State.activeWordsAfterUInt256,
                  Gas.keccakTotal, UInt256.succ, MachineState.memExpansionDelta,
                  show ∀ (a b : UInt256), a + b = a.add b from fun _ _ => rfl]
            grind
          rw [state_eq]
          exact StepRunning.keccak256 s offset size rest h_dec h_stack h_total
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
        set base := Gas.baseCost s.fork (.System .RETURN) with hbase
        set md := MachineState.memCost (MachineState.activeWordsAfter
                    s.activeWords.toNat offset.toNat size.toNat)
                  - MachineState.memCost s.activeWords.toNat with hmd
        have h_total : Gas.returnTotal s offset size ≤ s.gasAvailable := by
          show base + md ≤ s.gasAvailable
          simp [State.canExpandMemory, State.consumeGas,
                MachineState.memExpansionDelta, ← hbase, ← hmd] at h_mem
          omega
        have post_eq :
            ({ (s.consumeGas base h_gas).consumeMemExp
                offset.toNat size.toNat h_mem with
                halt := .Returned
                hReturn := MachineState.readPadded s.memory offset.toNat size.toNat
                stack := rest } : State)
            = ({ s with
                  halt := .Returned
                  hReturn := MachineState.readPadded s.memory offset.toNat size.toNat
                  stack := rest
                  gasAvailable := s.gasAvailable - Gas.returnTotal s offset size
                  activeWords := s.activeWordsAfterUInt256 offset.toNat size.toNat } : State) := by
          simp [State.consumeGas, State.consumeMemExp, State.activeWordsAfterUInt256,
                Gas.returnTotal, MachineState.memExpansionDelta, ← hbase, ← hmd]
          grind
        rw [post_eq]
        exact StepRunning.return_ s offset size rest h_dec h_stack h_total
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
        set base := Gas.baseCost s.fork (.System .REVERT) with hbase
        set md := MachineState.memCost (MachineState.activeWordsAfter
                    s.activeWords.toNat offset.toNat size.toNat)
                  - MachineState.memCost s.activeWords.toNat with hmd
        have h_total : Gas.revertTotal s offset size ≤ s.gasAvailable := by
          show base + md ≤ s.gasAvailable
          simp [State.canExpandMemory, State.consumeGas,
                MachineState.memExpansionDelta, ← hbase, ← hmd] at h_mem
          omega
        have post_eq :
            ({ (s.consumeGas base h_gas).consumeMemExp
                offset.toNat size.toNat h_mem with
                halt := .Reverted
                hReturn := MachineState.readPadded s.memory offset.toNat size.toNat
                stack := rest } : State)
            = ({ s with
                  halt := .Reverted
                  hReturn := MachineState.readPadded s.memory offset.toNat size.toNat
                  stack := rest
                  gasAvailable := s.gasAvailable - Gas.revertTotal s offset size
                  activeWords := s.activeWordsAfterUInt256 offset.toNat size.toNat } : State) := by
          simp [State.consumeGas, State.consumeMemExp, State.activeWordsAfterUInt256,
                Gas.revertTotal, MachineState.memExpansionDelta, ← hbase, ← hmd]
          grind
        rw [post_eq]
        exact StepRunning.revert s offset size rest h_dec h_stack h_total
      · simp [h_mem] at h
    | [], h           => nomatch h
    | [_], h          => nomatch h
  | INVALID =>
    -- stepF.system returns .error on INVALID; no .ok possible
    nomatch h
  | CALL =>
    match h_stack : s.stack, h with
    | gasArg :: toArg :: value :: argsOff :: argsLen :: retOff :: retLen :: rest, h =>
      by_cases h_static : ¬ s.executionEnv.permitStateMutation ∧ value.toNat ≠ 0
      · simp only [if_pos h_static, static] at h
        cases h
      · simp only [if_neg h_static] at h
        unfold chargeMem2 at h
        by_cases h_mem :
            (s.consumeGas (Gas.baseCost s.fork (.System .CALL)) h_gas).canExpandMemory2
              argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat
        · simp only [h_mem, dif_pos] at h
          set base := Gas.baseCost s.fork (.System .CALL) with hbase
          set md := MachineState.memCost
                      (MachineState.activeWordsAfter
                        (MachineState.activeWordsAfter s.activeWords.toNat
                          argsOff.toNat argsLen.toNat)
                        retOff.toNat retLen.toNat)
                    - MachineState.memCost s.activeWords.toNat with hmd
          split at h
          · rename_i h_sc
            -- The `accountMap` reads through `consumeGas`/`consumeMemExp2` are the
            -- same as on `s`. We need that for the surcharge bundling.
            set surch := Gas.callSurcharge s.fork (value.toNat != 0)
                  (((s.consumeGas base h_gas).consumeMemExp2 argsOff.toNat argsLen.toNat
                    retOff.toNat retLen.toNat h_mem).accountMap
                    (AccountAddress.ofUInt256 toArg)).isEmpty with hsurch
            have h_surch_eq : surch = Gas.callSurcharge s.fork (value.toNat != 0)
                (s.accountMap (AccountAddress.ofUInt256 toArg)).isEmpty := by
              simp [hsurch, State.consumeGas, State.consumeMemExp2]
            have h_committed :
                Gas.callCommitted s value argsOff argsLen retOff retLen toArg
                ≤ s.gasAvailable := by
              show base + md + Gas.callSurcharge s.fork (value.toNat != 0)
                    (s.accountMap (AccountAddress.ofUInt256 toArg)).isEmpty
                  ≤ s.gasAvailable
              rw [← h_surch_eq]
              simp [State.canExpandMemory2, State.consumeGas, State.consumeMemExp2,
                    MachineState.memExpansionDelta2, ← hbase, ← hmd] at h_mem h_sc
              omega
            split at h
            · rename_i h_fail
              cases h
              have h_fail' : s.executionEnv.depth ≥ 1024 ∨
                  (s.accountMap s.executionEnv.address).balance < value := by
                simpa [State.consumeGas, State.consumeMemExp2] using h_fail
              set s3 := ((s.consumeGas base h_gas).consumeMemExp2 argsOff.toNat argsLen.toNat
                          retOff.toNat retLen.toNat h_mem).consumeGas surch h_sc with hs3
              have post_eq :
                  ({ (if (value.toNat != 0) then
                        { s3 with gasAvailable := s3.gasAvailable + Gas.callStipend }
                      else s3) with
                      returnData := .empty }.replaceStackAndIncrPC
                    (UInt256.ofNat 0 :: rest))
                  = ({ s with
                      gasAvailable := s.gasAvailable
                        - Gas.callCommitted s value argsOff argsLen retOff retLen toArg
                        + (bif (value.toNat != 0) then Gas.callStipend else 0)
                      activeWords := s.activeWordsAfterUInt256_2
                        argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat
                      returnData := .empty
                      stack := UInt256.ofNat 0 :: rest
                      pc := s.pc.succ } : State) := by
                by_cases h_vnz : value.toNat != 0 <;>
                  simp [hs3, State.consumeGas, State.consumeMemExp2,
                        State.replaceStackAndIncrPC,
                        State.activeWordsAfterUInt256_2, Gas.callCommitted,
                        UInt256.succ, MachineState.memExpansionDelta2, h_vnz,
                        show ∀ (a b : UInt256), a + b = a.add b from fun _ _ => rfl] <;>
                  grind
              rw [post_eq]
              exact StepRunning.callFail s gasArg toArg value argsOff argsLen retOff retLen
                rest h_dec h_stack h_committed h_fail'
            · rename_i h_take
              split at h
              · rename_i h_fw
                cases h
                have h_take' : ¬ (s.executionEnv.depth ≥ 1024 ∨
                    (s.accountMap s.executionEnv.address).balance < value) := by
                  simpa [State.consumeGas, State.consumeMemExp2] using h_take
                have post_eq :
                    ((((s.consumeGas base h_gas).consumeMemExp2 argsOff.toNat argsLen.toNat
                        retOff.toNat retLen.toNat h_mem).consumeGas surch h_sc).consumeGas
                        (min gasArg.toNat (Gas.allButOneSixtyFourth s.fork
                          (((s.consumeGas base h_gas).consumeMemExp2 argsOff.toNat
                              argsLen.toNat retOff.toNat retLen.toNat h_mem).consumeGas
                            surch h_sc).gasAvailable)) h_fw).enterCall
                      rest (AccountAddress.ofUInt256 toArg) value
                      (MachineState.readPadded
                        ((((s.consumeGas base h_gas).consumeMemExp2 argsOff.toNat
                          argsLen.toNat retOff.toNat retLen.toNat h_mem).consumeGas surch
                            h_sc).consumeGas _ h_fw).memory
                        argsOff.toNat argsLen.toNat)
                      (((s.consumeGas base h_gas).consumeMemExp2 argsOff.toNat argsLen.toNat
                          retOff.toNat retLen.toNat h_mem).accountMap
                        (AccountAddress.ofUInt256 toArg)).code
                      ((min gasArg.toNat (Gas.allButOneSixtyFourth s.fork
                        (((s.consumeGas base h_gas).consumeMemExp2 argsOff.toNat
                          argsLen.toNat retOff.toNat retLen.toNat h_mem).consumeGas
                            surch h_sc).gasAvailable))
                        + (bif (value.toNat != 0) then Gas.callStipend else 0))
                      retOff.toNat retLen.toNat
                    = (({ s with
                          gasAvailable := s.gasAvailable
                            - Gas.callCommitted s value argsOff argsLen retOff retLen toArg
                            - (min gasArg.toNat (Gas.allButOneSixtyFourth s.fork
                                (s.gasAvailable
                                 - Gas.callCommitted s value argsOff argsLen retOff retLen
                                   toArg)))
                          activeWords := s.activeWordsAfterUInt256_2
                            argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat
                        } : State).enterCall rest (AccountAddress.ofUInt256 toArg) value
                          (MachineState.readPadded s.memory argsOff.toNat argsLen.toNat)
                          (s.accountMap (AccountAddress.ofUInt256 toArg)).code
                          ((min gasArg.toNat (Gas.allButOneSixtyFourth s.fork
                              (s.gasAvailable
                               - Gas.callCommitted s value argsOff argsLen retOff retLen
                                 toArg)))
                            + (bif (value.toNat != 0) then Gas.callStipend else 0))
                          retOff.toNat retLen.toNat) := by
                  simp [State.enterCall, State.consumeGas, State.consumeMemExp2,
                        State.activeWordsAfterUInt256_2, Gas.callCommitted,
                        MachineState.memExpansionDelta2,
                        show ∀ (a b : UInt256), a + b = a.add b from fun _ _ => rfl]
                  grind
                rw [post_eq]
                exact StepRunning.call s gasArg toArg value argsOff argsLen retOff retLen
                  rest _ h_dec h_stack h_committed h_take' rfl
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
        set base := Gas.baseCost s.fork (.System .CALLCODE) with hbase
        set md := MachineState.memCost
                    (MachineState.activeWordsAfter
                      (MachineState.activeWordsAfter s.activeWords.toNat
                        argsOff.toNat argsLen.toNat)
                      retOff.toNat retLen.toNat)
                  - MachineState.memCost s.activeWords.toNat with hmd
        split at h
        · rename_i h_sc
          have h_committed :
              Gas.callcodeCommitted s value argsOff argsLen retOff retLen ≤ s.gasAvailable := by
            show base + md + Gas.callSurcharge s.fork (value.toNat != 0) false
                ≤ s.gasAvailable
            simp [State.canExpandMemory2, State.consumeGas, State.consumeMemExp2,
                  MachineState.memExpansionDelta2, Gas.callSurcharge, Bool.and_false,
                  ← hbase, ← hmd] at h_mem h_sc
            simp [Gas.callSurcharge, Bool.and_false]
            omega
          split at h
          · rename_i h_fail
            cases h
            have h_fail' : s.executionEnv.depth ≥ 1024 ∨
                (s.accountMap s.executionEnv.address).balance < value := by
              simpa [State.consumeGas, State.consumeMemExp2] using h_fail
            -- LHS-after-replaceStackAndIncrPC, in two pieces.
            set s3 := ((s.consumeGas base h_gas).consumeMemExp2 argsOff.toNat argsLen.toNat
                        retOff.toNat retLen.toNat h_mem).consumeGas
                        (Gas.callSurcharge s.fork (value.toNat != 0) false) h_sc with hs3
            have post_eq :
                ({ (if (value.toNat != 0) then
                      { s3 with gasAvailable := s3.gasAvailable + Gas.callStipend }
                    else s3) with
                    returnData := .empty }.replaceStackAndIncrPC (UInt256.ofNat 0 :: rest))
                = ({ s with
                    gasAvailable := s.gasAvailable
                      - Gas.callcodeCommitted s value argsOff argsLen retOff retLen
                      + (bif (value.toNat != 0) then Gas.callStipend else 0)
                    activeWords := s.activeWordsAfterUInt256_2
                      argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat
                    returnData := .empty
                    stack := UInt256.ofNat 0 :: rest
                    pc := s.pc.succ } : State) := by
              by_cases h_vnz : value.toNat != 0 <;>
                simp [hs3, State.consumeGas, State.consumeMemExp2,
                      State.replaceStackAndIncrPC,
                      State.activeWordsAfterUInt256_2, Gas.callcodeCommitted,
                      UInt256.succ, MachineState.memExpansionDelta2, h_vnz,
                      show ∀ (a b : UInt256), a + b = a.add b from fun _ _ => rfl] <;>
                grind
            rw [post_eq]
            exact StepRunning.callcodeFail s gasArg toArg value argsOff argsLen retOff retLen
              rest h_dec h_stack h_committed h_fail'
          · rename_i h_take
            split at h
            · rename_i h_fw
              cases h
              have h_take' : ¬ (s.executionEnv.depth ≥ 1024 ∨
                  (s.accountMap s.executionEnv.address).balance < value) := by
                simpa [State.consumeGas, State.consumeMemExp2] using h_take
              have post_eq :
                  ((((s.consumeGas base h_gas).consumeMemExp2 argsOff.toNat argsLen.toNat
                      retOff.toNat retLen.toNat h_mem).consumeGas
                      (Gas.callSurcharge s.fork (value.toNat != 0) false) h_sc).consumeGas
                      (min gasArg.toNat (Gas.allButOneSixtyFourth s.fork
                        ((((s.consumeGas base h_gas).consumeMemExp2 argsOff.toNat
                          argsLen.toNat retOff.toNat retLen.toNat h_mem).consumeGas
                          (Gas.callSurcharge s.fork (value.toNat != 0) false) h_sc).gasAvailable)))
                      h_fw).enterCall rest
                    (((((s.consumeGas base h_gas).consumeMemExp2 argsOff.toNat
                        argsLen.toNat retOff.toNat retLen.toNat h_mem).consumeGas
                        (Gas.callSurcharge s.fork (value.toNat != 0) false) h_sc).consumeGas
                        _ h_fw).executionEnv.address)
                    value
                    (MachineState.readPadded
                      ((((s.consumeGas base h_gas).consumeMemExp2 argsOff.toNat
                        argsLen.toNat retOff.toNat retLen.toNat h_mem).consumeGas
                        (Gas.callSurcharge s.fork (value.toNat != 0) false) h_sc).consumeGas
                        _ h_fw).memory argsOff.toNat argsLen.toNat)
                    (((s.consumeGas base h_gas).consumeMemExp2 argsOff.toNat argsLen.toNat
                        retOff.toNat retLen.toNat h_mem).accountMap
                      (AccountAddress.ofUInt256 toArg)).code
                    ((min gasArg.toNat (Gas.allButOneSixtyFourth s.fork
                      ((((s.consumeGas base h_gas).consumeMemExp2 argsOff.toNat
                        argsLen.toNat retOff.toNat retLen.toNat h_mem).consumeGas
                        (Gas.callSurcharge s.fork (value.toNat != 0) false) h_sc).gasAvailable)))
                      + (bif (value.toNat != 0) then Gas.callStipend else 0))
                    retOff.toNat retLen.toNat
                  = (({ s with
                        gasAvailable := s.gasAvailable
                          - Gas.callcodeCommitted s value argsOff argsLen retOff retLen
                          - (min gasArg.toNat (Gas.allButOneSixtyFourth s.fork
                              (s.gasAvailable
                               - Gas.callcodeCommitted s value argsOff argsLen retOff retLen)))
                        activeWords := s.activeWordsAfterUInt256_2
                          argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat
                      } : State).enterCall rest s.executionEnv.address value
                        (MachineState.readPadded s.memory argsOff.toNat argsLen.toNat)
                        (s.accountMap (AccountAddress.ofUInt256 toArg)).code
                        ((min gasArg.toNat (Gas.allButOneSixtyFourth s.fork
                            (s.gasAvailable
                             - Gas.callcodeCommitted s value argsOff argsLen retOff retLen)))
                          + (bif (value.toNat != 0) then Gas.callStipend else 0))
                        retOff.toNat retLen.toNat) := by
                simp [State.enterCall, State.consumeGas, State.consumeMemExp2,
                      State.activeWordsAfterUInt256_2, Gas.callcodeCommitted,
                      MachineState.memExpansionDelta2,
                      show ∀ (a b : UInt256), a + b = a.add b from fun _ _ => rfl]
                grind
              rw [post_eq]
              exact StepRunning.callcode s gasArg toArg value argsOff argsLen retOff retLen
                rest _ h_dec h_stack h_committed h_take' rfl
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
  | DELEGATECALL =>
    match h_stack : s.stack, h with
    | gasArg :: toArg :: argsOff :: argsLen :: retOff :: retLen :: rest, h =>
      unfold chargeMem2 at h
      by_cases h_mem :
          (s.consumeGas (Gas.baseCost s.fork (.System .DELEGATECALL)) h_gas).canExpandMemory2
            argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat
      · simp only [h_mem, dif_pos] at h
        set base := Gas.baseCost s.fork (.System .DELEGATECALL) with hbase
        set md := MachineState.memCost
                    (MachineState.activeWordsAfter
                      (MachineState.activeWordsAfter s.activeWords.toNat
                        argsOff.toNat argsLen.toNat)
                      retOff.toNat retLen.toNat)
                  - MachineState.memCost s.activeWords.toNat with hmd
        have h_committed :
            Gas.delegatecallCommitted s argsOff argsLen retOff retLen ≤ s.gasAvailable := by
          show base + md ≤ s.gasAvailable
          simp [State.canExpandMemory2, State.consumeGas,
                MachineState.memExpansionDelta2, ← hbase, ← hmd] at h_mem
          omega
        split at h
        · rename_i h_fail
          cases h
          have h_fail' : s.executionEnv.depth ≥ 1024 := by
            simpa [State.consumeGas, State.consumeMemExp2] using h_fail
          have post_eq :
              ({ (s.consumeGas base h_gas).consumeMemExp2 argsOff.toNat argsLen.toNat
                  retOff.toNat retLen.toNat h_mem with
                  returnData := .empty }.replaceStackAndIncrPC (UInt256.ofNat 0 :: rest))
              = ({ s with
                    gasAvailable := s.gasAvailable
                      - Gas.delegatecallCommitted s argsOff argsLen retOff retLen
                    activeWords := s.activeWordsAfterUInt256_2
                      argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat
                    returnData := .empty
                    stack := UInt256.ofNat 0 :: rest
                    pc := s.pc.succ } : State) := by
            simp [State.consumeGas, State.consumeMemExp2, State.replaceStackAndIncrPC,
                  State.activeWordsAfterUInt256_2, Gas.delegatecallCommitted,
                  UInt256.succ, MachineState.memExpansionDelta2,
                  show ∀ (a b : UInt256), a + b = a.add b from fun _ _ => rfl]
            grind
          rw [post_eq]
          exact StepRunning.delegatecallFail s gasArg toArg argsOff argsLen retOff retLen
            rest h_dec h_stack h_committed h_fail'
        · rename_i h_take
          split at h
          · rename_i h_fw
            cases h
            have h_take' : ¬ s.executionEnv.depth ≥ 1024 := by
              simpa [State.consumeGas, State.consumeMemExp2] using h_take
            -- `forwarded` is bound by stepF as
            -- `min gasArg.toNat (allButOneSixtyFourth s2.gasAvailable)`, where
            -- `s2.gasAvailable = s.gasAvailable - Gas.delegatecallCommitted s …`.
            have h_fwd_eq :
                ((s.consumeGas base h_gas).consumeMemExp2 argsOff.toNat argsLen.toNat
                  retOff.toNat retLen.toNat h_mem).gasAvailable
                = s.gasAvailable - Gas.delegatecallCommitted s argsOff argsLen retOff retLen := by
              simp [State.consumeGas, State.consumeMemExp2, Gas.delegatecallCommitted,
                    MachineState.memExpansionDelta2, ← hbase, ← hmd]
              omega
            -- The stepF post-state matches the bundled rule's post-state because
            -- (i) `s2.gasAvailable = s.gasAvailable - committed` (`h_fwd_eq`),
            -- and (ii) `consumeGas` is proof-irrelevant in its proof argument.
            -- We prove the post-state equality by a single `simp` + `grind`,
            -- threading `h_fwd_eq` through.
            have post_eq :
                (((s.consumeGas base h_gas).consumeMemExp2 argsOff.toNat argsLen.toNat
                  retOff.toNat retLen.toNat h_mem).consumeGas
                    (min gasArg.toNat (Gas.allButOneSixtyFourth s.fork
                      ((s.consumeGas base h_gas).consumeMemExp2 argsOff.toNat argsLen.toNat
                        retOff.toNat retLen.toNat h_mem).gasAvailable))
                    h_fw).enterCallFor
                  .DelegateCall rest (AccountAddress.ofUInt256 toArg) ⟨0⟩
                  (MachineState.readPadded
                    (((s.consumeGas base h_gas).consumeMemExp2 argsOff.toNat argsLen.toNat
                      retOff.toNat retLen.toNat h_mem).consumeGas _ h_fw).memory
                    argsOff.toNat argsLen.toNat)
                  (((s.consumeGas base h_gas).consumeMemExp2 argsOff.toNat argsLen.toNat
                      retOff.toNat retLen.toNat h_mem).accountMap
                    (AccountAddress.ofUInt256 toArg)).code
                  (min gasArg.toNat (Gas.allButOneSixtyFourth s.fork
                    ((s.consumeGas base h_gas).consumeMemExp2 argsOff.toNat argsLen.toNat
                      retOff.toNat retLen.toNat h_mem).gasAvailable))
                  retOff.toNat retLen.toNat
                = (({ s with
                      gasAvailable := s.gasAvailable
                        - Gas.delegatecallCommitted s argsOff argsLen retOff retLen
                        - (min gasArg.toNat (Gas.allButOneSixtyFourth s.fork
                            (s.gasAvailable
                              - Gas.delegatecallCommitted s argsOff argsLen retOff retLen)))
                      activeWords := s.activeWordsAfterUInt256_2
                        argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat
                    } : State).enterCallFor .DelegateCall rest
                      (AccountAddress.ofUInt256 toArg) ⟨0⟩
                      (MachineState.readPadded s.memory argsOff.toNat argsLen.toNat)
                      (s.accountMap (AccountAddress.ofUInt256 toArg)).code
                      (min gasArg.toNat (Gas.allButOneSixtyFourth s.fork
                        (s.gasAvailable
                          - Gas.delegatecallCommitted s argsOff argsLen retOff retLen)))
                      retOff.toNat retLen.toNat) := by
              simp [State.enterCallFor, State.consumeGas, State.consumeMemExp2,
                    State.activeWordsAfterUInt256_2, Gas.delegatecallCommitted,
                    MachineState.memExpansionDelta2,
                    show ∀ (a b : UInt256), a + b = a.add b from fun _ _ => rfl]
              grind
            rw [post_eq]
            exact StepRunning.delegatecall s gasArg toArg argsOff argsLen retOff retLen
              rest _ h_dec h_stack h_committed h_take' rfl
          · nomatch h
      · simp [h_mem] at h
    | [], h                            => nomatch h
    | [_], h                           => nomatch h
    | [_, _], h                        => nomatch h
    | [_, _, _], h                     => nomatch h
    | [_, _, _, _], h                  => nomatch h
    | [_, _, _, _, _], h               => nomatch h
  | STATICCALL =>
    match h_stack : s.stack, h with
    | gasArg :: toArg :: argsOff :: argsLen :: retOff :: retLen :: rest, h =>
      unfold chargeMem2 at h
      by_cases h_mem :
          (s.consumeGas (Gas.baseCost s.fork (.System .STATICCALL)) h_gas).canExpandMemory2
            argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat
      · simp only [h_mem, dif_pos] at h
        set base := Gas.baseCost s.fork (.System .STATICCALL) with hbase
        set md := MachineState.memCost
                    (MachineState.activeWordsAfter
                      (MachineState.activeWordsAfter s.activeWords.toNat
                        argsOff.toNat argsLen.toNat)
                      retOff.toNat retLen.toNat)
                  - MachineState.memCost s.activeWords.toNat with hmd
        have h_committed :
            Gas.staticcallCommitted s argsOff argsLen retOff retLen ≤ s.gasAvailable := by
          show base + md ≤ s.gasAvailable
          simp [State.canExpandMemory2, State.consumeGas,
                MachineState.memExpansionDelta2, ← hbase, ← hmd] at h_mem
          omega
        split at h
        · rename_i h_fail
          cases h
          have h_fail' : s.executionEnv.depth ≥ 1024 := by
            simpa [State.consumeGas, State.consumeMemExp2] using h_fail
          have post_eq :
              ({ (s.consumeGas base h_gas).consumeMemExp2 argsOff.toNat argsLen.toNat
                  retOff.toNat retLen.toNat h_mem with
                  returnData := .empty }.replaceStackAndIncrPC (UInt256.ofNat 0 :: rest))
              = ({ s with
                    gasAvailable := s.gasAvailable
                      - Gas.staticcallCommitted s argsOff argsLen retOff retLen
                    activeWords := s.activeWordsAfterUInt256_2
                      argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat
                    returnData := .empty
                    stack := UInt256.ofNat 0 :: rest
                    pc := s.pc.succ } : State) := by
            simp [State.consumeGas, State.consumeMemExp2, State.replaceStackAndIncrPC,
                  State.activeWordsAfterUInt256_2, Gas.staticcallCommitted,
                  UInt256.succ, MachineState.memExpansionDelta2,
                  show ∀ (a b : UInt256), a + b = a.add b from fun _ _ => rfl]
            grind
          rw [post_eq]
          exact StepRunning.staticcallFail s gasArg toArg argsOff argsLen retOff retLen
            rest h_dec h_stack h_committed h_fail'
        · rename_i h_take
          split at h
          · rename_i h_fw
            cases h
            have h_take' : ¬ s.executionEnv.depth ≥ 1024 := by
              simpa [State.consumeGas, State.consumeMemExp2] using h_take
            have post_eq :
                (((s.consumeGas base h_gas).consumeMemExp2 argsOff.toNat argsLen.toNat
                  retOff.toNat retLen.toNat h_mem).consumeGas
                    (min gasArg.toNat (Gas.allButOneSixtyFourth s.fork
                      ((s.consumeGas base h_gas).consumeMemExp2 argsOff.toNat argsLen.toNat
                        retOff.toNat retLen.toNat h_mem).gasAvailable))
                    h_fw).enterCallFor
                  .StaticCall rest (AccountAddress.ofUInt256 toArg) ⟨0⟩
                  (MachineState.readPadded
                    (((s.consumeGas base h_gas).consumeMemExp2 argsOff.toNat argsLen.toNat
                      retOff.toNat retLen.toNat h_mem).consumeGas _ h_fw).memory
                    argsOff.toNat argsLen.toNat)
                  (((s.consumeGas base h_gas).consumeMemExp2 argsOff.toNat argsLen.toNat
                      retOff.toNat retLen.toNat h_mem).accountMap
                    (AccountAddress.ofUInt256 toArg)).code
                  (min gasArg.toNat (Gas.allButOneSixtyFourth s.fork
                    ((s.consumeGas base h_gas).consumeMemExp2 argsOff.toNat argsLen.toNat
                      retOff.toNat retLen.toNat h_mem).gasAvailable))
                  retOff.toNat retLen.toNat
                = (({ s with
                      gasAvailable := s.gasAvailable
                        - Gas.staticcallCommitted s argsOff argsLen retOff retLen
                        - (min gasArg.toNat (Gas.allButOneSixtyFourth s.fork
                            (s.gasAvailable
                              - Gas.staticcallCommitted s argsOff argsLen retOff retLen)))
                      activeWords := s.activeWordsAfterUInt256_2
                        argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat
                    } : State).enterCallFor .StaticCall rest
                      (AccountAddress.ofUInt256 toArg) ⟨0⟩
                      (MachineState.readPadded s.memory argsOff.toNat argsLen.toNat)
                      (s.accountMap (AccountAddress.ofUInt256 toArg)).code
                      (min gasArg.toNat (Gas.allButOneSixtyFourth s.fork
                        (s.gasAvailable
                          - Gas.staticcallCommitted s argsOff argsLen retOff retLen)))
                      retOff.toNat retLen.toNat) := by
              simp [State.enterCallFor, State.consumeGas, State.consumeMemExp2,
                    State.activeWordsAfterUInt256_2, Gas.staticcallCommitted,
                    MachineState.memExpansionDelta2,
                    show ∀ (a b : UInt256), a + b = a.add b from fun _ _ => rfl]
              grind
            rw [post_eq]
            exact StepRunning.staticcall s gasArg toArg argsOff argsLen retOff retLen
              rest _ h_dec h_stack h_committed h_take' rfl
          · nomatch h
      · simp [h_mem] at h
    | [], h                            => nomatch h
    | [_], h                           => nomatch h
    | [_, _], h                        => nomatch h
    | [_, _, _], h                     => nomatch h
    | [_, _, _, _], h                  => nomatch h
    | [_, _, _, _, _], h               => nomatch h
  | SELFDESTRUCT =>
    match h_stack : s.stack, h with
    | beneficiary :: rest, h =>
      -- Static-mode rejection short-circuits with `.error`, contradicting
      -- `h : … = .ok sf`. Otherwise the surcharge either fits (the
      -- `selfDestruct` rule fires) or runs out of gas (impossible).
      by_cases h_perm : ¬ s.executionEnv.permitStateMutation
      · simp [h_perm] at h
        unfold static at h; cases h
      · simp [h_perm] at h
        split at h
        · rename_i h_sc
          cases h
          have h_perm' : s.executionEnv.permitStateMutation = true := by
            simp at h_perm; exact h_perm
          set base := Gas.baseCost s.fork (.System .SELFDESTRUCT) with hbase
          set surch := Gas.selfDestructSurcharge s.fork
                        (s.accountMap (AccountAddress.ofUInt256 beneficiary)).isEmpty
                        ((s.accountMap s.executionEnv.address).balance.toNat != 0) with hsurch
          have h_total : Gas.selfDestructTotal s beneficiary ≤ s.gasAvailable := by
            show base + surch ≤ s.gasAvailable
            simp [State.consumeGas, ← hbase] at h_sc
            omega
          have post_eq :
              ((s.consumeGas base h_gas).consumeGas surch h_sc).selfDestructTo
                (AccountAddress.ofUInt256 beneficiary)
              = (({ s with gasAvailable := s.gasAvailable
                            - Gas.selfDestructTotal s beneficiary } : State).selfDestructTo
                  (AccountAddress.ofUInt256 beneficiary)) := by
            simp [State.consumeGas, State.selfDestructTo, Gas.selfDestructTotal]
            grind
          rw [post_eq]
          exact StepRunning.selfDestruct s beneficiary rest h_dec h_stack h_perm' h_total
        · nomatch h
    | [], h => nomatch h
  | CREATE =>
    match h_stack : s.stack, h with
    | value :: offset :: size :: rest, h =>
      by_cases h_perm : ¬ s.executionEnv.permitStateMutation
      · simp [h_perm] at h
        unfold static at h; cases h
      · simp [h_perm] at h
        have h_perm' : s.executionEnv.permitStateMutation = true := by
          simp at h_perm; exact h_perm
        unfold chargeMem at h
        by_cases h_mem :
            (s.consumeGas (Gas.baseCost s.fork (.System .CREATE)) h_gas).canExpandMemory
              offset.toNat size.toNat
        · simp only [h_mem, dif_pos] at h
          set base := Gas.baseCost s.fork (.System .CREATE) with hbase
          set md := MachineState.memCost
                      (MachineState.activeWordsAfter s.activeWords.toNat
                        offset.toNat size.toNat)
                    - MachineState.memCost s.activeWords.toNat with hmd
          have h_committed :
              Gas.createCommitted s offset size ≤ s.gasAvailable := by
            show base + md ≤ s.gasAvailable
            simp [State.canExpandMemory, State.consumeGas, MachineState.memExpansionDelta,
                  ← hbase, ← hmd] at h_mem
            omega
          split at h
          · rename_i h_fail
            cases h
            have h_fail' : s.executionEnv.depth ≥ 1024 ∨
                (s.accountMap s.executionEnv.address).balance < value := by
              simpa [State.consumeGas, State.consumeMemExp] using h_fail
            have post_eq :
                ({ (s.consumeGas base h_gas).consumeMemExp offset.toNat size.toNat
                    h_mem with
                    returnData := .empty }.replaceStackAndIncrPC (UInt256.ofNat 0 :: rest))
                = ({ s with
                    gasAvailable := s.gasAvailable - Gas.createCommitted s offset size
                    activeWords := s.activeWordsAfterUInt256 offset.toNat size.toNat
                    returnData := .empty
                    stack := UInt256.ofNat 0 :: rest
                    pc := s.pc.succ } : State) := by
              simp [State.consumeGas, State.consumeMemExp, State.replaceStackAndIncrPC,
                    State.activeWordsAfterUInt256, Gas.createCommitted,
                    UInt256.succ, MachineState.memExpansionDelta,
                    show ∀ (a b : UInt256), a + b = a.add b from fun _ _ => rfl]
              grind
            rw [post_eq]
            exact StepRunning.createFail s value offset size rest h_dec h_stack
              h_perm' h_committed h_fail'
          · rename_i h_take
            split at h
            · rename_i h_rlp_none; cases h
            · rename_i newAddr h_rlp
              split at h
              · rename_i h_fw
                have h_take' : ¬ (s.executionEnv.depth ≥ 1024 ∨
                    (s.accountMap s.executionEnv.address).balance < value) := by
                  simpa [State.consumeGas, State.consumeMemExp] using h_take
                have h_rlp' : EvmSemantics.createAddress s.executionEnv.address
                    (s.accountMap s.executionEnv.address).nonce.toNat = some newAddr := by
                  simpa [State.consumeGas, State.consumeMemExp] using h_rlp
                split at h
                · rename_i h_coll
                  cases h
                  have h_coll' : (s.accountMap newAddr).isContract = true := by
                    simpa [State.consumeGas, State.consumeMemExp] using h_coll
                  -- Bind the post-forward state to a local; the stepF output uses
                  -- this state's `accountMap`/`executionEnv` projections, which are
                  -- equal to `s`'s (since `consumeGas`/`consumeMemExp` leave them
                  -- untouched). `grind` handles the rest.
                  set s3 := ((s.consumeGas base h_gas).consumeMemExp offset.toNat size.toNat
                              h_mem).consumeGas
                              (Gas.allButOneSixtyFourth s.fork
                                ((s.consumeGas base h_gas).consumeMemExp
                                  offset.toNat size.toNat h_mem).gasAvailable) h_fw
                  have post_eq :
                      ({ s3 with
                          accountMap := s3.accountMap.set s3.executionEnv.address
                            { s3.accountMap s3.executionEnv.address with
                                nonce := (s3.accountMap s3.executionEnv.address).nonce
                                          + (⟨1⟩ : UInt256) }
                          returnData := .empty
                        }.replaceStackAndIncrPC (UInt256.ofNat 0 :: rest))
                      = ({ s with
                          gasAvailable := s.gasAvailable - Gas.createCommitted s offset size
                            - Gas.allButOneSixtyFourth s.fork
                                (s.gasAvailable - Gas.createCommitted s offset size)
                          activeWords := s.activeWordsAfterUInt256 offset.toNat size.toNat
                          accountMap := s.accountMap.set s.executionEnv.address
                            { s.accountMap s.executionEnv.address with
                                nonce := (s.accountMap s.executionEnv.address).nonce + ⟨1⟩ }
                          returnData := .empty
                          stack := UInt256.ofNat 0 :: rest
                          pc := s.pc.succ } : State) := by
                    simp [s3, State.consumeGas, State.consumeMemExp,
                          State.replaceStackAndIncrPC, State.activeWordsAfterUInt256,
                          Gas.createCommitted, UInt256.succ, MachineState.memExpansionDelta,
                          show ∀ (a b : UInt256), a + b = a.add b from fun _ _ => rfl]
                    grind
                  rw [post_eq]
                  exact StepRunning.createCollision s value offset size rest _ newAddr
                    h_dec h_stack h_perm' h_committed h_take' h_rlp' rfl h_coll'
                · rename_i h_nocoll
                  cases h
                  have h_nocoll' : (s.accountMap newAddr).isContract = false := by
                    simpa [State.consumeGas, State.consumeMemExp] using h_nocoll
                  have post_eq :
                      (((s.consumeGas base h_gas).consumeMemExp offset.toNat size.toNat
                        h_mem).consumeGas
                        (Gas.allButOneSixtyFourth s.fork ((s.consumeGas base h_gas).consumeMemExp
                          offset.toNat size.toNat h_mem).gasAvailable) h_fw).enterCreate
                        rest newAddr value
                        (MachineState.readPadded
                          (((s.consumeGas base h_gas).consumeMemExp offset.toNat size.toNat
                            h_mem).consumeGas _ h_fw).memory offset.toNat size.toNat)
                        (Gas.allButOneSixtyFourth s.fork ((s.consumeGas base h_gas).consumeMemExp
                          offset.toNat size.toNat h_mem).gasAvailable)
                      = (({ s with
                            gasAvailable := s.gasAvailable - Gas.createCommitted s offset size
                              - Gas.allButOneSixtyFourth s.fork
                                  (s.gasAvailable - Gas.createCommitted s offset size)
                            activeWords := s.activeWordsAfterUInt256 offset.toNat size.toNat
                          } : State).enterCreate rest newAddr value
                            (MachineState.readPadded s.memory offset.toNat size.toNat)
                            (Gas.allButOneSixtyFourth s.fork
                              (s.gasAvailable - Gas.createCommitted s offset size))) := by
                    simp [State.enterCreate, State.consumeGas, State.consumeMemExp,
                          State.activeWordsAfterUInt256, Gas.createCommitted,
                          MachineState.memExpansionDelta,
                          show ∀ (a b : UInt256), a + b = a.add b from fun _ _ => rfl]
                    grind
                  rw [post_eq]
                  exact StepRunning.create s value offset size rest _ newAddr
                    h_dec h_stack h_perm' h_committed h_take' h_rlp' rfl h_nocoll'
              · nomatch h
        · simp [h_mem] at h
    | [], h               => nomatch h
    | [_], h              => nomatch h
    | [_, _], h           => nomatch h
  | CREATE2 =>
    match h_stack : s.stack, h with
    | value :: offset :: size :: salt :: rest, h =>
      by_cases h_perm : ¬ s.executionEnv.permitStateMutation
      · simp [h_perm] at h
        unfold static at h; cases h
      · simp [h_perm] at h
        have h_perm' : s.executionEnv.permitStateMutation = true := by
          simp at h_perm; exact h_perm
        unfold chargeMem at h
        by_cases h_mem :
            (s.consumeGas (Gas.baseCost s.fork (.System .CREATE2)) h_gas).canExpandMemory
              offset.toNat size.toNat
        · simp only [h_mem, dif_pos] at h
          set base := Gas.baseCost s.fork (.System .CREATE2) with hbase
          set md := MachineState.memCost
                      (MachineState.activeWordsAfter s.activeWords.toNat
                        offset.toNat size.toNat)
                    - MachineState.memCost s.activeWords.toNat with hmd
          split at h
          · rename_i h_hash
            have h_committed :
                Gas.create2Committed s offset size ≤ s.gasAvailable := by
              show base + md + Gas.create2HashCost size.toNat ≤ s.gasAvailable
              simp [State.canExpandMemory, State.consumeGas, State.consumeMemExp,
                    MachineState.memExpansionDelta, ← hbase, ← hmd] at h_mem h_hash
              omega
            split at h
            · rename_i h_fail
              cases h
              have h_fail' : s.executionEnv.depth ≥ 1024 ∨
                  (s.accountMap s.executionEnv.address).balance < value := by
                simpa [State.consumeGas, State.consumeMemExp] using h_fail
              have post_eq :
                  ({ ((s.consumeGas base h_gas).consumeMemExp offset.toNat size.toNat
                      h_mem).consumeGas (Gas.create2HashCost size.toNat) h_hash with
                      returnData := .empty }.replaceStackAndIncrPC
                    (UInt256.ofNat 0 :: rest))
                  = ({ s with
                      gasAvailable := s.gasAvailable - Gas.create2Committed s offset size
                      activeWords := s.activeWordsAfterUInt256 offset.toNat size.toNat
                      returnData := .empty
                      stack := UInt256.ofNat 0 :: rest
                      pc := s.pc.succ } : State) := by
                simp [State.consumeGas, State.consumeMemExp, State.replaceStackAndIncrPC,
                      State.activeWordsAfterUInt256, Gas.create2Committed,
                      UInt256.succ, MachineState.memExpansionDelta,
                      show ∀ (a b : UInt256), a + b = a.add b from fun _ _ => rfl]
                grind
              rw [post_eq]
              exact StepRunning.create2Fail s value offset size salt rest h_dec h_stack
                h_perm' h_committed h_fail'
            · rename_i h_take
              split at h
              · rename_i h_fw
                have h_take' : ¬ (s.executionEnv.depth ≥ 1024 ∨
                    (s.accountMap s.executionEnv.address).balance < value) := by
                  simpa [State.consumeGas, State.consumeMemExp] using h_take
                set s3 := (((s.consumeGas base h_gas).consumeMemExp offset.toNat size.toNat
                            h_mem).consumeGas (Gas.create2HashCost size.toNat) h_hash
                          ).consumeGas
                            (Gas.allButOneSixtyFourth s.fork
                              (((s.consumeGas base h_gas).consumeMemExp offset.toNat
                                size.toNat h_mem).consumeGas
                                (Gas.create2HashCost size.toNat) h_hash).gasAvailable) h_fw
                split at h
                · rename_i h_coll
                  cases h
                  have h_coll' : (s.accountMap
                      (EvmSemantics.create2Address s.executionEnv.address salt
                        (MachineState.readPadded s.memory offset.toNat
                          size.toNat))).isContract = true := by
                    simpa [s3, State.consumeGas, State.consumeMemExp] using h_coll
                  have post_eq :
                      ({ s3 with
                          accountMap := s3.accountMap.set s3.executionEnv.address
                            { s3.accountMap s3.executionEnv.address with
                                nonce := (s3.accountMap s3.executionEnv.address).nonce
                                          + (⟨1⟩ : UInt256) }
                          returnData := .empty
                        }.replaceStackAndIncrPC (UInt256.ofNat 0 :: rest))
                      = ({ s with
                          gasAvailable := s.gasAvailable - Gas.create2Committed s offset size
                            - Gas.allButOneSixtyFourth s.fork
                                (s.gasAvailable - Gas.create2Committed s offset size)
                          activeWords := s.activeWordsAfterUInt256 offset.toNat size.toNat
                          accountMap := s.accountMap.set s.executionEnv.address
                            { s.accountMap s.executionEnv.address with
                                nonce := (s.accountMap s.executionEnv.address).nonce
                                          + (⟨1⟩ : UInt256) }
                          returnData := .empty
                          stack := UInt256.ofNat 0 :: rest
                          pc := s.pc.succ } : State) := by
                    simp [s3, State.consumeGas, State.consumeMemExp,
                          State.replaceStackAndIncrPC, State.activeWordsAfterUInt256,
                          Gas.create2Committed, UInt256.succ,
                          MachineState.memExpansionDelta,
                          show ∀ (a b : UInt256), a + b = a.add b from fun _ _ => rfl]
                    grind
                  rw [post_eq]
                  exact StepRunning.create2Collision s value offset size salt rest _
                    h_dec h_stack h_perm' h_committed h_take' rfl h_coll'
                · rename_i h_nocoll
                  cases h
                  have h_nocoll' : (s.accountMap
                      (EvmSemantics.create2Address s.executionEnv.address salt
                        (MachineState.readPadded s.memory offset.toNat
                          size.toNat))).isContract = false := by
                    simpa [s3, State.consumeGas, State.consumeMemExp] using h_nocoll
                  have post_eq :
                      s3.enterCreate rest
                        (EvmSemantics.create2Address s3.executionEnv.address salt
                          (MachineState.readPadded s3.memory offset.toNat size.toNat))
                        value
                        (MachineState.readPadded s3.memory offset.toNat size.toNat)
                        (Gas.allButOneSixtyFourth s.fork (((s.consumeGas base h_gas).consumeMemExp
                          offset.toNat size.toNat h_mem).consumeGas
                          (Gas.create2HashCost size.toNat) h_hash).gasAvailable)
                      = (({ s with
                            gasAvailable := s.gasAvailable - Gas.create2Committed s offset size
                              - Gas.allButOneSixtyFourth s.fork
                                  (s.gasAvailable - Gas.create2Committed s offset size)
                            activeWords := s.activeWordsAfterUInt256 offset.toNat size.toNat
                          } : State).enterCreate rest
                            (EvmSemantics.create2Address s.executionEnv.address salt
                              (MachineState.readPadded s.memory offset.toNat size.toNat))
                            value
                            (MachineState.readPadded s.memory offset.toNat size.toNat)
                            (Gas.allButOneSixtyFourth s.fork
                              (s.gasAvailable - Gas.create2Committed s offset size))) := by
                    simp [s3, State.enterCreate, State.consumeGas, State.consumeMemExp,
                          State.activeWordsAfterUInt256, Gas.create2Committed,
                          MachineState.memExpansionDelta,
                          show ∀ (a b : UInt256), a + b = a.add b from fun _ _ => rfl]
                    grind
                  rw [post_eq]
                  exact StepRunning.create2 s value offset size salt rest _
                    h_dec h_stack h_perm' h_committed h_take' rfl h_nocoll'
              · nomatch h
          · nomatch h
        · simp [h_mem] at h
    | [], h                  => nomatch h
    | [_], h                 => nomatch h
    | [_, _], h              => nomatch h
    | [_, _, _], h           => nomatch h

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
          set base := Gas.baseCost s.fork (.Env .CALLDATACOPY) with hbase
          set md := MachineState.memCost
                      (MachineState.activeWordsAfter s.activeWords.toNat dOff.toNat sz.toNat)
                    - MachineState.memCost s.activeWords.toNat with hmd
          have h_total : Gas.calldatacopyTotal s dOff sz ≤ s.gasAvailable := by
            show base + md + Gas.copyWordCost sz ≤ s.gasAvailable
            simp [State.canExpandMemory, State.consumeGas, State.consumeMemExp,
                  MachineState.memExpansionDelta, ← hbase, ← hmd] at h_mem h_dyn
            omega
          have post_eq :
              ({ ((s.consumeGas base h_gas).consumeMemExp dOff.toNat sz.toNat
                    h_mem).consumeGas (Gas.copyWordCost sz) h_dyn with
                  toMachineState :=
                    { (((s.consumeGas base h_gas).consumeMemExp dOff.toNat sz.toNat
                        h_mem).consumeGas (Gas.copyWordCost sz) h_dyn).toMachineState with
                      memory := MachineState.writeBytes s.memory
                                  (MachineState.readPadded s.executionEnv.calldata
                                    sOff.toNat sz.toNat) dOff.toNat }
                }.replaceStackAndIncrPC rest)
              = ({ s with
                  stack := rest
                  pc := s.pc.succ
                  gasAvailable := s.gasAvailable - Gas.calldatacopyTotal s dOff sz
                  memory := MachineState.writeBytes s.memory
                              (MachineState.readPadded s.executionEnv.calldata
                                sOff.toNat sz.toNat) dOff.toNat
                  activeWords := s.activeWordsAfterUInt256 dOff.toNat sz.toNat } : State) := by
            simp [State.consumeGas, State.consumeMemExp, State.replaceStackAndIncrPC,
                  State.activeWordsAfterUInt256, Gas.calldatacopyTotal, UInt256.succ,
                  MachineState.memExpansionDelta,
                  show ∀ (a b : UInt256), a + b = a.add b from fun _ _ => rfl]
            grind
          rw [post_eq]
          exact StepRunning.calldatacopy s dOff sOff sz rest h_dec h_stack h_total
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
          set base := Gas.baseCost s.fork (.Env .CODECOPY) with hbase
          set md := MachineState.memCost
                      (MachineState.activeWordsAfter s.activeWords.toNat dOff.toNat sz.toNat)
                    - MachineState.memCost s.activeWords.toNat with hmd
          have h_total : Gas.codecopyTotal s dOff sz ≤ s.gasAvailable := by
            show base + md + Gas.copyWordCost sz ≤ s.gasAvailable
            simp [State.canExpandMemory, State.consumeGas, State.consumeMemExp,
                  MachineState.memExpansionDelta, ← hbase, ← hmd] at h_mem h_dyn
            omega
          have post_eq :
              ({ ((s.consumeGas base h_gas).consumeMemExp dOff.toNat sz.toNat
                    h_mem).consumeGas (Gas.copyWordCost sz) h_dyn with
                  toMachineState :=
                    { (((s.consumeGas base h_gas).consumeMemExp dOff.toNat sz.toNat
                        h_mem).consumeGas (Gas.copyWordCost sz) h_dyn).toMachineState with
                      memory := MachineState.writeBytes s.memory
                                  (MachineState.readPadded s.executionEnv.code
                                    sOff.toNat sz.toNat) dOff.toNat }
                }.replaceStackAndIncrPC rest)
              = ({ s with
                  stack := rest
                  pc := s.pc.succ
                  gasAvailable := s.gasAvailable - Gas.codecopyTotal s dOff sz
                  memory := MachineState.writeBytes s.memory
                              (MachineState.readPadded s.executionEnv.code
                                sOff.toNat sz.toNat) dOff.toNat
                  activeWords := s.activeWordsAfterUInt256 dOff.toNat sz.toNat } : State) := by
            simp [State.consumeGas, State.consumeMemExp, State.replaceStackAndIncrPC,
                  State.activeWordsAfterUInt256, Gas.codecopyTotal, UInt256.succ,
                  MachineState.memExpansionDelta,
                  show ∀ (a b : UInt256), a + b = a.add b from fun _ _ => rfl]
            grind
          rw [post_eq]
          exact StepRunning.codecopy s dOff sOff sz rest h_dec h_stack h_total
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
          set base := Gas.baseCost s.fork (.Env .EXTCODECOPY) with hbase
          set md := MachineState.memCost
                      (MachineState.activeWordsAfter s.activeWords.toNat dOff.toNat sz.toNat)
                    - MachineState.memCost s.activeWords.toNat with hmd
          have h_total : Gas.extcodecopyTotal s dOff sz ≤ s.gasAvailable := by
            show base + md + Gas.copyWordCost sz ≤ s.gasAvailable
            simp [State.canExpandMemory, State.consumeGas, State.consumeMemExp,
                  MachineState.memExpansionDelta, ← hbase, ← hmd] at h_mem h_dyn
            omega
          have post_eq :
              ({ ((s.consumeGas base h_gas).consumeMemExp dOff.toNat sz.toNat
                    h_mem).consumeGas (Gas.copyWordCost sz) h_dyn with
                  toMachineState :=
                    { (((s.consumeGas base h_gas).consumeMemExp dOff.toNat sz.toNat
                        h_mem).consumeGas (Gas.copyWordCost sz) h_dyn).toMachineState with
                      memory := MachineState.writeBytes s.memory
                                  (MachineState.readPadded
                                    (s.accountMap (AccountAddress.ofUInt256 a)).code
                                    sOff.toNat sz.toNat) dOff.toNat }
                }.replaceStackAndIncrPC rest)
              = ({ s with
                  stack := rest
                  pc := s.pc.succ
                  gasAvailable := s.gasAvailable - Gas.extcodecopyTotal s dOff sz
                  memory := MachineState.writeBytes s.memory
                              (MachineState.readPadded
                                (s.accountMap (AccountAddress.ofUInt256 a)).code
                                sOff.toNat sz.toNat) dOff.toNat
                  activeWords := s.activeWordsAfterUInt256 dOff.toNat sz.toNat } : State) := by
            simp [State.consumeGas, State.consumeMemExp, State.replaceStackAndIncrPC,
                  State.activeWordsAfterUInt256, Gas.extcodecopyTotal, UInt256.succ,
                  MachineState.memExpansionDelta,
                  show ∀ (a b : UInt256), a + b = a.add b from fun _ _ => rfl]
            grind
          rw [post_eq]
          exact StepRunning.extcodecopy s a dOff sOff sz rest h_dec h_stack h_total
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
            set base := Gas.baseCost s.fork (.Env .RETURNDATACOPY) with hbase
            set md := MachineState.memCost
                        (MachineState.activeWordsAfter s.activeWords.toNat dOff.toNat sz.toNat)
                      - MachineState.memCost s.activeWords.toNat with hmd
            have h_total : Gas.returndatacopyTotal s dOff sz ≤ s.gasAvailable := by
              show base + md + Gas.copyWordCost sz ≤ s.gasAvailable
              simp [State.canExpandMemory, State.consumeGas, State.consumeMemExp,
                    MachineState.memExpansionDelta, ← hbase, ← hmd] at h_mem h_dyn
              omega
            have post_eq :
                ({ ((s.consumeGas base h_gas).consumeMemExp dOff.toNat sz.toNat
                      h_mem).consumeGas (Gas.copyWordCost sz) h_dyn with
                    toMachineState :=
                      { (((s.consumeGas base h_gas).consumeMemExp dOff.toNat sz.toNat
                          h_mem).consumeGas (Gas.copyWordCost sz) h_dyn).toMachineState with
                        memory := MachineState.writeBytes s.memory
                                    (MachineState.readPadded s.returnData
                                      sOff.toNat sz.toNat) dOff.toNat }
                  }.replaceStackAndIncrPC rest)
                = ({ s with
                    stack := rest
                    pc := s.pc.succ
                    gasAvailable := s.gasAvailable - Gas.returndatacopyTotal s dOff sz
                    memory := MachineState.writeBytes s.memory
                                (MachineState.readPadded s.returnData
                                  sOff.toNat sz.toNat) dOff.toNat
                    activeWords := s.activeWordsAfterUInt256 dOff.toNat sz.toNat } : State) := by
              simp [State.consumeGas, State.consumeMemExp, State.replaceStackAndIncrPC,
                    State.activeWordsAfterUInt256, Gas.returndatacopyTotal, UInt256.succ,
                    MachineState.memExpansionDelta,
                    show ∀ (a b : UInt256), a + b = a.add b from fun _ _ => rfl]
              grind
            rw [post_eq]
            exact StepRunning.returndatacopy s dOff sOff sz rest h_dec h_stack
              (Nat.le_of_not_lt h_oob) h_total
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
          set base := Gas.baseCost s.fork (.StackMemFlow .MLOAD) with hbase
          set md := MachineState.memCost
                      (MachineState.activeWordsAfter s.activeWords.toNat offset.toNat 32)
                    - MachineState.memCost s.activeWords.toNat with hmd
          have h_total : Gas.mloadTotal s offset ≤ s.gasAvailable := by
            show base + md ≤ s.gasAvailable
            simp [State.canExpandMemory, State.consumeGas,
                  MachineState.memExpansionDelta, ← hbase, ← hmd] at h_mem
            omega
          -- `MachineState.mload` reads the word from memory and returns it
          -- alongside the unchanged machine state (the activeWords update
          -- was done by `consumeMemExp`). From `h_load`, `v = readWord …`
          -- and `μ' = (consumeMemExp ...).toMachineState`.
          have hv : v = MachineState.readWord s.memory offset.toNat := by
            simp [MachineState.mload, State.consumeGas, State.consumeMemExp] at h_load
            exact h_load.1.symm
          have hμ' : μ' = ((s.consumeGas base h_gas).consumeMemExp offset.toNat 32
                            h_mem).toMachineState := by
            simp [MachineState.mload] at h_load
            exact h_load.2.symm
          have post_eq :
              ({ (s.consumeGas base h_gas).consumeMemExp offset.toNat 32 h_mem with
                  toMachineState := μ' }.replaceStackAndIncrPC (v :: rest))
              = ({ s with
                  stack := MachineState.readWord s.memory offset.toNat :: rest
                  pc := s.pc.succ
                  gasAvailable := s.gasAvailable - Gas.mloadTotal s offset
                  activeWords := s.activeWordsAfterUInt256 offset.toNat 32 } : State) := by
            subst hv; subst hμ'
            simp [State.consumeGas, State.consumeMemExp, State.replaceStackAndIncrPC,
                  State.activeWordsAfterUInt256, Gas.mloadTotal, UInt256.succ,
                  MachineState.memExpansionDelta,
                  show ∀ (a b : UInt256), a + b = a.add b from fun _ _ => rfl]
            grind
          rw [post_eq]
          exact StepRunning.mload s offset rest h_dec h_stack h_total
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
        set base := Gas.baseCost s.fork (.StackMemFlow .MSTORE) with hbase
        set md := MachineState.memCost
                    (MachineState.activeWordsAfter s.activeWords.toNat offset.toNat 32)
                  - MachineState.memCost s.activeWords.toNat with hmd
        have h_total : Gas.mstoreTotal s offset ≤ s.gasAvailable := by
          show base + md ≤ s.gasAvailable
          simp [State.canExpandMemory, State.consumeGas, MachineState.memExpansionDelta,
                ← hbase, ← hmd] at h_mem
          omega
        have post_eq :
            ({ (s.consumeGas base h_gas).consumeMemExp offset.toNat 32 h_mem with
                toMachineState := MachineState.mstore
                  ((s.consumeGas base h_gas).consumeMemExp offset.toNat 32 h_mem).toMachineState
                  offset value }.replaceStackAndIncrPC rest)
            = ({ s with
                stack := rest
                pc := s.pc.succ
                gasAvailable := s.gasAvailable - Gas.mstoreTotal s offset
                memory := MachineState.writeBytes s.memory
                            (MachineState.wordBytes value) offset.toNat
                activeWords := s.activeWordsAfterUInt256 offset.toNat 32 } : State) := by
          simp [State.consumeGas, State.consumeMemExp, State.replaceStackAndIncrPC,
                State.activeWordsAfterUInt256, Gas.mstoreTotal, UInt256.succ,
                MachineState.memExpansionDelta, MachineState.mstore,
                show ∀ (a b : UInt256), a + b = a.add b from fun _ _ => rfl]
          grind
        rw [post_eq]
        exact StepRunning.mstore s offset value rest h_dec h_stack h_total
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
        set base := Gas.baseCost s.fork (.StackMemFlow .MSTORE8) with hbase
        set md := MachineState.memCost
                    (MachineState.activeWordsAfter s.activeWords.toNat offset.toNat 1)
                  - MachineState.memCost s.activeWords.toNat with hmd
        have h_total : Gas.mstore8Total s offset ≤ s.gasAvailable := by
          show base + md ≤ s.gasAvailable
          simp [State.canExpandMemory, State.consumeGas, MachineState.memExpansionDelta,
                ← hbase, ← hmd] at h_mem
          omega
        have post_eq :
            ({ (s.consumeGas base h_gas).consumeMemExp offset.toNat 1 h_mem with
                toMachineState := MachineState.mstore8
                  ((s.consumeGas base h_gas).consumeMemExp offset.toNat 1 h_mem).toMachineState
                  offset value }.replaceStackAndIncrPC rest)
            = ({ s with
                stack := rest
                pc := s.pc.succ
                gasAvailable := s.gasAvailable - Gas.mstore8Total s offset
                memory := MachineState.writeBytes s.memory
                            (ByteArray.mk #[UInt8.ofNat (value.toNat % 256)]) offset.toNat
                activeWords := s.activeWordsAfterUInt256 offset.toNat 1 } : State) := by
          simp [State.consumeGas, State.consumeMemExp, State.replaceStackAndIncrPC,
                State.activeWordsAfterUInt256, Gas.mstore8Total, UInt256.succ,
                MachineState.memExpansionDelta, MachineState.mstore8,
                show ∀ (a b : UInt256), a + b = a.add b from fun _ _ => rfl]
          grind
        rw [post_eq]
        exact StepRunning.mstore8 s offset value rest h_dec h_stack h_total
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
                (s.substate.originalStorage s.executionEnv.address key)
                ((s.accountMap s.executionEnv.address).storage key) value
              ≤ (s.consumeGas (Gas.baseCost s.fork (.StackMemFlow .SSTORE))
                    h_gas).gasAvailable
          · simp [h_dyn] at h
            cases h
            set base := Gas.baseCost s.fork (.StackMemFlow .SSTORE) with hbase
            set dyn := Gas.sstoreCost s.fork
                        (s.substate.originalStorage s.executionEnv.address key)
                        ((s.accountMap s.executionEnv.address).storage key) value with hdyn
            have h_total : Gas.sstoreTotal s key value ≤ s.gasAvailable := by
              show base + dyn ≤ s.gasAvailable
              simp [State.consumeGas, ← hbase] at h_dyn
              omega
            have h_perm' : s.executionEnv.permitStateMutation = true := by
              simp at h_perm; exact h_perm
            let δ := Gas.sstoreRefund s.fork
                       (s.substate.originalStorage s.executionEnv.address key)
                       ((s.accountMap s.executionEnv.address).storage key) value
            let rb : Int := (s.substate.refundBalance.toNat : Int) + δ
            let sub' : Substate :=
              { s.substate with
                  refundBalance := UInt256.ofNat (if rb < 0 then 0 else rb.toNat) }
            have post_eq :
                ({ (s.consumeGas base h_gas).consumeGas dyn h_dyn with
                    accountMap := s.accountMap.set s.executionEnv.address
                      { s.accountMap s.executionEnv.address with
                          storage := (s.accountMap s.executionEnv.address).storage.set
                                       key value }
                    substate := sub' }.replaceStackAndIncrPC rest)
                = ({ s with
                    stack := rest
                    pc := s.pc.succ
                    gasAvailable := s.gasAvailable - Gas.sstoreTotal s key value
                    accountMap := s.accountMap.set s.executionEnv.address
                      { s.accountMap s.executionEnv.address with
                          storage := (s.accountMap s.executionEnv.address).storage.set
                                       key value }
                    substate := sub' } : State) := by
              simp [State.consumeGas, State.replaceStackAndIncrPC, Gas.sstoreTotal,
                    UInt256.succ,
                    show ∀ (a b : UInt256), a + b = a.add b from fun _ _ => rfl]
              grind
            rw [post_eq]
            exact StepRunning.sstore s key value rest h_dec h_perm' h_stack h_sentry h_total
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
          set base := Gas.baseCost s.fork (.StackMemFlow .MCOPY) with hbase
          set md := MachineState.memCost
                      (MachineState.activeWordsAfter
                        (MachineState.activeWordsAfter s.activeWords.toNat
                          dOff.toNat sz.toNat) sOff.toNat sz.toNat)
                    - MachineState.memCost s.activeWords.toNat with hmd
          have h_total : Gas.mcopyTotal s dOff sOff sz ≤ s.gasAvailable := by
            show base + md + Gas.copyWordCost sz ≤ s.gasAvailable
            simp [State.canExpandMemory2, State.consumeGas, State.consumeMemExp2,
                  MachineState.memExpansionDelta2, ← hbase, ← hmd] at h_mem h_dyn
            omega
          have post_eq :
              ({ ((s.consumeGas base h_gas).consumeMemExp2
                  dOff.toNat sz.toNat sOff.toNat sz.toNat h_mem).consumeGas
                  (Gas.copyWordCost sz) h_dyn with
                  toMachineState := MachineState.mcopy
                    (((s.consumeGas base h_gas).consumeMemExp2 dOff.toNat sz.toNat
                      sOff.toNat sz.toNat h_mem).consumeGas
                      (Gas.copyWordCost sz) h_dyn).toMachineState
                    dOff sOff sz }.replaceStackAndIncrPC rest)
              = ({ s with
                  stack := rest
                  pc := s.pc.succ
                  gasAvailable := s.gasAvailable - Gas.mcopyTotal s dOff sOff sz
                  memory := MachineState.writeBytes s.memory
                              (MachineState.readPadded s.memory sOff.toNat sz.toNat)
                              dOff.toNat
                  activeWords := s.activeWordsAfterUInt256_2
                                    dOff.toNat sz.toNat sOff.toNat sz.toNat } : State) := by
            simp [State.consumeGas, State.consumeMemExp2, State.replaceStackAndIncrPC,
                  State.activeWordsAfterUInt256_2, Gas.mcopyTotal, UInt256.succ,
                  MachineState.memExpansionDelta2, MachineState.mcopy,
                  show ∀ (a b : UInt256), a + b = a.add b from fun _ _ => rfl]
            grind
          rw [post_eq]
          exact StepRunning.mcopy s dOff sOff sz rest h_dec h_stack h_total
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
            set base := Gas.baseCost s.fork (.Log ⟨n⟩) with hbase
            set md := MachineState.memCost
                        (MachineState.activeWordsAfter s.activeWords.toNat
                          offset.toNat size.toNat)
                      - MachineState.memCost s.activeWords.toNat with hmd
            have h_total : Gas.logTotal s n offset size ≤ s.gasAvailable := by
              show base + md + Gas.logDataCost size ≤ s.gasAvailable
              simp [State.canExpandMemory, State.consumeGas, State.consumeMemExp,
                    MachineState.memExpansionDelta, ← hbase, ← hmd] at h_mem h_dyn
              omega
            have post_eq :
                ({ ((s.consumeGas base h_gas).consumeMemExp offset.toNat size.toNat
                      h_mem).consumeGas (Gas.logDataCost size) h_dyn with
                    substate := s.substate.appendLog
                      { address := s.executionEnv.address
                        topics := topics.toArray
                        data := MachineState.readPadded s.memory
                                  offset.toNat size.toNat }
                  }.replaceStackAndIncrPC rest')
                = ({ s with
                    stack := rest'
                    pc := s.pc.succ
                    gasAvailable := s.gasAvailable - Gas.logTotal s n offset size
                    activeWords := s.activeWordsAfterUInt256 offset.toNat size.toNat
                    substate := s.substate.appendLog
                      { address := s.executionEnv.address
                        topics := topics.toArray
                        data := MachineState.readPadded s.memory
                                  offset.toNat size.toNat } } : State) := by
              simp [State.consumeGas, State.consumeMemExp, State.replaceStackAndIncrPC,
                    State.activeWordsAfterUInt256, Gas.logTotal, UInt256.succ,
                    MachineState.memExpansionDelta,
                    show ∀ (a b : UInt256), a + b = a.add b from fun _ _ => rfl]
              grind
            rw [post_eq]
            exact StepRunning.log s n offset size topics rest' h_dec h_perm' h_len
              h_stack' h_total
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
  · -- `.Running`: ruled out by `h_nr`
    exact absurd ‹s.halt = .Running› h_nr
  · -- CALL-frame Success
    exact .callReturnSuccess s f rest (Or.inl ‹_›) h_stack ‹_›
  · -- CALL-frame Returned
    exact .callReturnSuccess s f rest (Or.inr ‹_›) h_stack ‹_›
  · -- CALL-frame Reverted
    exact .callReturnRevert s f rest ‹_› h_stack ‹_›
  · -- CALL-frame Exception
    exact .callReturnException s f rest _ ‹_› h_stack ‹_›
  · -- CREATE-frame Success
    exact .createReturnSuccess s f rest _ (Or.inl ‹_›) h_stack ‹_›
  · -- CREATE-frame Returned
    exact .createReturnSuccess s f rest _ (Or.inr ‹_›) h_stack ‹_›
  · -- CREATE-frame Reverted
    exact .createReturnRevert s f rest _ ‹_› h_stack ‹_›
  · -- CREATE-frame Exception
    exact .createReturnException s f rest _ _ ‹_› h_stack ‹_›

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
      -- Split on the stack-overflow check.
      split at h
      · -- overflow: would leave >1024 items on the stack
        nomatch h
      · -- no overflow; split on the gas check.
        split at h
        · -- gas ≥ cost
          rename_i h_gas
          -- Split on the operation kind.
          cases op with
          | StopArith op =>
            exact .running h_running
              (stepF.stopArith_sound s op (State.decoded_to_op h_dec) h_gas h)
          | CompBit op =>
            exact .running h_running
              (stepF.compBit_sound s op (State.decoded_to_op h_dec) h_gas h)
          | Keccak op =>
            exact .running h_running
              (stepF.keccak_sound s op (State.decoded_to_op h_dec) h_gas h)
          | Env op =>
            exact .running h_running
              (stepF.env_sound s op (State.decoded_to_op h_dec) h_gas h)
          | Block op =>
            exact .running h_running
              (stepF.block_sound s op (State.decoded_to_op h_dec) h_gas h)
          | StackMemFlow op =>
            exact .running h_running
              (stepF.stackMemFlow_sound s op (State.decoded_to_op h_dec) h_gas h)
          | Push op =>
            exact .running h_running (stepF.push_sound s op argOpt h_dec h_gas h)
          | Dup op =>
            exact .running h_running
              (stepF.dup_sound s op (State.decoded_to_op h_dec) h_gas h)
          | Swap op =>
            exact .running h_running
              (stepF.swap_sound s op (State.decoded_to_op h_dec) h_gas h)
          | DupN op =>
            exact .running h_running
              (stepF.dupN_sound s op (State.decoded_to_op h_dec) h_gas h)
          | SwapN op =>
            exact .running h_running
              (stepF.swapN_sound s op (State.decoded_to_op h_dec) h_gas h)
          | Exchange op =>
            exact .running h_running
              (stepF.exchange_sound s op (State.decoded_to_op h_dec) h_gas h)
          | Log op =>
            exact .running h_running
              (stepF.log_sound s op (State.decoded_to_op h_dec) h_gas h)
          | System op =>
            exact .running h_running
              (stepF.system_sound s op (State.decoded_to_op h_dec) h_gas h)
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
