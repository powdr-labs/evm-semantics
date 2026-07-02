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
   `base` and `memDelta` and avoid the `s.fork` / `s.executionEnv.fork`
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
                  (Gas.callTargetIsNew s.fork
                    ((s.consumeGas base h_gas).consumeMemExp2 argsOff.toNat argsLen.toNat
                      retOff.toNat retLen.toNat h_mem).accountMap
                    (AccountAddress.ofUInt256 toArg))
                  + Gas.accountColdSurcharge s (AccountAddress.ofUInt256 toArg) with hsurch
            have h_surch_eq : surch = Gas.callSurcharge s.fork (value.toNat != 0)
                (Gas.callTargetIsNew s.fork s.accountMap
                  (AccountAddress.ofUInt256 toArg))
                + Gas.accountColdSurcharge s (AccountAddress.ofUInt256 toArg) := by
              simp [hsurch, State.consumeGas, State.consumeMemExp2]
            have h_committed :
                Gas.callCommitted s value argsOff argsLen retOff retLen toArg
                ≤ s.gasAvailable := by
              show base + md + (Gas.callSurcharge s.fork (value.toNat != 0)
                    (Gas.callTargetIsNew s.fork s.accountMap
                      (AccountAddress.ofUInt256 toArg))
                    + Gas.accountColdSurcharge s (AccountAddress.ofUInt256 toArg))
                  ≤ s.gasAvailable
              rw [← h_surch_eq]
              simp [State.canExpandMemory2, State.consumeGas, State.consumeMemExp2,
                    MachineState.memExpansionDelta2, ← hbase, ← hmd] at h_mem h_sc
              omega
            split at h
            · rename_i h_fw
              -- forwarded OK: split on depth/balance to hit silent-fail vs
              -- successful-call.
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
                have h_afford :
                    Gas.forwardGas s.executionEnv.fork
                        (s.gasAvailable
                          - Gas.callCommitted s value argsOff argsLen retOff retLen toArg)
                        gasArg.toNat
                      ≤ s.gasAvailable
                        - Gas.callCommitted s value argsOff argsLen retOff retLen toArg := by
                  -- `set s3 := …` above rewrote `h_fw` to reference `s3`;
                  -- unfold it with `hs3` before rewriting the surch/consume
                  -- chain, mirroring the take-branch derivation below.
                  have h := h_fw
                  simp only [hs3, State.consumeGas, State.consumeMemExp2] at h
                  show Gas.forwardGas s.fork _ _ ≤ _
                  rw [show (s.gasAvailable -
                              Gas.callCommitted s value argsOff argsLen retOff retLen toArg)
                          = s.gasAvailable - base - md - surch from by
                        show _ = _
                        rw [show Gas.callCommitted s value argsOff argsLen retOff retLen toArg
                                  = base + md + surch from by
                              simp [Gas.callCommitted, ← hbase, ← hmd, ← h_surch_eq,
                                    MachineState.memExpansionDelta2]]
                        omega]
                  exact h
                exact StepRunning.callFail s gasArg toArg value argsOff argsLen retOff retLen
                  rest h_dec h_stack h_committed h_afford h_fail'
              · rename_i h_take
                cases h
                have h_take' : ¬ (s.executionEnv.depth ≥ 1024 ∨
                    (s.accountMap s.executionEnv.address).balance < value) := by
                  simpa [State.consumeGas, State.consumeMemExp2] using h_take
                have post_eq :
                    ((((s.consumeGas base h_gas).consumeMemExp2 argsOff.toNat argsLen.toNat
                        retOff.toNat retLen.toNat h_mem).consumeGas surch h_sc).consumeGas
                        (Gas.forwardGas s.fork
                          (((s.consumeGas base h_gas).consumeMemExp2 argsOff.toNat
                              argsLen.toNat retOff.toNat retLen.toNat h_mem).consumeGas
                            surch h_sc).gasAvailable gasArg.toNat) h_fw).enterCall
                      rest (AccountAddress.ofUInt256 toArg) (AccountAddress.ofUInt256 toArg)
                      value
                      (MachineState.readPadded
                        ((((s.consumeGas base h_gas).consumeMemExp2 argsOff.toNat
                          argsLen.toNat retOff.toNat retLen.toNat h_mem).consumeGas surch
                            h_sc).consumeGas _ h_fw).memory
                        argsOff.toNat argsLen.toNat)
                      (((s.consumeGas base h_gas).consumeMemExp2 argsOff.toNat argsLen.toNat
                          retOff.toNat retLen.toNat h_mem).accountMap
                        (AccountAddress.ofUInt256 toArg)).code
                      (Gas.forwardGas s.fork
                        (((s.consumeGas base h_gas).consumeMemExp2 argsOff.toNat
                          argsLen.toNat retOff.toNat retLen.toNat h_mem).consumeGas
                            surch h_sc).gasAvailable gasArg.toNat
                        + (bif (value.toNat != 0) then Gas.callStipend else 0))
                      retOff.toNat retLen.toNat
                    = (({ s with
                          gasAvailable := s.gasAvailable
                            - Gas.callCommitted s value argsOff argsLen retOff retLen toArg
                            - Gas.forwardGas s.fork
                                (s.gasAvailable
                                 - Gas.callCommitted s value argsOff argsLen retOff retLen
                                   toArg) gasArg.toNat
                          activeWords := s.activeWordsAfterUInt256_2
                            argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat
                        } : State).enterCall rest (AccountAddress.ofUInt256 toArg)
                          (AccountAddress.ofUInt256 toArg) value
                          (MachineState.readPadded s.memory argsOff.toNat argsLen.toNat)
                          (s.accountMap (AccountAddress.ofUInt256 toArg)).code
                          (Gas.forwardGas s.fork
                              (s.gasAvailable
                               - Gas.callCommitted s value argsOff argsLen retOff retLen
                                 toArg) gasArg.toNat
                            + (bif (value.toNat != 0) then Gas.callStipend else 0))
                          retOff.toNat retLen.toNat) := by
                  simp [State.enterCall, State.consumeGas, State.consumeMemExp2,
                        State.activeWordsAfterUInt256_2, Gas.callCommitted,
                        MachineState.memExpansionDelta2,
                        show ∀ (a b : UInt256), a + b = a.add b from fun _ _ => rfl]
                  grind
                rw [post_eq]
                have h_afford :
                    Gas.forwardGas s.executionEnv.fork
                        (s.gasAvailable
                          - Gas.callCommitted s value argsOff argsLen retOff retLen toArg)
                        gasArg.toNat
                      ≤ s.gasAvailable
                        - Gas.callCommitted s value argsOff argsLen retOff retLen toArg := by
                  have h := h_fw
                  simp only [State.consumeGas, State.consumeMemExp2,
                             ← h_surch_eq] at h
                  show Gas.forwardGas s.fork _ _ ≤ _
                  rw [show (s.gasAvailable -
                              Gas.callCommitted s value argsOff argsLen retOff retLen toArg)
                          = s.gasAvailable - base - md - surch from by
                        show _ = _
                        rw [show Gas.callCommitted s value argsOff argsLen retOff retLen toArg
                                  = base + md + surch from by
                              simp [Gas.callCommitted, ← hbase, ← hmd, ← h_surch_eq,
                                    MachineState.memExpansionDelta2]]
                        omega]
                  exact h
                exact StepRunning.call s gasArg toArg value argsOff argsLen retOff retLen
                  rest _ h_dec h_stack h_committed h_take' rfl h_afford
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
              Gas.callcodeCommitted s value argsOff argsLen retOff retLen toArg
                ≤ s.gasAvailable := by
            show base + md + (Gas.callSurcharge s.fork (value.toNat != 0) false
                  + Gas.accountColdSurcharge s (AccountAddress.ofUInt256 toArg))
                ≤ s.gasAvailable
            simp [State.canExpandMemory2, State.consumeGas, State.consumeMemExp2,
                  MachineState.memExpansionDelta2, Gas.callSurcharge, Bool.and_false,
                  ← hbase, ← hmd] at h_mem h_sc
            simp [Gas.callSurcharge, Bool.and_false]
            omega
          split at h
          · rename_i h_fw
            split at h
            · rename_i h_fail
              cases h
              have h_fail' : s.executionEnv.depth ≥ 1024 ∨
                  (s.accountMap s.executionEnv.address).balance < value := by
                simpa [State.consumeGas, State.consumeMemExp2] using h_fail
              -- LHS-after-replaceStackAndIncrPC, in two pieces.
              set s3 := ((s.consumeGas base h_gas).consumeMemExp2 argsOff.toNat argsLen.toNat
                          retOff.toNat retLen.toNat h_mem).consumeGas
                          ((Gas.callSurcharge s.fork (value.toNat != 0) false
                  + Gas.accountColdSurcharge s (AccountAddress.ofUInt256 toArg))) h_sc with hs3
              have post_eq :
                  ({ (if (value.toNat != 0) then
                        { s3 with gasAvailable := s3.gasAvailable + Gas.callStipend }
                      else s3) with
                      returnData := .empty }.replaceStackAndIncrPC (UInt256.ofNat 0 :: rest))
                  = ({ s with
                      gasAvailable := s.gasAvailable
                        - Gas.callcodeCommitted s value argsOff argsLen retOff retLen toArg
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
              have h_afford :
                  Gas.forwardGas s.executionEnv.fork
                      (s.gasAvailable
                        - Gas.callcodeCommitted s value argsOff argsLen retOff retLen toArg)
                      gasArg.toNat
                    ≤ s.gasAvailable
                      - Gas.callcodeCommitted s value argsOff argsLen retOff retLen toArg := by
                -- `set s3 := …` above rewrote `h_fw` to reference `s3`;
                -- unfold via `hs3` before the consume-chain simp — same
                -- pattern as `.CALL` above.
                have h := h_fw
                simp only [hs3, State.consumeGas, State.consumeMemExp2] at h
                show Gas.forwardGas s.fork _ _ ≤ _
                have eq : (s.gasAvailable
                            - Gas.callcodeCommitted s value argsOff argsLen retOff retLen toArg)
                        = s.gasAvailable - base - md
                          - (Gas.callSurcharge s.fork (value.toNat != 0) false
                  + Gas.accountColdSurcharge s (AccountAddress.ofUInt256 toArg)) := by
                  show _ = _
                  rw [show Gas.callcodeCommitted s value argsOff argsLen retOff retLen toArg
                          = base + md + (Gas.callSurcharge s.fork (value.toNat != 0) false
                  + Gas.accountColdSurcharge s (AccountAddress.ofUInt256 toArg)) from
                        rfl]
                  omega
                rw [eq]
                exact h
              exact StepRunning.callcodeFail s gasArg toArg value argsOff argsLen retOff retLen
                rest h_dec h_stack h_committed h_afford h_fail'
            · rename_i h_take
              cases h
              have h_take' : ¬ (s.executionEnv.depth ≥ 1024 ∨
                  (s.accountMap s.executionEnv.address).balance < value) := by
                simpa [State.consumeGas, State.consumeMemExp2] using h_take
              have post_eq :
                  ((((s.consumeGas base h_gas).consumeMemExp2 argsOff.toNat argsLen.toNat
                      retOff.toNat retLen.toNat h_mem).consumeGas
                      ((Gas.callSurcharge s.fork (value.toNat != 0) false
                  + Gas.accountColdSurcharge s (AccountAddress.ofUInt256 toArg))) h_sc).consumeGas
                      (Gas.forwardGas s.fork
                        ((((s.consumeGas base h_gas).consumeMemExp2 argsOff.toNat
                          argsLen.toNat retOff.toNat retLen.toNat h_mem).consumeGas
                          ((Gas.callSurcharge s.fork (value.toNat != 0) false
                  + Gas.accountColdSurcharge s (AccountAddress.ofUInt256 toArg)))
                          h_sc).gasAvailable) gasArg.toNat)
                      h_fw).enterCall rest
                    (((((s.consumeGas base h_gas).consumeMemExp2 argsOff.toNat
                        argsLen.toNat retOff.toNat retLen.toNat h_mem).consumeGas
                        ((Gas.callSurcharge s.fork (value.toNat != 0) false
                  + Gas.accountColdSurcharge s (AccountAddress.ofUInt256 toArg))) h_sc).consumeGas
                        _ h_fw).executionEnv.address)
                    (AccountAddress.ofUInt256 toArg)
                    value
                    (MachineState.readPadded
                      ((((s.consumeGas base h_gas).consumeMemExp2 argsOff.toNat
                        argsLen.toNat retOff.toNat retLen.toNat h_mem).consumeGas
                        ((Gas.callSurcharge s.fork (value.toNat != 0) false
                  + Gas.accountColdSurcharge s (AccountAddress.ofUInt256 toArg))) h_sc).consumeGas
                        _ h_fw).memory argsOff.toNat argsLen.toNat)
                    (((s.consumeGas base h_gas).consumeMemExp2 argsOff.toNat argsLen.toNat
                        retOff.toNat retLen.toNat h_mem).accountMap
                      (AccountAddress.ofUInt256 toArg)).code
                    (Gas.forwardGas s.fork
                      ((((s.consumeGas base h_gas).consumeMemExp2 argsOff.toNat
                        argsLen.toNat retOff.toNat retLen.toNat h_mem).consumeGas
                        ((Gas.callSurcharge s.fork (value.toNat != 0) false
                  + Gas.accountColdSurcharge s (AccountAddress.ofUInt256 toArg)))
                        h_sc).gasAvailable) gasArg.toNat
                      + (bif (value.toNat != 0) then Gas.callStipend else 0))
                    retOff.toNat retLen.toNat
                  = (({ s with
                        gasAvailable := s.gasAvailable
                          - Gas.callcodeCommitted s value argsOff argsLen retOff retLen toArg
                          - Gas.forwardGas s.fork
                              (s.gasAvailable
                               - Gas.callcodeCommitted s value argsOff argsLen retOff retLen toArg)
                              gasArg.toNat
                        activeWords := s.activeWordsAfterUInt256_2
                          argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat
                      } : State).enterCall rest s.executionEnv.address
                        (AccountAddress.ofUInt256 toArg) value
                        (MachineState.readPadded s.memory argsOff.toNat argsLen.toNat)
                        (s.accountMap (AccountAddress.ofUInt256 toArg)).code
                        (Gas.forwardGas s.fork
                            (s.gasAvailable
                             - Gas.callcodeCommitted s value argsOff argsLen retOff retLen toArg)
                            gasArg.toNat
                          + (bif (value.toNat != 0) then Gas.callStipend else 0))
                        retOff.toNat retLen.toNat) := by
                simp [State.enterCall, State.consumeGas, State.consumeMemExp2,
                      State.activeWordsAfterUInt256_2, Gas.callcodeCommitted,
                      MachineState.memExpansionDelta2,
                      show ∀ (a b : UInt256), a + b = a.add b from fun _ _ => rfl]
                grind
              rw [post_eq]
              have h_afford :
                  Gas.forwardGas s.executionEnv.fork
                      (s.gasAvailable
                        - Gas.callcodeCommitted s value argsOff argsLen retOff retLen toArg)
                      gasArg.toNat
                    ≤ s.gasAvailable
                      - Gas.callcodeCommitted s value argsOff argsLen retOff retLen toArg := by
                have h := h_fw
                simp only [State.consumeGas, State.consumeMemExp2] at h
                show Gas.forwardGas s.fork _ _ ≤ _
                have eq : (s.gasAvailable
                            - Gas.callcodeCommitted s value argsOff argsLen retOff retLen toArg)
                        = s.gasAvailable - base - md
                          - (Gas.callSurcharge s.fork (value.toNat != 0) false
                  + Gas.accountColdSurcharge s (AccountAddress.ofUInt256 toArg)) := by
                  show _ = _
                  rw [show Gas.callcodeCommitted s value argsOff argsLen retOff retLen toArg
                          = base + md + (Gas.callSurcharge s.fork (value.toNat != 0) false
                  + Gas.accountColdSurcharge s (AccountAddress.ofUInt256 toArg)) from
                        rfl]
                  omega
                rw [eq]
                exact h
              exact StepRunning.callcode s gasArg toArg value argsOff argsLen retOff retLen
                rest _ h_dec h_stack h_committed h_take' rfl h_afford
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
        split at h
        · rename_i h_cs
          set cold := Gas.accountColdSurcharge s (AccountAddress.ofUInt256 toArg) with hcold
          have h_committed :
              Gas.delegatecallCommitted s argsOff argsLen retOff retLen toArg
                ≤ s.gasAvailable := by
            show base + md + cold ≤ s.gasAvailable
            simp [State.canExpandMemory2, State.consumeGas, State.consumeMemExp2,
                  MachineState.memExpansionDelta2, ← hbase, ← hmd] at h_mem h_cs
            omega
          split at h
          · rename_i h_fw
            split at h
            · rename_i h_fail
              cases h
              have h_fail' : s.executionEnv.depth ≥ 1024 := by
                simpa [State.consumeGas, State.consumeMemExp2] using h_fail
              have post_eq :
                  ({ (((s.consumeGas base h_gas).consumeMemExp2 argsOff.toNat argsLen.toNat
                      retOff.toNat retLen.toNat h_mem).consumeGas cold h_cs) with
                      returnData := .empty }.replaceStackAndIncrPC (UInt256.ofNat 0 :: rest))
                  = ({ s with
                        gasAvailable := s.gasAvailable
                          - Gas.delegatecallCommitted s argsOff argsLen retOff retLen toArg
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
              have h_afford :
                  Gas.forwardGas s.executionEnv.fork
                      (s.gasAvailable
                        - Gas.delegatecallCommitted s argsOff argsLen retOff retLen toArg)
                      gasArg.toNat
                    ≤ s.gasAvailable
                      - Gas.delegatecallCommitted s argsOff argsLen retOff retLen toArg := by
                have h := h_fw
                simp only [State.consumeGas, State.consumeMemExp2] at h
                show Gas.forwardGas s.fork _ _ ≤ _
                have eq : (s.gasAvailable
                            - Gas.delegatecallCommitted s argsOff argsLen retOff retLen toArg)
                        = s.gasAvailable - base - md - cold := by
                  show _ = _
                  rw [show Gas.delegatecallCommitted s argsOff argsLen retOff retLen toArg
                          = base + md + cold from rfl]
                  omega
                rw [eq]
                exact h
              exact StepRunning.delegatecallFail s gasArg toArg argsOff argsLen retOff retLen
                rest h_dec h_stack h_committed h_afford h_fail'
            · rename_i h_take
              cases h
              have h_take' : ¬ s.executionEnv.depth ≥ 1024 := by
                simpa [State.consumeGas, State.consumeMemExp2] using h_take
              have post_eq :
                  ((((s.consumeGas base h_gas).consumeMemExp2 argsOff.toNat argsLen.toNat
                    retOff.toNat retLen.toNat h_mem).consumeGas cold h_cs).consumeGas
                      (Gas.forwardGas s.fork
                        (((s.consumeGas base h_gas).consumeMemExp2 argsOff.toNat argsLen.toNat
                          retOff.toNat retLen.toNat h_mem).consumeGas cold h_cs).gasAvailable
                          gasArg.toNat)
                      h_fw).enterCallFor
                    .DelegateCall rest (AccountAddress.ofUInt256 toArg) ⟨0⟩
                    (MachineState.readPadded
                      ((((s.consumeGas base h_gas).consumeMemExp2 argsOff.toNat argsLen.toNat
                        retOff.toNat retLen.toNat h_mem).consumeGas cold h_cs).consumeGas
                          _ h_fw).memory
                      argsOff.toNat argsLen.toNat)
                    (((s.consumeGas base h_gas).consumeMemExp2 argsOff.toNat argsLen.toNat
                        retOff.toNat retLen.toNat h_mem).accountMap
                      (AccountAddress.ofUInt256 toArg)).code
                    (Gas.forwardGas s.fork
                      (((s.consumeGas base h_gas).consumeMemExp2 argsOff.toNat argsLen.toNat
                        retOff.toNat retLen.toNat h_mem).consumeGas cold h_cs).gasAvailable
                        gasArg.toNat)
                    retOff.toNat retLen.toNat
                  = (({ s with
                        gasAvailable := s.gasAvailable
                          - Gas.delegatecallCommitted s argsOff argsLen retOff retLen toArg
                          - Gas.forwardGas s.fork
                              (s.gasAvailable
                                - Gas.delegatecallCommitted s argsOff argsLen retOff retLen
                                  toArg)
                              gasArg.toNat
                        activeWords := s.activeWordsAfterUInt256_2
                          argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat
                      } : State).enterCallFor .DelegateCall rest
                        (AccountAddress.ofUInt256 toArg) ⟨0⟩
                        (MachineState.readPadded s.memory argsOff.toNat argsLen.toNat)
                        (s.accountMap (AccountAddress.ofUInt256 toArg)).code
                        (Gas.forwardGas s.fork
                          (s.gasAvailable
                            - Gas.delegatecallCommitted s argsOff argsLen retOff retLen toArg)
                          gasArg.toNat)
                        retOff.toNat retLen.toNat) := by
                simp [State.enterCallFor, State.consumeGas, State.consumeMemExp2,
                      State.activeWordsAfterUInt256_2, Gas.delegatecallCommitted,
                      MachineState.memExpansionDelta2,
                      show ∀ (a b : UInt256), a + b = a.add b from fun _ _ => rfl]
                grind
              rw [post_eq]
              have h_afford :
                  Gas.forwardGas s.executionEnv.fork
                      (s.gasAvailable
                        - Gas.delegatecallCommitted s argsOff argsLen retOff retLen toArg)
                      gasArg.toNat
                    ≤ s.gasAvailable
                      - Gas.delegatecallCommitted s argsOff argsLen retOff retLen toArg := by
                have h := h_fw
                simp only [State.consumeGas, State.consumeMemExp2] at h
                show Gas.forwardGas s.fork _ _ ≤ _
                have eq : (s.gasAvailable
                            - Gas.delegatecallCommitted s argsOff argsLen retOff retLen toArg)
                        = s.gasAvailable - base - md - cold := by
                  show _ = _
                  rw [show Gas.delegatecallCommitted s argsOff argsLen retOff retLen toArg
                          = base + md + cold from rfl]
                  omega
                rw [eq]
                exact h
              exact StepRunning.delegatecall s gasArg toArg argsOff argsLen retOff retLen
                rest _ h_dec h_stack h_committed h_take' rfl h_afford
          · nomatch h
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
        split at h
        · rename_i h_cs
          set cold := Gas.accountColdSurcharge s (AccountAddress.ofUInt256 toArg) with hcold
          have h_committed :
              Gas.staticcallCommitted s argsOff argsLen retOff retLen toArg
                ≤ s.gasAvailable := by
            show base + md + cold ≤ s.gasAvailable
            simp [State.canExpandMemory2, State.consumeGas, State.consumeMemExp2,
                  MachineState.memExpansionDelta2, ← hbase, ← hmd] at h_mem h_cs
            omega
          split at h
          · rename_i h_fw
            split at h
            · rename_i h_fail
              cases h
              have h_fail' : s.executionEnv.depth ≥ 1024 := by
                simpa [State.consumeGas, State.consumeMemExp2] using h_fail
              have post_eq :
                  ({ (((s.consumeGas base h_gas).consumeMemExp2 argsOff.toNat argsLen.toNat
                      retOff.toNat retLen.toNat h_mem).consumeGas cold h_cs) with
                      returnData := .empty }.replaceStackAndIncrPC (UInt256.ofNat 0 :: rest))
                  = ({ s with
                        gasAvailable := s.gasAvailable
                          - Gas.staticcallCommitted s argsOff argsLen retOff retLen toArg
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
              have h_afford :
                  Gas.forwardGas s.executionEnv.fork
                      (s.gasAvailable
                        - Gas.staticcallCommitted s argsOff argsLen retOff retLen toArg)
                      gasArg.toNat
                    ≤ s.gasAvailable
                      - Gas.staticcallCommitted s argsOff argsLen retOff retLen toArg := by
                have h := h_fw
                simp only [State.consumeGas, State.consumeMemExp2] at h
                show Gas.forwardGas s.fork _ _ ≤ _
                have eq : (s.gasAvailable
                            - Gas.staticcallCommitted s argsOff argsLen retOff retLen toArg)
                        = s.gasAvailable - base - md - cold := by
                  show _ = _
                  rw [show Gas.staticcallCommitted s argsOff argsLen retOff retLen toArg
                          = base + md + cold from rfl]
                  omega
                rw [eq]
                exact h
              exact StepRunning.staticcallFail s gasArg toArg argsOff argsLen retOff retLen
                rest h_dec h_stack h_committed h_afford h_fail'
            · rename_i h_take
              cases h
              have h_take' : ¬ s.executionEnv.depth ≥ 1024 := by
                simpa [State.consumeGas, State.consumeMemExp2] using h_take
              have post_eq :
                  ((((s.consumeGas base h_gas).consumeMemExp2 argsOff.toNat argsLen.toNat
                    retOff.toNat retLen.toNat h_mem).consumeGas cold h_cs).consumeGas
                      (Gas.forwardGas s.fork
                        (((s.consumeGas base h_gas).consumeMemExp2 argsOff.toNat argsLen.toNat
                          retOff.toNat retLen.toNat h_mem).consumeGas cold h_cs).gasAvailable
                          gasArg.toNat)
                      h_fw).enterCallFor
                    .StaticCall rest (AccountAddress.ofUInt256 toArg) ⟨0⟩
                    (MachineState.readPadded
                      ((((s.consumeGas base h_gas).consumeMemExp2 argsOff.toNat argsLen.toNat
                        retOff.toNat retLen.toNat h_mem).consumeGas cold h_cs).consumeGas
                          _ h_fw).memory
                      argsOff.toNat argsLen.toNat)
                    (((s.consumeGas base h_gas).consumeMemExp2 argsOff.toNat argsLen.toNat
                        retOff.toNat retLen.toNat h_mem).accountMap
                      (AccountAddress.ofUInt256 toArg)).code
                    (Gas.forwardGas s.fork
                      (((s.consumeGas base h_gas).consumeMemExp2 argsOff.toNat argsLen.toNat
                        retOff.toNat retLen.toNat h_mem).consumeGas cold h_cs).gasAvailable
                        gasArg.toNat)
                    retOff.toNat retLen.toNat
                  = (({ s with
                        gasAvailable := s.gasAvailable
                          - Gas.staticcallCommitted s argsOff argsLen retOff retLen toArg
                          - Gas.forwardGas s.fork
                              (s.gasAvailable
                                - Gas.staticcallCommitted s argsOff argsLen retOff retLen
                                  toArg)
                              gasArg.toNat
                        activeWords := s.activeWordsAfterUInt256_2
                          argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat
                      } : State).enterCallFor .StaticCall rest
                        (AccountAddress.ofUInt256 toArg) ⟨0⟩
                        (MachineState.readPadded s.memory argsOff.toNat argsLen.toNat)
                        (s.accountMap (AccountAddress.ofUInt256 toArg)).code
                        (Gas.forwardGas s.fork
                          (s.gasAvailable
                            - Gas.staticcallCommitted s argsOff argsLen retOff retLen toArg)
                          gasArg.toNat)
                        retOff.toNat retLen.toNat) := by
                simp [State.enterCallFor, State.consumeGas, State.consumeMemExp2,
                      State.activeWordsAfterUInt256_2, Gas.staticcallCommitted,
                      MachineState.memExpansionDelta2,
                      show ∀ (a b : UInt256), a + b = a.add b from fun _ _ => rfl]
                grind
              rw [post_eq]
              have h_afford :
                  Gas.forwardGas s.executionEnv.fork
                      (s.gasAvailable
                        - Gas.staticcallCommitted s argsOff argsLen retOff retLen toArg)
                      gasArg.toNat
                    ≤ s.gasAvailable
                      - Gas.staticcallCommitted s argsOff argsLen retOff retLen toArg := by
                have h := h_fw
                simp only [State.consumeGas, State.consumeMemExp2] at h
                show Gas.forwardGas s.fork _ _ ≤ _
                have eq : (s.gasAvailable
                            - Gas.staticcallCommitted s argsOff argsLen retOff retLen toArg)
                        = s.gasAvailable - base - md - cold := by
                  show _ = _
                  rw [show Gas.staticcallCommitted s argsOff argsLen retOff retLen toArg
                          = base + md + cold from rfl]
                  omega
                rw [eq]
                exact h
              exact StepRunning.staticcall s gasArg toArg argsOff argsLen retOff retLen
                rest _ h_dec h_stack h_committed h_take' rfl h_afford
          · nomatch h
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
                (s.accountMap s.executionEnv.address).balance < value ∨
                (s.accountMap s.executionEnv.address).nonce.toNat ≥ 2^64 - 1 := by
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
            · rename_i h_fw
              have h_take' : ¬ (s.executionEnv.depth ≥ 1024 ∨
                  (s.accountMap s.executionEnv.address).balance < value ∨
                  (s.accountMap s.executionEnv.address).nonce.toNat ≥ 2^64 - 1) := by
                simpa [State.consumeGas, State.consumeMemExp] using h_take
              -- `createAddress` is total now. Set `newAddr` to the
              -- stepF-style expression (over the consumed state) so the
              -- `set` abbreviation hits in the goal; `consumeGas` /
              -- `consumeMemExp` leave `executionEnv.address` and
              -- `accountMap` untouched, so the simplified form is equal.
              set newAddr := EvmSemantics.createAddress
                ((s.consumeGas base h_gas).consumeMemExp offset.toNat size.toNat
                  h_mem).executionEnv.address
                (((s.consumeGas base h_gas).consumeMemExp offset.toNat size.toNat
                    h_mem).accountMap
                  ((s.consumeGas base h_gas).consumeMemExp offset.toNat size.toNat
                    h_mem).executionEnv.address).nonce with hna
              have hna_eq : newAddr = EvmSemantics.createAddress s.executionEnv.address
                    (s.accountMap s.executionEnv.address).nonce := by
                rw [hna]; simp [State.consumeGas, State.consumeMemExp]
              split at h
              · rename_i h_coll
                cases h
                have h_coll' : (s.accountMap newAddr).isContract = true := by
                  simpa [State.consumeGas, State.consumeMemExp, hna] using h_coll
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
                rw [hna_eq] at h_coll'
                exact StepRunning.createCollision s value offset size rest _
                  h_dec h_stack h_perm' h_committed h_take' rfl h_coll'
              · rename_i h_nocoll
                cases h
                have h_nocoll' : (s.accountMap newAddr).isContract = false := by
                  simpa [State.consumeGas, State.consumeMemExp, hna] using h_nocoll
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
                  simp [hna, State.enterCreate, State.consumeGas, State.consumeMemExp,
                        State.activeWordsAfterUInt256, Gas.createCommitted,
                        MachineState.memExpansionDelta,
                        show ∀ (a b : UInt256), a + b = a.add b from fun _ _ => rfl]
                  grind
                rw [post_eq]
                rw [hna_eq] at h_nocoll' ⊢
                exact StepRunning.create s value offset size rest _
                  h_dec h_stack h_perm' h_committed h_take' rfl h_nocoll'
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
                  (s.accountMap s.executionEnv.address).balance < value ∨
                  (s.accountMap s.executionEnv.address).nonce.toNat ≥ 2^64 - 1 := by
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
                    (s.accountMap s.executionEnv.address).balance < value ∨
                    (s.accountMap s.executionEnv.address).nonce.toNat ≥ 2^64 - 1) := by
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
    | a :: rest, h =>
      by_cases h_total : Gas.balanceTotal s a ≤ s.gasAvailable
      · simp [h_total] at h
        cases h
        exact .balance s a rest h_dec h_total h_stack
      · simp [h_total] at h
    | [], h       => nomatch h
  | CALLDATALOAD =>
    match h_stack : s.stack, h with
    | i :: rest, h => cases h; exact .calldataload s i rest h_dec h_gas h_stack
    | [], h       => nomatch h
  | EXTCODESIZE =>
    match h_stack : s.stack, h with
    | a :: rest, h =>
      by_cases h_total : Gas.extcodesizeTotal s a ≤ s.gasAvailable
      · simp [h_total] at h
        cases h
        exact .extcodesize s a rest h_dec h_total h_stack
      · simp [h_total] at h
    | [], h       => nomatch h
  | EXTCODEHASH =>
    match h_stack : s.stack, h with
    | a :: rest, h =>
      by_cases h_total : Gas.extcodehashTotal s a ≤ s.gasAvailable
      · simp [h_total] at h
        cases h
        exact .extcodehash s a rest h_dec h_total h_stack
      · simp [h_total] at h
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
        by_cases h_dyn : Gas.copyWordCost sz
              + Gas.accountColdSurcharge s (AccountAddress.ofUInt256 a) ≤
            ((s.consumeGas (Gas.baseCost s.fork (.Env .EXTCODECOPY))
                            h_gas).consumeMemExp dOff.toNat sz.toNat h_mem).gasAvailable
        · simp [h_dyn] at h
          cases h
          set base := Gas.baseCost s.fork (.Env .EXTCODECOPY) with hbase
          set md := MachineState.memCost
                      (MachineState.activeWordsAfter s.activeWords.toNat dOff.toNat sz.toNat)
                    - MachineState.memCost s.activeWords.toNat with hmd
          have h_total : Gas.extcodecopyTotal s a dOff sz ≤ s.gasAvailable := by
            show base + md + (Gas.copyWordCost sz
                    + Gas.accountColdSurcharge s (AccountAddress.ofUInt256 a)) ≤ s.gasAvailable
            simp [State.canExpandMemory, State.consumeGas, State.consumeMemExp,
                  MachineState.memExpansionDelta, ← hbase, ← hmd] at h_mem h_dyn
            omega
          have post_eq :
              ({ ((s.consumeGas base h_gas).consumeMemExp dOff.toNat sz.toNat
                    h_mem).consumeGas (Gas.copyWordCost sz
                      + Gas.accountColdSurcharge s (AccountAddress.ofUInt256 a)) h_dyn with
                  toMachineState :=
                    { (((s.consumeGas base h_gas).consumeMemExp dOff.toNat sz.toNat
                        h_mem).consumeGas (Gas.copyWordCost sz
                          + Gas.accountColdSurcharge s (AccountAddress.ofUInt256 a))
                          h_dyn).toMachineState with
                      memory := MachineState.writeBytes s.memory
                                  (MachineState.readPadded
                                    (s.accountMap (AccountAddress.ofUInt256 a)).code
                                    sOff.toNat sz.toNat) dOff.toNat }
                  substate := s.substate.addAccessedAccount (AccountAddress.ofUInt256 a)
                }.replaceStackAndIncrPC rest)
              = ({ s with
                  stack := rest
                  pc := s.pc.succ
                  gasAvailable := s.gasAvailable - Gas.extcodecopyTotal s a dOff sz
                  memory := MachineState.writeBytes s.memory
                              (MachineState.readPadded
                                (s.accountMap (AccountAddress.ofUInt256 a)).code
                                sOff.toNat sz.toNat) dOff.toNat
                  activeWords := s.activeWordsAfterUInt256 dOff.toNat sz.toNat
                  substate := s.substate.addAccessedAccount
                                (AccountAddress.ofUInt256 a) } : State) := by
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
                            (Data.Bytes.natToBytesPadded value.toNat 32) offset.toNat
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
    | key :: rest, h =>
      by_cases h_total : Gas.sloadTotal s key ≤ s.gasAvailable
      · simp [h_total] at h
        cases h
        exact .sload s key rest h_dec h_total h_stack
      · simp [h_total] at h
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
              + Gas.sstoreColdSurcharge s key
              ≤ (s.consumeGas (Gas.baseCost s.fork (.StackMemFlow .SSTORE))
                    h_gas).gasAvailable
          · simp [h_dyn] at h
            cases h
            set base := Gas.baseCost s.fork (.StackMemFlow .SSTORE) with hbase
            set dyn := Gas.sstoreCost s.fork
                        (s.substate.originalStorage s.executionEnv.address key)
                        ((s.accountMap s.executionEnv.address).storage key) value
                        + Gas.sstoreColdSurcharge s key with hdyn
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
              { s.substate.addAccessedStorageKey (s.executionEnv.address, key) with
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
private theorem stepFE_sound_ok' (s s' : State) (h_nd : ¬ s.isDone) (h : stepFE s = .ok s') :
    Step s s' := by
  unfold stepFE at h
  simp only [Id.run] at h
  -- Split on s.halt.
  split at h
  · -- s.halt = .Running
    rename_i h_running
    -- Precompile dispatch: `stepFE` first matches on
    -- `Precompile.isPrecompile fork codeAddr`. The `true` arm runs
    -- the precompile (which then further splits on its `.success` /
    -- `.outOfGas` result); the `false` arm falls through to the
    -- standard bytecode dispatch.
    split at h
    · -- `Precompile.isPrecompile … = true`
      rename_i h_isPrec
      split at h
      · -- `Precompile.run … = .success out gasUsed`
        rename_i out gasUsed h_prec
        cases h
        exact Step.precompileSuccess s out gasUsed h_running h_isPrec h_prec
      · -- `Precompile.run … = .outOfGas`
        rename_i h_prec
        cases h
        exact Step.precompileOog s h_running h_isPrec h_prec
    · -- `Precompile.isPrecompile … = false`: standard bytecode dispatch.
      rename_i h_isPrec
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
              exact .running h_running h_isPrec
                (stepF.stopArith_sound s op (State.decoded_to_op h_dec) h_gas h)
            | CompBit op =>
              exact .running h_running h_isPrec
                (stepF.compBit_sound s op (State.decoded_to_op h_dec) h_gas h)
            | Keccak op =>
              exact .running h_running h_isPrec
                (stepF.keccak_sound s op (State.decoded_to_op h_dec) h_gas h)
            | Env op =>
              exact .running h_running h_isPrec
                (stepF.env_sound s op (State.decoded_to_op h_dec) h_gas h)
            | Block op =>
              exact .running h_running h_isPrec
                (stepF.block_sound s op (State.decoded_to_op h_dec) h_gas h)
            | StackMemFlow op =>
              exact .running h_running h_isPrec
                (stepF.stackMemFlow_sound s op (State.decoded_to_op h_dec) h_gas h)
            | Push op =>
              exact .running h_running h_isPrec
                (stepF.push_sound s op argOpt h_dec h_gas h)
            | Dup op =>
              exact .running h_running h_isPrec
                (stepF.dup_sound s op (State.decoded_to_op h_dec) h_gas h)
            | Swap op =>
              exact .running h_running h_isPrec
                (stepF.swap_sound s op (State.decoded_to_op h_dec) h_gas h)
            | DupN op =>
              exact .running h_running h_isPrec
                (stepF.dupN_sound s op (State.decoded_to_op h_dec) h_gas h)
            | SwapN op =>
              exact .running h_running h_isPrec
                (stepF.swapN_sound s op (State.decoded_to_op h_dec) h_gas h)
            | Exchange op =>
              exact .running h_running h_isPrec
                (stepF.exchange_sound s op (State.decoded_to_op h_dec) h_gas h)
            | Log op =>
              exact .running h_running h_isPrec
                (stepF.log_sound s op (State.decoded_to_op h_dec) h_gas h)
            | System op =>
              exact .running h_running h_isPrec
                (stepF.system_sound s op (State.decoded_to_op h_dec) h_gas h)
          · -- gas < cost
            nomatch h
  -- Non-Running halts: `stepFE` resumes the top caller (`.ok`, via the
  -- `callReturn*` rules) when the call stack is non-empty, otherwise it
  -- returns the state unchanged (the YP-empty case — no transition is
  -- defined). The `¬ s.isDone` precondition rules out the latter:
  -- `isDone = isHalted ∧ callStack.isEmpty`, so a halted state with an
  -- empty call stack would be done.
  all_goals
    split at h
    · rename_i h_cs
      exfalso
      apply h_nd
      simp [State.isDone, State.isHalted, State.isRunning, h_cs]
    · rename_i f rest h_cs
      injection h with h_eq
      subst h_eq
      exact .returning (resume_sound s f rest (by simp_all) h_cs)

/-- Soundness of `stepF` *on the success path*: when `stepFE s = .ok s'`
    (no in-frame exception), `stepF s = s'` and the transition is a
    valid `Step`. A direct corollary of `stepFE_sound` plus the
    definitional reduction of `stepF`. -/
theorem stepF_sound_ok (s s' : State) (h_nd : ¬ s.isDone)
    (h : stepFE s = .ok s') : stepF s = s' ∧ Step s s' := by
  refine ⟨?_, stepFE_sound_ok' s s' h_nd h⟩
  show (match stepFE s with
         | .ok s'   => s'
         | .error e => { s with halt := .Exception e }) = s'
  rw [h]

----------------------------------------------------------------------------
-- Exception direction: each per-helper `*_sound_error` lemma takes a
-- `.error e` outcome from `stepF.<helper>` and produces the matching
-- `StepRunning` exception derivation. They mirror the `*_sound` lemmas
-- above, with the .ok arm now contradicted (via `nomatch h`) and the
-- exception arms discharged with the corresponding constructor.
----------------------------------------------------------------------------

namespace stepF

/-- Stack-underflow helper: when `s.stack` matches a too-short prefix and
    a `.stackUnderflow` derivation is needed, package the popArity-gap
    proof and adapt the goal-side `stack := <pattern>` substitution back
    to `stack := s.stack` so the constructor's conclusion unifies. -/
private theorem mk_underflow {s : State} {op : Operation} {stk : List UInt256}
    (h_dec : s.decodedOp = some op) (h_stack : s.stack = stk)
    (h_under : stk.length < op.popArity) :
    StepRunning s ({ toSharedState := s.toSharedState, pc := s.pc, stack := stk,
                     execLength := s.execLength, halt := .Exception .StackUnderflow,
                     callStack := s.callStack }) := by
  subst h_stack
  exact StepRunning.stackUnderflow s op h_dec h_under

/-- OutOfGas helper. Same goal-adaptation trick as `mk_underflow`. -/
private theorem mk_outOfGas {s : State} {op : Operation} {stk : List UInt256}
    (h_dec : s.decodedOp = some op) (h_stack : s.stack = stk)
    (cost : Nat) (h_lb : Gas.baseCost s.fork op ≤ cost) (h_gas : s.gasAvailable < cost) :
    StepRunning s ({ toSharedState := s.toSharedState, pc := s.pc, stack := stk,
                     execLength := s.execLength, halt := .Exception .OutOfGas,
                     callStack := s.callStack }) := by
  subst h_stack
  exact StepRunning.outOfGas s op cost h_dec h_lb h_gas

/-- StaticModeViolation helper. -/
private theorem mk_staticMode {s : State} {op : Operation} {stk : List UInt256}
    (h_dec : s.decodedOp = some op) (h_stack : s.stack = stk)
    (h_mut : op.isStateMutating = true)
    (h_perm : s.executionEnv.permitStateMutation = false) :
    StepRunning s ({ toSharedState := s.toSharedState, pc := s.pc, stack := stk,
                     execLength := s.execLength, halt := .Exception .StaticModeViolation,
                     callStack := s.callStack }) := by
  subst h_stack
  exact StepRunning.staticModeViolation s op h_dec h_mut h_perm

/-- `s.exchange i j = none` exactly when at least one index is out of range. -/
private theorem exchange_eq_none_iff {α : Type _} (s : List α) (i j : Nat) :
    s.exchange i j = none ↔ s.length ≤ i ∨ s.length ≤ j := by
  unfold List.exchange
  simp [bind, Option.bind]
  cases h₁ : s[i]? with
  | none =>
    simp
    exact Or.inl (List.getElem?_eq_none_iff.mp h₁)
  | some _ =>
    cases h₂ : s[j]? with
    | none =>
      simp
      have h_i_lt : i < s.length := by
        by_contra h
        push Not at h
        rw [List.getElem?_eq_none_iff.mpr h] at h₁
        cases h₁
      right
      exact List.getElem?_eq_none_iff.mp h₂
    | some _ =>
      simp
      have h_i_lt : i < s.length := by
        by_contra h
        push Not at h
        rw [List.getElem?_eq_none_iff.mpr h] at h₁
        cases h₁
      have h_j_lt : j < s.length := by
        by_contra h
        push Not at h
        rw [List.getElem?_eq_none_iff.mpr h] at h₂
        cases h₂
      omega

/-- CallStatic helper: CALL with value ≠ 0 in static mode. -/
private theorem mk_callStatic {s : State} {stk : List UInt256}
    (h_dec : s.decodedOp = some .CALL) (h_stack : s.stack = stk)
    (gasArg toArg value argsOff argsLen retOff retLen : UInt256)
    (rest : List UInt256)
    (h_stack_pat : stk = gasArg :: toArg :: value :: argsOff :: argsLen :: retOff :: retLen :: rest)
    (h_perm : s.executionEnv.permitStateMutation = false)
    (h_value : value.toNat ≠ 0) :
    StepRunning s ({ toSharedState := s.toSharedState, pc := s.pc, stack := stk,
                     execLength := s.execLength,
                     halt := .Exception .StaticModeViolation,
                     callStack := s.callStack }) := by
  subst h_stack
  exact StepRunning.callStatic s gasArg toArg value argsOff argsLen retOff retLen rest
        h_dec h_stack_pat h_perm h_value

/-- BadJumpDestination helper for `JUMP`. -/
private theorem mk_jumpBad {s : State} {stk : List UInt256}
    (h_dec : s.decodedOp = some .JUMP) (h_stack : s.stack = stk)
    (dest : UInt256) (rest : List UInt256)
    (h_stack_pat : stk = dest :: rest)
    (h_gas : Gas.baseCost s.fork .JUMP ≤ s.gasAvailable)
    (h_bad : Decode.isValidJumpDest s.executionEnv.code dest.toNat = false) :
    StepRunning s ({ toSharedState := s.toSharedState, pc := s.pc, stack := stk,
                     execLength := s.execLength,
                     halt := .Exception .BadJumpDestination,
                     callStack := s.callStack }) := by
  subst h_stack
  exact StepRunning.jumpBadDest s dest rest h_dec h_gas h_stack_pat h_bad

/-- BadJumpDestination helper for `JUMPI` (taken branch with bad destination). -/
private theorem mk_jumpiBad {s : State} {stk : List UInt256}
    (h_dec : s.decodedOp = some .JUMPI) (h_stack : s.stack = stk)
    (dest cond : UInt256) (rest : List UInt256)
    (h_stack_pat : stk = dest :: cond :: rest)
    (h_gas : Gas.baseCost s.fork .JUMPI ≤ s.gasAvailable)
    (h_cond : UInt256.isTrue cond)
    (h_bad : Decode.isValidJumpDest s.executionEnv.code dest.toNat = false) :
    StepRunning s ({ toSharedState := s.toSharedState, pc := s.pc, stack := stk,
                     execLength := s.execLength,
                     halt := .Exception .BadJumpDestination,
                     callStack := s.callStack }) := by
  subst h_stack
  exact StepRunning.jumpiBadDest s dest cond rest h_dec h_gas h_stack_pat h_cond h_bad

/-- InvalidMemoryAccess helper (e.g. RETURNDATACOPY OOB). -/
private theorem mk_invalidMem {s : State} {op : Operation} {stk : List UInt256}
    (h_dec : s.decodedOp = some op) (h_stack : s.stack = stk)
    (h_op_returndatacopy : op = .RETURNDATACOPY)
    (destOff srcOff sz : UInt256) (rest : List UInt256)
    (h_stack_pat : stk = destOff :: srcOff :: sz :: rest)
    (h_gas_op : Gas.baseCost s.fork .RETURNDATACOPY ≤ s.gasAvailable)
    (h_oob : srcOff.toNat + sz.toNat > s.returnData.size) :
    StepRunning s ({ toSharedState := s.toSharedState, pc := s.pc, stack := stk,
                     execLength := s.execLength, halt := .Exception .InvalidMemoryAccess,
                     callStack := s.callStack }) := by
  subst h_op_returndatacopy
  subst h_stack
  exact StepRunning.returndatacopyOob s destOff srcOff sz rest h_dec h_gas_op
        h_stack_pat h_oob

/-- InvalidInstruction helper (explicit INVALID opcode). -/
private theorem mk_invalidOp {s : State} {stk : List UInt256}
    (h_dec : s.decodedOp = some .INVALID) (h_stack : s.stack = stk) :
    StepRunning s ({ toSharedState := s.toSharedState, pc := s.pc, stack := stk,
                     execLength := s.execLength, halt := .Exception .InvalidInstruction,
                     callStack := s.callStack }) := by
  subst h_stack
  exact StepRunning.invalidOpcode s h_dec

/-- StopArith error path: only `StackUnderflow` (any binary/ternary op
    with too few items) and `OutOfGas` (EXP's dynamic per-byte fee). -/
theorem stopArith_sound_error (s : State) (op : Operation.StopArithOps)
    (h_dec : s.decodedOp = some (.StopArith op))
    (h_gas : Gas.baseCost s.fork (.StopArith op) ≤ s.gasAvailable)
    {e : ExecutionException}
    (h : stepF.stopArith s (s.consumeGas (Gas.baseCost s.fork (.StopArith op)) h_gas) op
           = .error e) :
    StepRunning s ({ s with halt := .Exception e }) := by
  unfold stepF.stopArith at h
  cases op with
  | STOP => nomatch h
  | ADD =>
    match h_stack : s.stack, h with
    | _ :: _ :: _, h => nomatch h
    | [],      h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_],     h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
  | MUL =>
    match h_stack : s.stack, h with
    | _ :: _ :: _, h => nomatch h
    | [],      h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_],     h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
  | SUB =>
    match h_stack : s.stack, h with
    | _ :: _ :: _, h => nomatch h
    | [],      h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_],     h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
  | DIV =>
    match h_stack : s.stack, h with
    | _ :: _ :: _, h => nomatch h
    | [],      h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_],     h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
  | SDIV =>
    match h_stack : s.stack, h with
    | _ :: _ :: _, h => nomatch h
    | [],      h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_],     h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
  | MOD =>
    match h_stack : s.stack, h with
    | _ :: _ :: _, h => nomatch h
    | [],      h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_],     h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
  | SMOD =>
    match h_stack : s.stack, h with
    | _ :: _ :: _, h => nomatch h
    | [],      h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_],     h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
  | ADDMOD =>
    match h_stack : s.stack, h with
    | _ :: _ :: _ :: _, h => nomatch h
    | [],      h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_],     h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_, _],  h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
  | MULMOD =>
    match h_stack : s.stack, h with
    | _ :: _ :: _ :: _, h => nomatch h
    | [],      h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_],     h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_, _],  h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
  | EXP =>
    match h_stack : s.stack, h with
    | a :: b :: rest, h =>
      by_cases h_dyn : Gas.expByteCost s.fork b
                        ≤ (s.consumeGas (Gas.baseCost s.fork (.StopArith .EXP))
                              h_gas).gasAvailable
      · simp [h_dyn] at h
      · simp [h_dyn] at h
        cases h
        refine mk_outOfGas h_dec h_stack
          (Gas.baseCost s.fork (.StopArith .EXP) + Gas.expByteCost s.fork b)
          (Nat.le_add_right _ _) ?_
        unfold State.consumeGas at h_dyn
        simp at h_dyn
        omega
    | [],      h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_],     h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
  | SIGNEXTEND =>
    match h_stack : s.stack, h with
    | _ :: _ :: _, h => nomatch h
    | [],      h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_],     h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])

/-- CompBit error path: every op is `StackUnderflow` only — pure
    register-to-register operations with no dynamic gas. -/
theorem compBit_sound_error (s : State) (op : Operation.CompareBitwiseOps)
    (h_dec : s.decodedOp = some (.CompBit op))
    (h_gas : Gas.baseCost s.fork (.CompBit op) ≤ s.gasAvailable)
    {e : ExecutionException}
    (h : stepF.compBit s (s.consumeGas (Gas.baseCost s.fork (.CompBit op)) h_gas) op
           = .error e) :
    StepRunning s ({ s with halt := .Exception e }) := by
  unfold stepF.compBit at h
  -- Binary ops (12) all share the same shape: `[]` or `[_]` ⇒ underflow.
  -- Unary ops (`ISZERO`, `NOT`): only `[]` ⇒ underflow.
  cases op <;>
    first
    | (match h_stack : s.stack, h with
       | _ :: _ :: _, h => nomatch h
       | [],  h =>
         cases h
         exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
       | [_], h =>
         cases h
         exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length]))
    | (match h_stack : s.stack, h with
       | _ :: _, h => nomatch h
       | [],  h =>
         cases h
         exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length]))

/-- Block error path: only `BLOCKHASH` and `BLOBHASH` can underflow
    (all others are nullary reads). -/
theorem block_sound_error (s : State) (op : Operation.BlockOps)
    (h_dec : s.decodedOp = some (.Block op))
    (h_gas : Gas.baseCost s.fork (.Block op) ≤ s.gasAvailable)
    {e : ExecutionException}
    (h : stepF.block s (s.consumeGas (Gas.baseCost s.fork (.Block op)) h_gas) op = .error e) :
    StepRunning s ({ s with halt := .Exception e }) := by
  unfold stepF.block at h
  cases op with
  | BLOCKHASH =>
    match h_stack : s.stack, h with
    | _ :: _, h => nomatch h
    | [],  h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
  | BLOBHASH =>
    match h_stack : s.stack, h with
    | _ :: _, h => nomatch h
    | [],  h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
  | COINBASE | TIMESTAMP | NUMBER | PREVRANDAO | GASLIMIT | CHAINID
  | SELFBALANCE | BASEFEE | BLOBBASEFEE => nomatch h

/-- DUP error path: only `StackUnderflow` (index out of range). -/
theorem dup_sound_error (s : State) (op : Operation.DupOp)
    (h_dec : s.decodedOp = some (.Dup op))
    (h_gas : Gas.baseCost s.fork (.Dup op) ≤ s.gasAvailable)
    {e : ExecutionException}
    (h : stepF.dup s (s.consumeGas (Gas.baseCost s.fork (.Dup op)) h_gas) op = .error e) :
    StepRunning s ({ s with halt := .Exception e }) := by
  unfold stepF.dup at h
  match h_get : s.stack[op.idx.val]?, h with
  | some _, h => nomatch h
  | none,   h =>
    cases h
    refine mk_underflow h_dec rfl ?_
    have h_len : s.stack.length ≤ op.idx.val := List.getElem?_eq_none_iff.mp h_get
    show s.stack.length < op.idx.val + 1
    omega

/-- SWAP error path: only `StackUnderflow`. -/
theorem swap_sound_error (s : State) (op : Operation.SwapOp)
    (h_dec : s.decodedOp = some (.Swap op))
    (h_gas : Gas.baseCost s.fork (.Swap op) ≤ s.gasAvailable)
    {e : ExecutionException}
    (h : stepF.swap s (s.consumeGas (Gas.baseCost s.fork (.Swap op)) h_gas) op = .error e) :
    StepRunning s ({ s with halt := .Exception e }) := by
  unfold stepF.swap at h
  match h_ex : s.stack.exchange 0 (op.idx.val + 1), h with
  | some _, h => nomatch h
  | none,   h =>
    cases h
    refine mk_underflow h_dec rfl ?_
    rcases (exchange_eq_none_iff _ _ _).mp h_ex with h0 | h1
    · show s.stack.length < op.idx.val + 2; omega
    · show s.stack.length < op.idx.val + 2; omega

/-- DUPN error path. -/
theorem dupN_sound_error (s : State) (op : Operation.DupNOp)
    (h_dec : s.decodedOp = some (.DupN op))
    (h_gas : Gas.baseCost s.fork (.DupN op) ≤ s.gasAvailable)
    {e : ExecutionException}
    (h : stepF.dupN s (s.consumeGas (Gas.baseCost s.fork (.DupN op)) h_gas) op = .error e) :
    StepRunning s ({ s with halt := .Exception e }) := by
  unfold stepF.dupN at h
  match h_get : s.stack[op.n.val]?, h with
  | some _, h => nomatch h
  | none,   h =>
    cases h
    refine mk_underflow h_dec rfl ?_
    have h_len : s.stack.length ≤ op.n.val := List.getElem?_eq_none_iff.mp h_get
    show s.stack.length < op.n.val + 1
    omega

/-- SWAPN error path. -/
theorem swapN_sound_error (s : State) (op : Operation.SwapNOp)
    (h_dec : s.decodedOp = some (.SwapN op))
    (h_gas : Gas.baseCost s.fork (.SwapN op) ≤ s.gasAvailable)
    {e : ExecutionException}
    (h : stepF.swapN s (s.consumeGas (Gas.baseCost s.fork (.SwapN op)) h_gas) op = .error e) :
    StepRunning s ({ s with halt := .Exception e }) := by
  unfold stepF.swapN at h
  match h_ex : s.stack.exchange 0 (op.n.val + 1), h with
  | some _, h => nomatch h
  | none,   h =>
    cases h
    refine mk_underflow h_dec rfl ?_
    rcases (exchange_eq_none_iff _ _ _).mp h_ex with h0 | h1
    · show s.stack.length < op.n.val + 2; omega
    · show s.stack.length < op.n.val + 2; omega

/-- EXCHANGE error path. -/
theorem exchange_sound_error (s : State) (op : Operation.ExchangeOp)
    (h_dec : s.decodedOp = some (.Exchange op))
    (h_gas : Gas.baseCost s.fork (.Exchange op) ≤ s.gasAvailable)
    {e : ExecutionException}
    (h : stepF.exchange s (s.consumeGas (Gas.baseCost s.fork (.Exchange op)) h_gas) op
           = .error e) :
    StepRunning s ({ s with halt := .Exception e }) := by
  unfold stepF.exchange at h
  match h_ex : s.stack.exchange (op.n + 1) (op.m + 1), h with
  | some _, h => nomatch h
  | none,   h =>
    cases h
    refine mk_underflow h_dec rfl ?_
    rcases (exchange_eq_none_iff _ _ _).mp h_ex with hn | hm
    · show s.stack.length < Nat.max (op.n + 1) (op.m + 1) + 1
      simp [Nat.max_def]; split <;> omega
    · show s.stack.length < Nat.max (op.n + 1) (op.m + 1) + 1
      simp [Nat.max_def]; split <;> omega

/-- Env error path. Sites:
    * Stack underflow on `BALANCE`/`CALLDATALOAD`/`EXTCODESIZE`/`EXTCODEHASH`
      (1-arg), `CALLDATACOPY`/`CODECOPY`/`RETURNDATACOPY` (3-arg),
      `EXTCODECOPY` (4-arg).
    * `OutOfGas` from `chargeMem` for the four memory-touching copy ops.
    * `OutOfGas` from `copyWordCost` for the same four copy ops.
    * `InvalidMemoryAccess` for `RETURNDATACOPY` OOB. -/
theorem env_sound_error (s : State) (op : Operation.EnvOps)
    (h_dec : s.decodedOp = some (.Env op))
    (h_gas : Gas.baseCost s.fork (.Env op) ≤ s.gasAvailable)
    {e : ExecutionException}
    (h : stepF.env s (s.consumeGas (Gas.baseCost s.fork (.Env op)) h_gas) op = .error e) :
    StepRunning s ({ s with halt := .Exception e }) := by
  unfold stepF.env at h
  cases op with
  | ADDRESS | ORIGIN | CALLER | CALLVALUE | CALLDATASIZE | CODESIZE
  | GASPRICE | RETURNDATASIZE => nomatch h
  | BALANCE =>
    match h_stack : s.stack, h with
    | a :: rest, h =>
      by_cases h_total : Gas.balanceTotal s a ≤ s.gasAvailable
      · simp [h_total] at h
      · simp [h_total] at h
        cases h
        refine mk_outOfGas h_dec h_stack (Gas.balanceTotal s a) ?_ ?_
        · show Gas.baseCost s.fork (.Env .BALANCE)
               ≤ Gas.baseCost s.fork (.Env .BALANCE)
                 + Gas.accountColdSurcharge s (AccountAddress.ofUInt256 a)
          omega
        · omega
    | [], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
  | CALLDATALOAD =>
    match h_stack : s.stack, h with
    | _ :: _, h => nomatch h
    | [], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
  | EXTCODESIZE =>
    match h_stack : s.stack, h with
    | a :: rest, h =>
      by_cases h_total : Gas.extcodesizeTotal s a ≤ s.gasAvailable
      · simp [h_total] at h
      · simp [h_total] at h
        cases h
        refine mk_outOfGas h_dec h_stack (Gas.extcodesizeTotal s a) ?_ ?_
        · show Gas.baseCost s.fork (.Env .EXTCODESIZE)
               ≤ Gas.baseCost s.fork (.Env .EXTCODESIZE)
                 + Gas.accountColdSurcharge s (AccountAddress.ofUInt256 a)
          omega
        · omega
    | [], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
  | EXTCODEHASH =>
    match h_stack : s.stack, h with
    | a :: rest, h =>
      by_cases h_total : Gas.extcodehashTotal s a ≤ s.gasAvailable
      · simp [h_total] at h
      · simp [h_total] at h
        cases h
        refine mk_outOfGas h_dec h_stack (Gas.extcodehashTotal s a) ?_ ?_
        · show Gas.baseCost s.fork (.Env .EXTCODEHASH)
               ≤ Gas.baseCost s.fork (.Env .EXTCODEHASH)
                 + Gas.accountColdSurcharge s (AccountAddress.ofUInt256 a)
          omega
        · omega
    | [], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
  | CALLDATACOPY =>
    match h_stack : s.stack, h with
    | destOff :: srcOff :: sz :: rest, h =>
      unfold chargeMem at h
      by_cases h_mem :
          (s.consumeGas (Gas.baseCost s.fork (.Env .CALLDATACOPY)) h_gas).canExpandMemory
            destOff.toNat sz.toNat
      · simp [h_mem] at h
        by_cases h_dyn : Gas.copyWordCost sz ≤
            ((s.consumeGas (Gas.baseCost s.fork (.Env .CALLDATACOPY))
                            h_gas).consumeMemExp destOff.toNat sz.toNat h_mem).gasAvailable
        · simp [h_dyn] at h
        · simp [h_dyn] at h
          cases h
          set base := Gas.baseCost s.fork (.Env .CALLDATACOPY) with hbase
          set md := MachineState.memCost (MachineState.activeWordsAfter
                      s.activeWords.toNat destOff.toNat sz.toNat)
                    - MachineState.memCost s.activeWords.toNat with hmd
          set cwc := Gas.copyWordCost sz with hcwc
          have h_mem' : md ≤ s.gasAvailable - base := by
            simp only [State.canExpandMemory, State.consumeGas,
                       MachineState.memExpansionDelta, ← hbase, ← hmd] at h_mem
            exact h_mem
          have h_dyn' : s.gasAvailable - base - md < cwc := by
            simp only [State.consumeGas, State.consumeMemExp, ← hbase, ← hmd] at h_dyn
            omega
          refine mk_outOfGas h_dec h_stack (base + md + cwc) ?_ ?_
          · show base ≤ base + md + cwc; omega
          · show s.gasAvailable < base + md + cwc; omega
      · simp [h_mem] at h
        cases h
        set base := Gas.baseCost s.fork (.Env .CALLDATACOPY) with hbase
        set md := MachineState.memCost (MachineState.activeWordsAfter
                    s.activeWords.toNat destOff.toNat sz.toNat)
                  - MachineState.memCost s.activeWords.toNat with hmd
        have h_mem' : ¬ md ≤ s.gasAvailable - base := by
          simp only [State.canExpandMemory, State.consumeGas,
                     MachineState.memExpansionDelta, ← hbase, ← hmd] at h_mem
          exact h_mem
        refine mk_outOfGas h_dec h_stack (base + md) (Nat.le_add_right _ _) ?_
        omega
    | [], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_, _], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
  | CODECOPY =>
    match h_stack : s.stack, h with
    | destOff :: srcOff :: sz :: rest, h =>
      unfold chargeMem at h
      by_cases h_mem :
          (s.consumeGas (Gas.baseCost s.fork (.Env .CODECOPY)) h_gas).canExpandMemory
            destOff.toNat sz.toNat
      · simp [h_mem] at h
        by_cases h_dyn : Gas.copyWordCost sz ≤
            ((s.consumeGas (Gas.baseCost s.fork (.Env .CODECOPY))
                            h_gas).consumeMemExp destOff.toNat sz.toNat h_mem).gasAvailable
        · simp [h_dyn] at h
        · simp [h_dyn] at h
          cases h
          set base := Gas.baseCost s.fork (.Env .CODECOPY) with hbase
          set md := MachineState.memCost (MachineState.activeWordsAfter
                      s.activeWords.toNat destOff.toNat sz.toNat)
                    - MachineState.memCost s.activeWords.toNat with hmd
          set cwc := Gas.copyWordCost sz with hcwc
          have h_mem' : md ≤ s.gasAvailable - base := by
            simp only [State.canExpandMemory, State.consumeGas,
                       MachineState.memExpansionDelta, ← hbase, ← hmd] at h_mem
            exact h_mem
          have h_dyn' : s.gasAvailable - base - md < cwc := by
            simp only [State.consumeGas, State.consumeMemExp, ← hbase, ← hmd] at h_dyn
            omega
          refine mk_outOfGas h_dec h_stack (base + md + cwc) ?_ ?_
          · show base ≤ base + md + cwc; omega
          · show s.gasAvailable < base + md + cwc; omega
      · simp [h_mem] at h
        cases h
        set base := Gas.baseCost s.fork (.Env .CODECOPY) with hbase
        set md := MachineState.memCost (MachineState.activeWordsAfter
                    s.activeWords.toNat destOff.toNat sz.toNat)
                  - MachineState.memCost s.activeWords.toNat with hmd
        have h_mem' : ¬ md ≤ s.gasAvailable - base := by
          simp only [State.canExpandMemory, State.consumeGas,
                     MachineState.memExpansionDelta, ← hbase, ← hmd] at h_mem
          exact h_mem
        refine mk_outOfGas h_dec h_stack (base + md) (Nat.le_add_right _ _) ?_
        omega
    | [], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_, _], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
  | EXTCODECOPY =>
    match h_stack : s.stack, h with
    | a :: destOff :: srcOff :: sz :: rest, h =>
      unfold chargeMem at h
      by_cases h_mem :
          (s.consumeGas (Gas.baseCost s.fork (.Env .EXTCODECOPY)) h_gas).canExpandMemory
            destOff.toNat sz.toNat
      · simp [h_mem] at h
        by_cases h_dyn : Gas.copyWordCost sz
              + Gas.accountColdSurcharge s (AccountAddress.ofUInt256 a) ≤
            ((s.consumeGas (Gas.baseCost s.fork (.Env .EXTCODECOPY))
                            h_gas).consumeMemExp destOff.toNat sz.toNat h_mem).gasAvailable
        · simp [h_dyn] at h
        · simp [h_dyn] at h
          cases h
          set base := Gas.baseCost s.fork (.Env .EXTCODECOPY) with hbase
          set md := MachineState.memCost (MachineState.activeWordsAfter
                      s.activeWords.toNat destOff.toNat sz.toNat)
                    - MachineState.memCost s.activeWords.toNat with hmd
          set cwc := Gas.copyWordCost sz
                       + Gas.accountColdSurcharge s (AccountAddress.ofUInt256 a) with hcwc
          have h_mem' : md ≤ s.gasAvailable - base := by
            simp only [State.canExpandMemory, State.consumeGas,
                       MachineState.memExpansionDelta, ← hbase, ← hmd] at h_mem
            exact h_mem
          have h_dyn' : s.gasAvailable - base - md < cwc := by
            simp only [State.consumeGas, State.consumeMemExp, ← hbase, ← hmd] at h_dyn
            omega
          refine mk_outOfGas h_dec h_stack (base + md + cwc) ?_ ?_
          · show base ≤ base + md + cwc; omega
          · show s.gasAvailable < base + md + cwc; omega
      · simp [h_mem] at h
        cases h
        set base := Gas.baseCost s.fork (.Env .EXTCODECOPY) with hbase
        set md := MachineState.memCost (MachineState.activeWordsAfter
                    s.activeWords.toNat destOff.toNat sz.toNat)
                  - MachineState.memCost s.activeWords.toNat with hmd
        have h_mem' : ¬ md ≤ s.gasAvailable - base := by
          simp only [State.canExpandMemory, State.consumeGas,
                     MachineState.memExpansionDelta, ← hbase, ← hmd] at h_mem
          exact h_mem
        refine mk_outOfGas h_dec h_stack (base + md) (Nat.le_add_right _ _) ?_
        omega
    | [], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_, _], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_, _, _], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
  | RETURNDATACOPY =>
    match h_stack : s.stack, h with
    | destOff :: srcOff :: sz :: rest, h =>
      by_cases h_oob : srcOff.toNat + sz.toNat > s.returnData.size
      · -- InvalidMemoryAccess
        simp [h_oob] at h
        cases h
        refine mk_invalidMem h_dec h_stack rfl destOff srcOff sz rest rfl h_gas h_oob
      · simp [h_oob] at h
        unfold chargeMem at h
        by_cases h_mem :
            (s.consumeGas (Gas.baseCost s.fork (.Env .RETURNDATACOPY)) h_gas).canExpandMemory
              destOff.toNat sz.toNat
        · simp [h_mem] at h
          by_cases h_dyn : Gas.copyWordCost sz ≤
              ((s.consumeGas (Gas.baseCost s.fork (.Env .RETURNDATACOPY))
                              h_gas).consumeMemExp destOff.toNat sz.toNat h_mem).gasAvailable
          · simp [h_dyn] at h
          · simp [h_dyn] at h
            cases h
            set base := Gas.baseCost s.fork (.Env .RETURNDATACOPY) with hbase
            set md := MachineState.memCost (MachineState.activeWordsAfter
                        s.activeWords.toNat destOff.toNat sz.toNat)
                      - MachineState.memCost s.activeWords.toNat with hmd
            set cwc := Gas.copyWordCost sz with hcwc
            have h_mem' : md ≤ s.gasAvailable - base := by
              simp only [State.canExpandMemory, State.consumeGas,
                         MachineState.memExpansionDelta, ← hbase, ← hmd] at h_mem
              exact h_mem
            have h_dyn' : s.gasAvailable - base - md < cwc := by
              simp only [State.consumeGas, State.consumeMemExp, ← hbase, ← hmd] at h_dyn
              omega
            refine mk_outOfGas h_dec h_stack (base + md + cwc) ?_ ?_
            · show base ≤ base + md + cwc; omega
            · show s.gasAvailable < base + md + cwc; omega
        · simp [h_mem] at h
          cases h
          set base := Gas.baseCost s.fork (.Env .RETURNDATACOPY) with hbase
          set md := MachineState.memCost (MachineState.activeWordsAfter
                      s.activeWords.toNat destOff.toNat sz.toNat)
                    - MachineState.memCost s.activeWords.toNat with hmd
          have h_mem' : ¬ md ≤ s.gasAvailable - base := by
            simp only [State.canExpandMemory, State.consumeGas,
                       MachineState.memExpansionDelta, ← hbase, ← hmd] at h_mem
            exact h_mem
          refine mk_outOfGas h_dec h_stack (base + md) (Nat.le_add_right _ _) ?_
          omega
    | [], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_, _], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])

/-- Keccak error path: stack underflow (`[]` or `[_]`), memory-expansion
    `OutOfGas` (the `chargeMem` arm), and per-word `OutOfGas` (the
    `keccakWordCost` dyn arm). The cost witness for the dyn arm is
    `Gas.keccakTotal s offset size`; for the chargeMem arm it's
    `baseCost + memExpansionDelta`. -/
theorem keccak_sound_error (s : State) (op : Operation.KeccakOps)
    (h_dec : s.decodedOp = some (.Keccak op))
    (h_gas : Gas.baseCost s.fork (.Keccak op) ≤ s.gasAvailable)
    {e : ExecutionException}
    (h : stepF.keccak s (s.consumeGas (Gas.baseCost s.fork (.Keccak op)) h_gas) op
           = .error e) :
    StepRunning s ({ s with halt := .Exception e }) := by
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
        · simp [h_dyn] at h
          cases h
          -- Set up abstractions so omega can reason about distinct gas atoms.
          set base := Gas.baseCost s.fork (.Keccak .KECCAK256) with hbase
          set md := MachineState.memCost (MachineState.activeWordsAfter
                      s.activeWords.toNat offset.toNat size.toNat)
                    - MachineState.memCost s.activeWords.toNat with hmd
          set kwc := Gas.keccakWordCost size with hkwc
          have h_mem' : md ≤ s.gasAvailable - base := by
            simp only [State.canExpandMemory, State.consumeGas,
                       MachineState.memExpansionDelta, ← hbase, ← hmd] at h_mem
            exact h_mem
          have h_dyn' : s.gasAvailable - base - md < kwc := by
            simp only [State.consumeGas, State.consumeMemExp, ← hbase, ← hmd] at h_dyn
            omega
          refine mk_outOfGas h_dec h_stack (base + md + kwc) ?_ ?_
          · show base ≤ base + md + kwc; omega
          · show s.gasAvailable < base + md + kwc; omega
      · simp [h_mem] at h
        cases h
        set base := Gas.baseCost s.fork (.Keccak .KECCAK256) with hbase
        set md := MachineState.memCost (MachineState.activeWordsAfter
                    s.activeWords.toNat offset.toNat size.toNat)
                  - MachineState.memCost s.activeWords.toNat with hmd
        have h_mem' : ¬ md ≤ s.gasAvailable - base := by
          simp only [State.canExpandMemory, State.consumeGas,
                     MachineState.memExpansionDelta, ← hbase, ← hmd] at h_mem
          exact h_mem
        refine mk_outOfGas h_dec h_stack (base + md) (Nat.le_add_right _ _) ?_
        omega
    | [], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])

/-- Decoder invariant: `decodeAt` never produces `(.Push p, none)`. The
    `.Push` arm of `decodeAt` always returns `some (UInt256.ofNat n, w)`
    as the immediate; the non-`.Push` arms produce a different first
    component. -/
private theorem decodeAt_push_arg_some {code : ByteArray} {pc : Nat}
    {p : Operation.PushOp} {argOpt : Option (UInt256 × Nat)}
    (h : Decode.decodeAt code pc = some (.Push p, argOpt)) :
    argOpt ≠ none := by
  unfold Decode.decodeAt at h
  split at h
  · cases h_op : Decode.opcodeOf code[pc] with
    | none => simp [h_op] at h
    | some op =>
      simp [h_op] at h
      cases op
      case Push p' =>
        intro hne
        subst hne
        simp at h
      all_goals (simp at h)
  · cases h

/-- Same invariant on `State.decoded`. -/
private theorem decoded_push_arg_some {s : State} {p : Operation.PushOp}
    {argOpt : Option (UInt256 × Nat)}
    (h : s.decoded = some (.Push p, argOpt)) :
    argOpt ≠ none := by
  unfold State.decoded at h
  cases h_da : Decode.decodeAt s.executionEnv.code s.pc.toNat with
  | none => simp [h_da] at h
  | some op_pair =>
    obtain ⟨op_inner, imm_inner⟩ := op_pair
    simp [h_da] at h
    obtain ⟨_, h_op_eq, h_imm_eq⟩ := h
    subst h_op_eq h_imm_eq
    exact decodeAt_push_arg_some h_da

/-- PUSH error path: the only error site is `.error .InvalidInstruction`
    when the immediate operand is missing for a positive-width PUSH. Via
    the decoder-invariant `decoded_push_arg_some`, this case is
    unreachable from `stepFE` — `decodeAt` always pairs a `.Push p`
    with `some (UInt256.ofNat n, w)`. -/
theorem push_sound_error (s : State) (op : Operation.PushOp)
    (argOpt : Option (UInt256 × Nat))
    (h_dec : s.decoded = some (.Push op, argOpt))
    (h_gas : Gas.baseCost s.fork (.Push op) ≤ s.gasAvailable)
    {e : ExecutionException}
    (h : stepF.push s (s.consumeGas (Gas.baseCost s.fork (.Push op)) h_gas) op argOpt
           = .error e) :
    StepRunning s ({ s with halt := .Exception e }) := by
  unfold stepF.push at h
  obtain ⟨⟨w, hw⟩⟩ := op
  cases w with
  | zero => simp at h
  | succ k =>
    cases h_arg : argOpt with
    | some d_n =>
      rw [h_arg] at h
      simp at h
    | none =>
      -- Unreachable: `decodeAt` never produces (.Push _, none).
      exact absurd h_arg (decoded_push_arg_some h_dec)

/-- `popN.go stk k acc = none → stk.length < k`. Mirror of `popN_go_correct`
    for the negative direction. -/
private theorem popN_go_eq_none_imp_len_lt :
    ∀ (k : Nat) (stk acc : List UInt256),
      stepF.popN.go stk k acc = none → stk.length < k := by
  intro k
  induction k with
  | zero =>
    intro stk acc h
    unfold stepF.popN.go at h
    simp at h
  | succ k' ih =>
    intro stk acc h
    match stk with
    | []          => simp [List.length]
    | top :: rest =>
      unfold stepF.popN.go at h
      simp at h
      have := ih rest (top :: acc) h
      simp [List.length]; omega

/-- `popN stk k = none → stk.length < k`. -/
private theorem popN_eq_none_imp_len_lt (stk : List UInt256) (k : Nat)
    (h : stepF.popN stk k = none) : stk.length < k := by
  unfold stepF.popN at h
  exact popN_go_eq_none_imp_len_lt k stk [] h

/-- LOG error path. Sites:
    1. `StaticModeViolation` when `permitStateMutation = false` (since
       `.Log _` is state-mutating per `Operation.isStateMutating`).
    2. Stack underflow on `[]` / `[_]`.
    3. `OutOfGas` on `chargeMem` (memory-expansion budget).
    4. `OutOfGas` on `Gas.logDataCost size` (per-byte fee budget).
    5. Stack underflow when `popN rest op.topics.val = none` (fewer
       topic slots than the operation requires). -/
theorem log_sound_error (s : State) (op : Operation.LogOp)
    (h_dec : s.decodedOp = some (.Log op))
    (h_gas : Gas.baseCost s.fork (.Log op) ≤ s.gasAvailable)
    {e : ExecutionException}
    (h : stepF.log s (s.consumeGas (Gas.baseCost s.fork (.Log op)) h_gas) op = .error e) :
    StepRunning s ({ s with halt := .Exception e }) := by
  unfold stepF.log at h
  by_cases h_perm : ¬ s.executionEnv.permitStateMutation
  · -- Static-mode violation.
    simp [h_perm] at h
    unfold static at h
    cases h
    refine mk_staticMode h_dec (rfl : s.stack = s.stack) ?_ ?_
    · show (Operation.Log op).isStateMutating = true; rfl
    · simp at h_perm; exact h_perm
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
          -- popN arm: either it returns `some` (success → contradiction)
          -- or `none` → underflow.
          cases h_pop : stepF.popN rest op.topics.val with
          | some p => obtain ⟨topics, rest'⟩ := p
                      simp [h_pop] at h
          | none =>
            simp [h_pop] at h
            unfold underflow at h
            cases h
            -- topics.val + 2 ≤ s.stack.length is what we'd need for popN to succeed;
            -- popN = none means rest.length < op.topics.val, so
            -- s.stack.length = rest.length + 2 < op.topics.val + 2 = popArity.
            refine mk_underflow h_dec h_stack ?_
            have h_pop_len : rest.length < op.topics.val := popN_eq_none_imp_len_lt _ _ h_pop
            simp only [List.length, Operation.popArity]
            omega
        · simp [h_dyn] at h
          cases h
          set base := Gas.baseCost s.fork (.Log op) with hbase
          set md := MachineState.memCost (MachineState.activeWordsAfter
                      s.activeWords.toNat offset.toNat size.toNat)
                    - MachineState.memCost s.activeWords.toNat with hmd
          set ldc := Gas.logDataCost size with hldc
          have h_mem' : md ≤ s.gasAvailable - base := by
            simp only [State.canExpandMemory, State.consumeGas,
                       MachineState.memExpansionDelta, ← hbase, ← hmd] at h_mem
            exact h_mem
          have h_dyn' : s.gasAvailable - base - md < ldc := by
            simp only [State.consumeGas, State.consumeMemExp, ← hbase, ← hmd] at h_dyn
            omega
          refine mk_outOfGas h_dec h_stack (base + md + ldc) ?_ ?_
          · show base ≤ base + md + ldc; omega
          · show s.gasAvailable < base + md + ldc; omega
      · simp [h_mem] at h
        cases h
        set base := Gas.baseCost s.fork (.Log op) with hbase
        set md := MachineState.memCost (MachineState.activeWordsAfter
                    s.activeWords.toNat offset.toNat size.toNat)
                  - MachineState.memCost s.activeWords.toNat with hmd
        have h_mem' : ¬ md ≤ s.gasAvailable - base := by
          simp only [State.canExpandMemory, State.consumeGas,
                     MachineState.memExpansionDelta, ← hbase, ← hmd] at h_mem
          exact h_mem
        refine mk_outOfGas h_dec h_stack (base + md) (Nat.le_add_right _ _) ?_
        omega
    | [], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])

/-- System error path. The most error-dense helper.

    Sites by op:
    * `RETURN`/`REVERT`: 2-arg underflow + `chargeMem`-`OutOfGas`.
    * `INVALID`: explicit `.InvalidInstruction`.
    * `CALL`: 7-arg underflow + `StaticModeViolation` (value-NZ in static) +
      `chargeMem2`-`OutOfGas` + surcharge-`OutOfGas` + forwarded-`OutOfGas`.
    * `CALLCODE`: 7-arg underflow + 3 `OutOfGas` sites.
    * `DELEGATECALL`/`STATICCALL`: 6-arg underflow + 2 `OutOfGas` sites.
    * `SELFDESTRUCT`: 1-arg underflow + `StaticModeViolation` + surcharge-`OutOfGas`.
    * `CREATE`/`CREATE2`: 3-arg/4-arg underflow + `StaticModeViolation` +
      `chargeMem`-`OutOfGas` + (CREATE2 only) hashCost-`OutOfGas` +
      forwarded-`OutOfGas` + (CREATE only) unreachable `InvalidInstruction`
      from `createAddress = none`.

    *Several deeper `OutOfGas` sites in the CALL/CREATE families are
    sorry'd*: the cost-witness reconstruction beyond `chargeMem`+committed
    cost requires threading multiple intermediate `consumeGas` results
    through the surcharge, `forwardGas`, and EIP-150 `allButOneSixtyFourth`
    computations. The proof shape is the same `set base/md/x with hbase`
    abstraction trick used in `keccak`/`log`/`env`/`stackMemFlow`, but with
    a deeper chain of intermediate states. Closing them is mechanical but
    out of scope for this single session. -/
theorem system_sound_error (s : State) (op : Operation.SystemOps)
    (h_dec : s.decodedOp = some (.System op))
    (h_gas : Gas.baseCost s.fork (.System op) ≤ s.gasAvailable)
    {e : ExecutionException}
    (h : stepF.system s (s.consumeGas (Gas.baseCost s.fork (.System op)) h_gas) op
           = .error e) :
    StepRunning s ({ s with halt := .Exception e }) := by
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
      · simp [h_mem] at h
        cases h
        set base := Gas.baseCost s.fork (.System .RETURN) with hbase
        set md := MachineState.memCost (MachineState.activeWordsAfter
                    s.activeWords.toNat offset.toNat size.toNat)
                  - MachineState.memCost s.activeWords.toNat with hmd
        have h_mem' : ¬ md ≤ s.gasAvailable - base := by
          simp only [State.canExpandMemory, State.consumeGas,
                     MachineState.memExpansionDelta, ← hbase, ← hmd] at h_mem
          exact h_mem
        refine mk_outOfGas h_dec h_stack (base + md) (Nat.le_add_right _ _) ?_
        omega
    | [], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
  | REVERT =>
    match h_stack : s.stack, h with
    | offset :: size :: rest, h =>
      unfold chargeMem at h
      by_cases h_mem :
          (s.consumeGas (Gas.baseCost s.fork (.System .REVERT)) h_gas).canExpandMemory
            offset.toNat size.toNat
      · simp [h_mem] at h
      · simp [h_mem] at h
        cases h
        set base := Gas.baseCost s.fork (.System .REVERT) with hbase
        set md := MachineState.memCost (MachineState.activeWordsAfter
                    s.activeWords.toNat offset.toNat size.toNat)
                  - MachineState.memCost s.activeWords.toNat with hmd
        have h_mem' : ¬ md ≤ s.gasAvailable - base := by
          simp only [State.canExpandMemory, State.consumeGas,
                     MachineState.memExpansionDelta, ← hbase, ← hmd] at h_mem
          exact h_mem
        refine mk_outOfGas h_dec h_stack (base + md) (Nat.le_add_right _ _) ?_
        omega
    | [], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
  | INVALID =>
    cases h
    exact mk_invalidOp h_dec rfl
  | CALL =>
    match h_stack : s.stack, h with
    | gasArg :: toArg :: value :: argsOff :: argsLen :: retOff :: retLen :: rest, h =>
      by_cases h_static : ¬ s.executionEnv.permitStateMutation ∧ value.toNat ≠ 0
      · simp only [if_pos h_static, static] at h
        cases h
        refine mk_callStatic h_dec h_stack gasArg toArg value argsOff argsLen retOff
          retLen rest rfl ?_ h_static.2
        rcases Bool.eq_false_or_eq_true s.executionEnv.permitStateMutation with hp | hp
        · exact absurd hp h_static.1
        · exact hp
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
          set surch := Gas.callSurcharge s.fork (value.toNat != 0)
                (((s.consumeGas base h_gas).consumeMemExp2 argsOff.toNat argsLen.toNat
                  retOff.toNat retLen.toNat h_mem).accountMap
                  (AccountAddress.ofUInt256 toArg)).isEmpty with hsurch
          split at h
          · rename_i h_sc
            -- surcharge OK; check forwarded (gas-cap), then depth/balance.
            split at h
            · -- forwarded OK: both inner branches (silent fail /
              -- successful call) return .ok, so h is contradictory.
              split at h
              · cases h  -- fail branch returns .ok
              · cases h  -- successful CALL returns .ok
            · -- forwarded OOG: pick cost = s.gasAvailable + 1.
              cases h
              refine mk_outOfGas h_dec h_stack (s.gasAvailable + 1) ?_ ?_
              · show base ≤ s.gasAvailable + 1
                omega
              · omega
          · -- surcharge OOG: pick cost = s.gasAvailable + 1.
            cases h
            refine mk_outOfGas h_dec h_stack (s.gasAvailable + 1) ?_ ?_
            · show base ≤ s.gasAvailable + 1; omega
            · omega
        · -- chargeMem2 OOG
          simp [h_mem] at h
          cases h
          set base := Gas.baseCost s.fork (.System .CALL) with hbase
          set md := MachineState.memCost
                      (MachineState.activeWordsAfter
                        (MachineState.activeWordsAfter s.activeWords.toNat
                          argsOff.toNat argsLen.toNat)
                        retOff.toNat retLen.toNat)
                    - MachineState.memCost s.activeWords.toNat with hmd
          have h_mem' : ¬ md ≤ s.gasAvailable - base := by
            simp only [State.canExpandMemory2, State.consumeGas,
                       MachineState.memExpansionDelta2, ← hbase, ← hmd] at h_mem
            exact h_mem
          refine mk_outOfGas h_dec h_stack (base + md) (Nat.le_add_right _ _) ?_
          omega
    | [], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_, _], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_, _, _], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_, _, _, _], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_, _, _, _, _], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_, _, _, _, _, _], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
  | CALLCODE =>
    match h_stack : s.stack, h with
    | gasArg :: toArg :: value :: argsOff :: argsLen :: retOff :: retLen :: rest, h =>
      unfold chargeMem2 at h
      by_cases h_mem :
          (s.consumeGas (Gas.baseCost s.fork (.System .CALLCODE)) h_gas).canExpandMemory2
            argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat
      · simp only [h_mem, dif_pos] at h
        set base := Gas.baseCost s.fork (.System .CALLCODE) with hbase
        split at h
        · -- surcharge OK; check forwarded (gas-cap), then depth/balance.
          split at h
          · -- forwarded OK: both inner branches return .ok.
            split at h
            · cases h  -- fail branch
            · cases h  -- successful CALLCODE
          · cases h  -- forwarded OOG
            refine mk_outOfGas h_dec h_stack (s.gasAvailable + 1) ?_ ?_
            · show base ≤ s.gasAvailable + 1; omega
            · omega
        · -- surcharge OOG
          cases h
          refine mk_outOfGas h_dec h_stack (s.gasAvailable + 1) ?_ ?_
          · show base ≤ s.gasAvailable + 1; omega
          · omega
      · simp [h_mem] at h
        cases h
        set base := Gas.baseCost s.fork (.System .CALLCODE) with hbase
        refine mk_outOfGas h_dec h_stack (s.gasAvailable + 1) ?_ ?_
        · show base ≤ s.gasAvailable + 1; omega
        · omega
    | [], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_, _], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_, _, _], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_, _, _, _], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_, _, _, _, _], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_, _, _, _, _, _], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
  | DELEGATECALL =>
    match h_stack : s.stack, h with
    | gasArg :: toArg :: argsOff :: argsLen :: retOff :: retLen :: rest, h =>
      unfold chargeMem2 at h
      by_cases h_mem :
          (s.consumeGas (Gas.baseCost s.fork (.System .DELEGATECALL)) h_gas).canExpandMemory2
            argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat
      · simp only [h_mem, dif_pos] at h
        set base := Gas.baseCost s.fork (.System .DELEGATECALL) with hbase
        -- Outermost split is now on `hcs` (EIP-2929 cold surcharge); then
        -- `hfw` (gas-cap); then depth.
        split at h
        · -- cold surcharge affordable
          split at h
          · -- forwarded OK: both inner branches return .ok, so h is contradictory.
            split at h
            · cases h  -- depth-≥-1024 branch returns .ok
            · cases h  -- forwarded + depth OK branch returns .ok
          · cases h  -- forwarded OOG
            refine mk_outOfGas h_dec h_stack (s.gasAvailable + 1) ?_ ?_
            · show base ≤ s.gasAvailable + 1; omega
            · omega
        · cases h  -- cold surcharge OOG
          refine mk_outOfGas h_dec h_stack (s.gasAvailable + 1) ?_ ?_
          · show base ≤ s.gasAvailable + 1; omega
          · omega
      · simp [h_mem] at h
        cases h
        set base := Gas.baseCost s.fork (.System .DELEGATECALL) with hbase
        refine mk_outOfGas h_dec h_stack (s.gasAvailable + 1) ?_ ?_
        · show base ≤ s.gasAvailable + 1; omega
        · omega
    | [], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_, _], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_, _, _], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_, _, _, _], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_, _, _, _, _], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
  | STATICCALL =>
    match h_stack : s.stack, h with
    | gasArg :: toArg :: argsOff :: argsLen :: retOff :: retLen :: rest, h =>
      unfold chargeMem2 at h
      by_cases h_mem :
          (s.consumeGas (Gas.baseCost s.fork (.System .STATICCALL)) h_gas).canExpandMemory2
            argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat
      · simp only [h_mem, dif_pos] at h
        set base := Gas.baseCost s.fork (.System .STATICCALL) with hbase
        -- Same outer-hcs / hfw / depth ordering as DELEGATECALL above.
        split at h
        · split at h
          · split at h
            · cases h  -- depth-≥-1024 returns .ok
            · cases h  -- forwarded + depth OK returns .ok
          · cases h  -- forwarded OOG
            refine mk_outOfGas h_dec h_stack (s.gasAvailable + 1) ?_ ?_
            · show base ≤ s.gasAvailable + 1; omega
            · omega
        · cases h  -- cold surcharge OOG
          refine mk_outOfGas h_dec h_stack (s.gasAvailable + 1) ?_ ?_
          · show base ≤ s.gasAvailable + 1; omega
          · omega
      · simp [h_mem] at h
        cases h
        set base := Gas.baseCost s.fork (.System .STATICCALL) with hbase
        refine mk_outOfGas h_dec h_stack (s.gasAvailable + 1) ?_ ?_
        · show base ≤ s.gasAvailable + 1; omega
        · omega
    | [], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_, _], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_, _, _], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_, _, _, _], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_, _, _, _, _], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
  | SELFDESTRUCT =>
    match h_stack : s.stack, h with
    | beneficiary :: rest, h =>
      by_cases h_perm : ¬ s.executionEnv.permitStateMutation
      · simp only [if_pos h_perm, static] at h
        cases h
        refine mk_staticMode h_dec h_stack ?_ ?_
        · show (Operation.System .SELFDESTRUCT).isStateMutating = true; rfl
        · simp at h_perm; exact h_perm
      · simp only [if_neg h_perm] at h
        split at h
        · cases h  -- surcharge OK; .ok contradicts .error
        · -- surcharge OOG
          cases h
          set base := Gas.baseCost s.fork (.System .SELFDESTRUCT) with hbase
          refine mk_outOfGas h_dec h_stack (s.gasAvailable + 1) ?_ ?_
          · show base ≤ s.gasAvailable + 1; omega
          · omega
    | [], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
  | CREATE =>
    match h_stack : s.stack, h with
    | value :: offset :: size :: rest, h =>
      by_cases h_perm : ¬ s.executionEnv.permitStateMutation
      · simp only [if_pos h_perm, static] at h
        cases h
        refine mk_staticMode h_dec h_stack ?_ ?_
        · show (Operation.System .CREATE).isStateMutating = true; rfl
        · simp at h_perm; exact h_perm
      · simp only [if_neg h_perm] at h
        unfold chargeMem at h
        by_cases h_mem :
            (s.consumeGas (Gas.baseCost s.fork (.System .CREATE)) h_gas).canExpandMemory
              offset.toNat size.toNat
        · simp only [h_mem, dif_pos] at h
          set base := Gas.baseCost s.fork (.System .CREATE) with hbase
          split at h
          · cases h  -- depth/balance fail returns .ok
          · rename_i h_take
            -- `createAddress` is total now; only the forwarded-OOG and
            -- collision branches remain (the latter two are `.ok`).
            split at h
            · split at h
              all_goals cases h
            · -- forwarded OOG
              cases h
              refine mk_outOfGas h_dec h_stack (s.gasAvailable + 1) ?_ ?_
              · show base ≤ s.gasAvailable + 1; omega
              · omega
        · simp [h_mem] at h
          cases h
          set base := Gas.baseCost s.fork (.System .CREATE) with hbase
          refine mk_outOfGas h_dec h_stack (s.gasAvailable + 1) ?_ ?_
          · show base ≤ s.gasAvailable + 1; omega
          · omega
    | [], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_, _], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
  | CREATE2 =>
    match h_stack : s.stack, h with
    | value :: offset :: size :: salt :: rest, h =>
      by_cases h_perm : ¬ s.executionEnv.permitStateMutation
      · simp only [if_pos h_perm, static] at h
        cases h
        refine mk_staticMode h_dec h_stack ?_ ?_
        · show (Operation.System .CREATE2).isStateMutating = true; rfl
        · simp at h_perm; exact h_perm
      · simp only [if_neg h_perm] at h
        unfold chargeMem at h
        by_cases h_mem :
            (s.consumeGas (Gas.baseCost s.fork (.System .CREATE2)) h_gas).canExpandMemory
              offset.toNat size.toNat
        · simp only [h_mem, dif_pos] at h
          set base := Gas.baseCost s.fork (.System .CREATE2) with hbase
          split at h
          · -- hashCost OK
            split at h
            · cases h  -- depth/balance fail returns .ok
            · split at h
              · split at h
                all_goals cases h
              · -- forwarded OOG
                cases h
                refine mk_outOfGas h_dec h_stack (s.gasAvailable + 1) ?_ ?_
                · show base ≤ s.gasAvailable + 1; omega
                · omega
          · -- hashCost OOG
            cases h
            refine mk_outOfGas h_dec h_stack (s.gasAvailable + 1) ?_ ?_
            · show base ≤ s.gasAvailable + 1; omega
            · omega
        · simp [h_mem] at h
          cases h
          set base := Gas.baseCost s.fork (.System .CREATE2) with hbase
          refine mk_outOfGas h_dec h_stack (s.gasAvailable + 1) ?_ ?_
          · show base ≤ s.gasAvailable + 1; omega
          · omega
    | [], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_, _], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_, _, _], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])

/-- StackMemFlow error path. The largest helper. Sites:
    * `POP`/`SLOAD`/`TLOAD`: 1-arg underflow.
    * `MLOAD`: underflow + `chargeMem`-`OutOfGas`.
    * `MSTORE`/`MSTORE8`: 2-arg underflow + `chargeMem`-`OutOfGas`.
    * `SSTORE`: `StaticModeViolation`, EIP-2200 sentry `OutOfGas`,
      2-arg underflow, dynamic `sstoreCost` `OutOfGas`.
    * `JUMP`: underflow + `BadJumpDestination`.
    * `JUMPI`: 2-arg underflow + `BadJumpDestination` (taken with bad dest).
    * `PC`/`JUMPDEST`/`MSIZE`/`GAS`: no error.
    * `TSTORE`: `StaticModeViolation` + 2-arg underflow.
    * `MCOPY`: 3-arg underflow + `chargeMem2`-`OutOfGas` + `copyWordCost`-`OutOfGas`. -/
theorem stackMemFlow_sound_error (s : State) (op : Operation.StackMemFlowOps)
    (h_dec : s.decodedOp = some (.StackMemFlow op))
    (h_gas : Gas.baseCost s.fork (.StackMemFlow op) ≤ s.gasAvailable)
    {e : ExecutionException}
    (h : stepF.stackMemFlow s (s.consumeGas (Gas.baseCost s.fork (.StackMemFlow op)) h_gas) op
           = .error e) :
    StepRunning s ({ s with halt := .Exception e }) := by
  unfold stepF.stackMemFlow at h
  cases op with
  | POP =>
    match h_stack : s.stack, h with
    | _ :: _, h => nomatch h
    | [], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
  | SLOAD =>
    match h_stack : s.stack, h with
    | key :: rest, h =>
      by_cases h_total : Gas.sloadTotal s key ≤ s.gasAvailable
      · simp [h_total] at h
      · simp [h_total] at h
        cases h
        refine mk_outOfGas h_dec h_stack (Gas.sloadTotal s key) ?_ ?_
        · show Gas.baseCost s.fork (.StackMemFlow .SLOAD)
               ≤ Gas.baseCost s.fork (.StackMemFlow .SLOAD) + Gas.sloadColdSurcharge s key
          omega
        · omega
    | [], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
  | TLOAD =>
    match h_stack : s.stack, h with
    | _ :: _, h => nomatch h
    | [], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
  | MLOAD =>
    match h_stack : s.stack, h with
    | offset :: rest, h =>
      unfold chargeMem at h
      by_cases h_mem :
          (s.consumeGas (Gas.baseCost s.fork (.StackMemFlow .MLOAD)) h_gas).canExpandMemory
            offset.toNat 32
      · simp [h_mem] at h
      · simp [h_mem] at h
        cases h
        set base := Gas.baseCost s.fork (.StackMemFlow .MLOAD) with hbase
        set md := MachineState.memCost (MachineState.activeWordsAfter
                    s.activeWords.toNat offset.toNat 32)
                  - MachineState.memCost s.activeWords.toNat with hmd
        have h_mem' : ¬ md ≤ s.gasAvailable - base := by
          simp only [State.canExpandMemory, State.consumeGas,
                     MachineState.memExpansionDelta, ← hbase, ← hmd] at h_mem
          exact h_mem
        refine mk_outOfGas h_dec h_stack (base + md) (Nat.le_add_right _ _) ?_
        omega
    | [], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
  | MSTORE =>
    match h_stack : s.stack, h with
    | offset :: value :: rest, h =>
      unfold chargeMem at h
      by_cases h_mem :
          (s.consumeGas (Gas.baseCost s.fork (.StackMemFlow .MSTORE)) h_gas).canExpandMemory
            offset.toNat 32
      · simp [h_mem] at h
      · simp [h_mem] at h
        cases h
        set base := Gas.baseCost s.fork (.StackMemFlow .MSTORE) with hbase
        set md := MachineState.memCost (MachineState.activeWordsAfter
                    s.activeWords.toNat offset.toNat 32)
                  - MachineState.memCost s.activeWords.toNat with hmd
        have h_mem' : ¬ md ≤ s.gasAvailable - base := by
          simp only [State.canExpandMemory, State.consumeGas,
                     MachineState.memExpansionDelta, ← hbase, ← hmd] at h_mem
          exact h_mem
        refine mk_outOfGas h_dec h_stack (base + md) (Nat.le_add_right _ _) ?_
        omega
    | [], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
  | MSTORE8 =>
    match h_stack : s.stack, h with
    | offset :: value :: rest, h =>
      unfold chargeMem at h
      by_cases h_mem :
          (s.consumeGas (Gas.baseCost s.fork (.StackMemFlow .MSTORE8)) h_gas).canExpandMemory
            offset.toNat 1
      · simp [h_mem] at h
      · simp [h_mem] at h
        cases h
        set base := Gas.baseCost s.fork (.StackMemFlow .MSTORE8) with hbase
        set md := MachineState.memCost (MachineState.activeWordsAfter
                    s.activeWords.toNat offset.toNat 1)
                  - MachineState.memCost s.activeWords.toNat with hmd
        have h_mem' : ¬ md ≤ s.gasAvailable - base := by
          simp only [State.canExpandMemory, State.consumeGas,
                     MachineState.memExpansionDelta, ← hbase, ← hmd] at h_mem
          exact h_mem
        refine mk_outOfGas h_dec h_stack (base + md) (Nat.le_add_right _ _) ?_
        omega
    | [], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
  | SSTORE =>
    by_cases h_perm : ¬ s.executionEnv.permitStateMutation
    · simp [h_perm] at h
      unfold static at h
      cases h
      refine mk_staticMode h_dec (rfl : s.stack = s.stack) ?_ ?_
      · show (Operation.StackMemFlow .SSTORE).isStateMutating = true; rfl
      · simp at h_perm; exact h_perm
    · simp [h_perm] at h
      by_cases h_sentry : Gas.sstoreSentry s.fork
                            (s.consumeGas (Gas.baseCost s.fork (.StackMemFlow .SSTORE))
                              h_gas).gasAvailable
      · -- Sentry OOG: only fires on Istanbul+. gas - base ≤ 2300.
        simp [h_sentry] at h
        cases h
        set base := Gas.baseCost s.fork (.StackMemFlow .SSTORE) with hbase
        -- Cost witness: base + 2301 > s.gasAvailable.
        refine mk_outOfGas h_dec rfl (base + 2301) ?_ ?_
        · show base ≤ base + 2301; omega
        · show s.gasAvailable < base + 2301
          unfold Gas.sstoreSentry at h_sentry
          split at h_sentry
          · simp at h_sentry
            simp only [State.consumeGas, ← hbase] at h_sentry
            omega
          · simp at h_sentry
      · simp [h_sentry] at h
        match h_stack : s.stack, h with
        | key :: value :: rest, h =>
          by_cases h_cost :
              Gas.sstoreCost s.fork
                (s.substate.originalStorage s.executionEnv.address key)
                ((s.accountMap s.executionEnv.address).storage key) value
              + Gas.sstoreColdSurcharge s key
              ≤ (s.consumeGas (Gas.baseCost s.fork (.StackMemFlow .SSTORE))
                  h_gas).gasAvailable
          · simp [h_cost] at h
          · simp [h_cost] at h
            cases h
            set base := Gas.baseCost s.fork (.StackMemFlow .SSTORE) with hbase
            set scost := Gas.sstoreCost s.fork
                  (s.substate.originalStorage s.executionEnv.address key)
                  ((s.accountMap s.executionEnv.address).storage key) value
                  + Gas.sstoreColdSurcharge s key with hscost
            have h_cost' : ¬ scost ≤ s.gasAvailable - base := by
              simp only [State.consumeGas, ] at h_cost
              exact h_cost
            refine mk_outOfGas h_dec h_stack (base + scost) (Nat.le_add_right _ _) ?_
            omega
        | [], h =>
          cases h
          exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
        | [_], h =>
          cases h
          exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
  | JUMP =>
    match h_stack : s.stack, h with
    | dest :: rest, h =>
      by_cases h_valid : Decode.isValidJumpDest s.executionEnv.code dest.toNat
      · simp [h_valid] at h
      · simp [h_valid] at h
        cases h
        refine mk_jumpBad h_dec h_stack dest rest rfl h_gas ?_
        simp at h_valid
        exact h_valid
    | [], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
  | JUMPI =>
    match h_stack : s.stack, h with
    | dest :: cond :: rest, h =>
      by_cases h_cond : cond.toNat = 0
      · simp [h_cond] at h
      · simp [h_cond] at h
        by_cases h_valid : Decode.isValidJumpDest s.executionEnv.code dest.toNat
        · simp [h_valid] at h
        · simp [h_valid] at h
          cases h
          refine mk_jumpiBad h_dec h_stack dest cond rest rfl h_gas ?_ ?_
          · show cond.toNat ≠ 0; exact h_cond
          · simp at h_valid; exact h_valid
    | [], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
  | PC | JUMPDEST | MSIZE | GAS => nomatch h
  | TSTORE =>
    by_cases h_perm : ¬ s.executionEnv.permitStateMutation
    · simp [h_perm] at h
      unfold static at h
      cases h
      refine mk_staticMode h_dec (rfl : s.stack = s.stack) ?_ ?_
      · show (Operation.StackMemFlow .TSTORE).isStateMutating = true; rfl
      · simp at h_perm; exact h_perm
    · simp [h_perm] at h
      match h_stack : s.stack, h with
      | _ :: _ :: _, h => nomatch h
      | [], h =>
        cases h
        exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
      | [_], h =>
        cases h
        exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
  | MCOPY =>
    match h_stack : s.stack, h with
    | destOff :: srcOff :: sz :: rest, h =>
      unfold chargeMem2 at h
      by_cases h_mem :
          (s.consumeGas (Gas.baseCost s.fork (.StackMemFlow .MCOPY)) h_gas).canExpandMemory2
            destOff.toNat sz.toNat srcOff.toNat sz.toNat
      · simp [h_mem] at h
        by_cases h_dyn : Gas.copyWordCost sz ≤
            ((s.consumeGas (Gas.baseCost s.fork (.StackMemFlow .MCOPY))
                            h_gas).consumeMemExp2 destOff.toNat sz.toNat
                              srcOff.toNat sz.toNat h_mem).gasAvailable
        · simp [h_dyn] at h
        · simp [h_dyn] at h
          cases h
          set base := Gas.baseCost s.fork (.StackMemFlow .MCOPY) with hbase
          set md := MachineState.memCost (MachineState.activeWordsAfter
                      (MachineState.activeWordsAfter s.activeWords.toNat
                        destOff.toNat sz.toNat) srcOff.toNat sz.toNat)
                    - MachineState.memCost s.activeWords.toNat with hmd
          set cwc := Gas.copyWordCost sz with hcwc
          have h_mem' : md ≤ s.gasAvailable - base := by
            simp only [State.canExpandMemory2, State.consumeGas,
                       MachineState.memExpansionDelta2, ← hbase, ← hmd] at h_mem
            exact h_mem
          have h_dyn' : s.gasAvailable - base - md < cwc := by
            simp only [State.consumeGas, State.consumeMemExp2, ← hbase, ← hmd] at h_dyn
            omega
          refine mk_outOfGas h_dec h_stack (base + md + cwc) ?_ ?_
          · show base ≤ base + md + cwc; omega
          · show s.gasAvailable < base + md + cwc; omega
      · simp [h_mem] at h
        cases h
        set base := Gas.baseCost s.fork (.StackMemFlow .MCOPY) with hbase
        set md := MachineState.memCost (MachineState.activeWordsAfter
                    (MachineState.activeWordsAfter s.activeWords.toNat
                      destOff.toNat sz.toNat) srcOff.toNat sz.toNat)
                  - MachineState.memCost s.activeWords.toNat with hmd
        have h_mem' : ¬ md ≤ s.gasAvailable - base := by
          simp only [State.canExpandMemory2, State.consumeGas,
                     MachineState.memExpansionDelta2, ← hbase, ← hmd] at h_mem
          exact h_mem
        refine mk_outOfGas h_dec h_stack (base + md) (Nat.le_add_right _ _) ?_
        omega
    | [], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])
    | [_, _], h =>
      cases h
      exact mk_underflow h_dec h_stack (by simp [Operation.popArity, List.length])

end stepF

/-- Universal bound: `op.pushArity ≤ 1024` for every op we model. Used in
    the stack-overflow case of `stepFE_sound_error` to derive
    `op.popArity ≤ s.stack.length` from `stepFE`'s overflow guard
    `length + pushArity > 1024 + popArity` (with `pushArity ≤ 1024`, get
    `length > popArity`). Max actual pushArity is 257 (`SwapN`/`DupN`). -/
private theorem Operation.pushArity_le_1024 (op : Operation) :
    op.pushArity ≤ 1024 := by
  cases op with
  | StopArith op => cases op <;> decide
  | CompBit op => cases op <;> decide
  | Keccak op => cases op; decide
  | Env op => cases op <;> decide
  | Block op => cases op <;> decide
  | StackMemFlow op => cases op <;> decide
  | Push p =>
    obtain ⟨⟨w, hw⟩⟩ := p
    show 1 ≤ 1024
    omega
  | Dup d =>
    obtain ⟨⟨i, hi⟩⟩ := d
    show i + 2 ≤ 1024
    omega
  | Swap e =>
    obtain ⟨⟨i, hi⟩⟩ := e
    show i + 2 ≤ 1024
    omega
  | DupN d =>
    obtain ⟨⟨i, hi⟩⟩ := d
    show i + 2 ≤ 1024
    omega
  | SwapN se =>
    obtain ⟨⟨i, hi⟩⟩ := se
    show i + 2 ≤ 1024
    omega
  | Exchange e =>
    show Nat.max (e.n + 1) (e.m + 1) + 1 ≤ 1024
    have hn : e.n ≤ 15 := by
      show e.packed.val >>> 4 ≤ 15
      have hpacked := e.packed.isLt
      omega
    have hm : e.m ≤ 15 := by
      show e.packed.val &&& 0xf ≤ 15
      have := Nat.and_le_right (n := e.packed.val) (m := 0xf)
      omega
    simp only [Nat.max_def]; split <;> omega
  | Log l => show 0 ≤ 1024; omega
  | System op => cases op <;> decide

/-- Outer wrapper: `stepFE s = .error e` implies a `StepRunning` derivation
    that lands in `{ s with halt := .Exception e }`. Mirrors `stepFE_sound`
    structurally — same outer dispatch tree, but the `.error` branches now
    discharge via the 14 per-helper `*_sound_error` lemmas plus the
    top-level `decodeFailure`/`stackOverflow`/`outOfGas` constructors. -/
private theorem stepFE_sound_error' (s : State) (e : ExecutionException)
    (h : stepFE s = .error e) :
    s.halt = .Running ∧
    Precompile.isPrecompile s.executionEnv.fork s.executionEnv.codeAddr = false ∧
    StepRunning s ({ s with halt := .Exception e }) := by
  unfold stepFE at h
  simp only [Id.run] at h
  split at h
  · -- s.halt = .Running
    rename_i h_running
    split at h
    · -- Precompile arm: both `.success` and `.outOfGas` return `.ok`.
      split at h <;> cases h
    · -- Non-precompile path: capture isPrecompile = false and dispatch.
      rename_i h_npc
      refine ⟨h_running, h_npc, ?_⟩
      split at h
      · -- decoded = none → InvalidInstruction
        rename_i h_none
        cases h
        exact StepRunning.decodeFailure s h_none
      · rename_i op argOpt h_dec
        split at h
        · -- stack overflow
          rename_i h_over
          cases h
          refine StepRunning.stackOverflow s op (State.decoded_to_op h_dec) ?_ ?_
          · have h_bound := Operation.pushArity_le_1024 op
            simp at h_over
            omega
          · have h_bound := Operation.pushArity_le_1024 op
            simp at h_over
            omega
        · split at h
          · -- gas ≥ cost
            rename_i h_gas
            cases op with
            | StopArith op =>
              exact stepF.stopArith_sound_error s op (State.decoded_to_op h_dec) h_gas h
            | CompBit op =>
              exact stepF.compBit_sound_error s op (State.decoded_to_op h_dec) h_gas h
            | Keccak op =>
              exact stepF.keccak_sound_error s op (State.decoded_to_op h_dec) h_gas h
            | Env op =>
              exact stepF.env_sound_error s op (State.decoded_to_op h_dec) h_gas h
            | Block op =>
              exact stepF.block_sound_error s op (State.decoded_to_op h_dec) h_gas h
            | StackMemFlow op =>
              exact stepF.stackMemFlow_sound_error s op (State.decoded_to_op h_dec) h_gas h
            | Push op =>
              exact stepF.push_sound_error s op argOpt h_dec h_gas h
            | Dup op =>
              exact stepF.dup_sound_error s op (State.decoded_to_op h_dec) h_gas h
            | Swap op =>
              exact stepF.swap_sound_error s op (State.decoded_to_op h_dec) h_gas h
            | DupN op =>
              exact stepF.dupN_sound_error s op (State.decoded_to_op h_dec) h_gas h
            | SwapN op =>
              exact stepF.swapN_sound_error s op (State.decoded_to_op h_dec) h_gas h
            | Exchange op =>
              exact stepF.exchange_sound_error s op (State.decoded_to_op h_dec) h_gas h
            | Log op =>
              exact stepF.log_sound_error s op (State.decoded_to_op h_dec) h_gas h
            | System op =>
              exact stepF.system_sound_error s op (State.decoded_to_op h_dec) h_gas h
          · -- gas < cost: top-level OOG
            cases h
            rename_i h_ngas
            refine StepRunning.outOfGas s op (Gas.baseCost s.fork op)
              (State.decoded_to_op h_dec) (Nat.le_refl _) ?_
            simp at h_ngas
            exact h_ngas
  -- Non-Running halts: stepFE returns `.ok _` only; contradicts `.error e`.
  all_goals (split at h <;> cases h)

/-- **Unified soundness of the executable shadow.** Whatever `stepFE`
    returns — `.ok s'` for an ordinary transition, `.error e` for an
    in-frame exception — the relational `Step` justifies the same
    outcome: on `.ok s'`, `Step s s'`; on `.error e`, `Step s` to the
    state with `halt := .Exception e`. This is the single combined
    statement; the `.ok` and `.error` directions live as private
    helpers `stepFE_sound_ok'` and `stepFE_sound_error'`.

    Key techniques inside the two directions:
    - The `s.gasAvailable + 1` cost-witness trick discharges the
      `StepRunning.outOfGas` obligations in the deeper gas-commitment
      chains (CALL/CREATE families) without reconstructing the
      multi-stage post-state. Any `cost ≥ baseCost` with
      `s.gasAvailable < cost` works, and `s.gasAvailable + 1`
      satisfies both since `baseCost ≤ s.gasAvailable` (from `h_gas`).
    - `Operation.pushArity_le_1024` discharges the
      `StepRunning.stackOverflow` premises in the outer wrapper.
    - `decoded_push_arg_some` (decoder invariant) closes the
      unreachable `(.Push p, none)` arm of `stepF.push`.
    - `EvmSemantics.createAddress` returns `AccountAddress` directly
      (rather than `Option AccountAddress`) by taking a `UInt256`
      nonce. Totality is provided internally by `Option.get` plus
      `Rlp.encodeAddrNonce_isSome`. This removes the unreachable
      `createAddress = none` branch from both `stepF.system .CREATE`
      and the corresponding `StepRunning.create` / `createCollision`
      constructors (which previously had a `h_addr : createAddress …
      = some newAddr` premise; now `newAddr` is just the direct
      `createAddress` application).

    Helpers: `mk_underflow`, `mk_outOfGas`, `mk_staticMode`,
    `mk_invalidOp`, `mk_invalidMem`, `mk_jumpBad`, `mk_jumpiBad`,
    `mk_callStatic`. -/
theorem stepFE_sound (s : State) (h_nd : ¬ s.isDone) :
    Step s (match stepFE s with
            | .ok s' => s'
            | .error e => { s with halt := .Exception e }) := by
  cases h_fe : stepFE s with
  | ok s' => exact stepFE_sound_ok' s s' h_nd h_fe
  | error e =>
    obtain ⟨h_nr, h_npc, h_step⟩ := stepFE_sound_error' s e h_fe
    exact .running h_nr h_npc h_step

/-- Soundness on the public total `stepF`. Trivial corollary of
    `stepFE_sound` plus the definitional unfolding of `stepF`. -/
theorem stepF_sound (s : State) (h_nd : ¬ s.isDone) : Step s (stepF s) :=
  stepFE_sound s h_nd

end EVM
end EvmSemantics
