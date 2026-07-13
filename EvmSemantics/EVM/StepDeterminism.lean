module

public import EvmSemantics.EVM.StepComplete.Arith
public import EvmSemantics.EVM.StepComplete.CompBit
public import EvmSemantics.EVM.StepComplete.EnvReads
public import EvmSemantics.EVM.StepComplete.CopiesKeccak
public import EvmSemantics.EVM.StepComplete.Block
public import EvmSemantics.EVM.StepComplete.StackMem
public import EvmSemantics.EVM.StepComplete.Flow
public import EvmSemantics.EVM.StepComplete.Calls
public import EvmSemantics.EVM.StepComplete.Creates
public import EvmSemantics.EVM.StepComplete.Exceptions
public import EvmSemantics.EVM.StepComplete.Oog
public import EvmSemantics.EVM.StepComplete.Underflow
public import EvmSemantics.EVM.Equiv

/-!
`StepDeterminism` — the small-step relation `Step` is **deterministic**,
proven via **completeness** of the executable shadow: every relational
transition is exactly the one `stepF` computes.

* `step_complete : Step s s' → stepF s = s'` — the converse of
  `stepF_sound`. Each `StepRunning` constructor's premises pin every
  branch `stepFE` takes (the per-constructor cases live in
  `EvmSemantics/EVM/StepComplete/`); the `StepReturn` and precompile
  constructors mirror `stepFE`'s halted and precompile arms directly.
* `step_deterministic : Step s s₁ → Step s s₂ → s₁ = s₂` — immediate:
  both successors equal `stepF s`.
* `step_iff_stepF : ¬ s.isDone → (Step s s' ↔ stepF s = s')` — together
  with `stepF_sound`, `Step` is exactly the graph of `stepF` on non-done
  states.

Historical note: before the priority premises were added to the
exception rules (and the stack-overflow guards to the success rules),
`Step` was *not* deterministic — e.g. on a running frame decoding `ADD`
with an empty stack and zero gas, both `stackUnderflow` and `outOfGas`
fired, and their successors differ in which exception is reported. The
premises now encode `stepF`'s check order, making the reported kind
unique.
-/

@[expose] public section

namespace EvmSemantics
namespace EVM

/-- `stepFE` on a *halted* frame with a suspended caller pops and
    resumes it via `State.resumeByHalt`. -/
theorem stepFE_resume {s : State} {f : Frame} {rest : List Frame}
    (h_nr : s.halt ≠ .Running)
    (h_cs : s.callStack = f :: rest) :
    stepFE s = .ok (s.resumeByHalt f rest) := by
  unfold stepFE
  simp only [Id.run]
  rcases hh : s.halt with _ | _ | _ | _ | e
  · exact absurd hh h_nr
  all_goals simp only [hh, h_cs]

/-- Completeness of the per-opcode layer: a `StepRunning` transition out
    of a running, non-precompile frame is exactly the `stepF` step. -/
theorem stepRunning_complete {s s' : State}
    (h_run : s.halt = .Running)
    (h_np : Precompile.isPrecompile s.executionEnv.fork
              s.executionEnv.codeAddr = false)
    (h : StepRunning s s') :
    stepF s = s' := by
  cases h with
  | add a b rest h_op h_gas h_stack h_cap =>
      exact StepComplete.complete_add s a b rest h_op h_gas h_stack h_cap h_run h_np
  | mul a b rest h_op h_gas h_stack h_cap =>
      exact StepComplete.complete_mul s a b rest h_op h_gas h_stack h_cap h_run h_np
  | sub a b rest h_op h_gas h_stack h_cap =>
      exact StepComplete.complete_sub s a b rest h_op h_gas h_stack h_cap h_run h_np
  | div a b rest h_op h_gas h_stack h_cap =>
      exact StepComplete.complete_div s a b rest h_op h_gas h_stack h_cap h_run h_np
  | sdiv a b rest h_op h_gas h_stack h_cap =>
      exact StepComplete.complete_sdiv s a b rest h_op h_gas h_stack h_cap h_run h_np
  | mod a b rest h_op h_gas h_stack h_cap =>
      exact StepComplete.complete_mod s a b rest h_op h_gas h_stack h_cap h_run h_np
  | smod a b rest h_op h_gas h_stack h_cap =>
      exact StepComplete.complete_smod s a b rest h_op h_gas h_stack h_cap h_run h_np
  | addmod a b n rest h_op h_gas h_stack h_cap =>
      exact StepComplete.complete_addmod s a b n rest h_op h_gas h_stack h_cap h_run h_np
  | mulmod a b n rest h_op h_gas h_stack h_cap =>
      exact StepComplete.complete_mulmod s a b n rest h_op h_gas h_stack h_cap h_run h_np
  | exp a b rest h_op h_gas h_stack h_cap =>
      exact StepComplete.complete_exp s a b rest h_op h_gas h_stack h_cap h_run h_np
  | signextend b x rest h_op h_gas h_stack h_cap =>
      exact StepComplete.complete_signextend s b x rest h_op h_gas h_stack h_cap h_run h_np
  | lt a b rest h_op h_gas h_stack h_cap =>
      exact StepComplete.complete_lt s a b rest h_op h_gas h_stack h_cap h_run h_np
  | gt a b rest h_op h_gas h_stack h_cap =>
      exact StepComplete.complete_gt s a b rest h_op h_gas h_stack h_cap h_run h_np
  | slt a b rest h_op h_gas h_stack h_cap =>
      exact StepComplete.complete_slt s a b rest h_op h_gas h_stack h_cap h_run h_np
  | sgt a b rest h_op h_gas h_stack h_cap =>
      exact StepComplete.complete_sgt s a b rest h_op h_gas h_stack h_cap h_run h_np
  | eq a b rest h_op h_gas h_stack h_cap =>
      exact StepComplete.complete_eq s a b rest h_op h_gas h_stack h_cap h_run h_np
  | iszero a rest h_op h_gas h_stack h_cap =>
      exact StepComplete.complete_iszero s a rest h_op h_gas h_stack h_cap h_run h_np
  | and a b rest h_op h_gas h_stack h_cap =>
      exact StepComplete.complete_and s a b rest h_op h_gas h_stack h_cap h_run h_np
  | or a b rest h_op h_gas h_stack h_cap =>
      exact StepComplete.complete_or s a b rest h_op h_gas h_stack h_cap h_run h_np
  | xor_ a b rest h_op h_gas h_stack h_cap =>
      exact StepComplete.complete_xor_ s a b rest h_op h_gas h_stack h_cap h_run h_np
  | not a rest h_op h_gas h_stack h_cap =>
      exact StepComplete.complete_not s a rest h_op h_gas h_stack h_cap h_run h_np
  | clz a rest h_op h_gas h_stack h_cap =>
      exact StepComplete.complete_clz s a rest h_op h_gas h_stack h_cap h_run h_np
  | byte_ i x rest h_op h_gas h_stack h_cap =>
      exact StepComplete.complete_byte_ s i x rest h_op h_gas h_stack h_cap h_run h_np
  | shl shift v rest h_op h_gas h_stack h_cap =>
      exact StepComplete.complete_shl s shift v rest h_op h_gas h_stack h_cap h_run h_np
  | shr shift v rest h_op h_gas h_stack h_cap =>
      exact StepComplete.complete_shr s shift v rest h_op h_gas h_stack h_cap h_run h_np
  | sar shift v rest h_op h_gas h_stack h_cap =>
      exact StepComplete.complete_sar s shift v rest h_op h_gas h_stack h_cap h_run h_np
  | keccak256 offset size rest h_op h_stack h_gas h_cap =>
      exact StepComplete.complete_keccak256 s offset size rest h_op h_stack h_gas h_cap h_run h_np
  | address h_op h_gas h_cap =>
      exact StepComplete.complete_address s h_op h_gas h_cap h_run h_np
  | balance addr rest h_op h_gas h_stack h_cap =>
      exact StepComplete.complete_balance s addr rest h_op h_gas h_stack h_cap h_run h_np
  | origin h_op h_gas h_cap =>
      exact StepComplete.complete_origin s h_op h_gas h_cap h_run h_np
  | caller h_op h_gas h_cap =>
      exact StepComplete.complete_caller s h_op h_gas h_cap h_run h_np
  | callvalue h_op h_gas h_cap =>
      exact StepComplete.complete_callvalue s h_op h_gas h_cap h_run h_np
  | calldataload i rest h_op h_gas h_stack h_cap =>
      exact StepComplete.complete_calldataload s i rest h_op h_gas h_stack h_cap h_run h_np
  | calldatasize h_op h_gas h_cap =>
      exact StepComplete.complete_calldatasize s h_op h_gas h_cap h_run h_np
  | calldatacopy destOff srcOff sz rest h_op h_stack h_gas h_cap =>
      exact StepComplete.complete_calldatacopy s destOff srcOff sz rest h_op h_stack h_gas h_cap
        h_run h_np
  | codesize h_op h_gas h_cap =>
      exact StepComplete.complete_codesize s h_op h_gas h_cap h_run h_np
  | codecopy destOff srcOff sz rest h_op h_stack h_gas h_cap =>
      exact StepComplete.complete_codecopy s destOff srcOff sz rest h_op h_stack h_gas h_cap h_run
        h_np
  | gasprice h_op h_gas h_cap =>
      exact StepComplete.complete_gasprice s h_op h_gas h_cap h_run h_np
  | extcodesize addr rest h_op h_gas h_stack h_cap =>
      exact StepComplete.complete_extcodesize s addr rest h_op h_gas h_stack h_cap h_run h_np
  | extcodecopy addr destOff srcOff sz rest h_op h_stack h_gas h_cap =>
      exact StepComplete.complete_extcodecopy s addr destOff srcOff sz rest h_op h_stack h_gas
        h_cap h_run h_np
  | returndatasize h_op h_gas h_cap =>
      exact StepComplete.complete_returndatasize s h_op h_gas h_cap h_run h_np
  | returndatacopy destOff srcOff sz rest h_op h_stack h_inbounds h_gas h_cap =>
      exact StepComplete.complete_returndatacopy s destOff srcOff sz rest h_op h_stack h_inbounds
        h_gas h_cap h_run h_np
  | extcodehash addr rest h_op h_gas h_stack h_cap =>
      exact StepComplete.complete_extcodehash s addr rest h_op h_gas h_stack h_cap h_run h_np
  | blockhash n rest h_op h_gas h_stack h_cap =>
      exact StepComplete.complete_blockhash s n rest h_op h_gas h_stack h_cap h_run h_np
  | coinbase h_op h_gas h_cap =>
      exact StepComplete.complete_coinbase s h_op h_gas h_cap h_run h_np
  | timestamp h_op h_gas h_cap =>
      exact StepComplete.complete_timestamp s h_op h_gas h_cap h_run h_np
  | number h_op h_gas h_cap =>
      exact StepComplete.complete_number s h_op h_gas h_cap h_run h_np
  | prevrandao h_op h_gas h_cap =>
      exact StepComplete.complete_prevrandao s h_op h_gas h_cap h_run h_np
  | gaslimit h_op h_gas h_cap =>
      exact StepComplete.complete_gaslimit s h_op h_gas h_cap h_run h_np
  | chainid h_op h_gas h_cap =>
      exact StepComplete.complete_chainid s h_op h_gas h_cap h_run h_np
  | selfbalance h_op h_gas h_cap =>
      exact StepComplete.complete_selfbalance s h_op h_gas h_cap h_run h_np
  | basefee h_op h_gas h_cap =>
      exact StepComplete.complete_basefee s h_op h_gas h_cap h_run h_np
  | blobhash i rest h h_op h_gas h_stack h_get h_cap =>
      exact StepComplete.complete_blobhash s i rest h h_op h_gas h_stack h_get h_cap h_run h_np
  | blobhash_oob i rest h_op h_gas h_stack h_oob h_cap =>
      exact StepComplete.complete_blobhash_oob s i rest h_op h_gas h_stack h_oob h_cap h_run h_np
  | blobbasefee h_op h_gas h_cap =>
      exact StepComplete.complete_blobbasefee s h_op h_gas h_cap h_run h_np
  | pop a rest h_op h_gas h_stack h_cap =>
      exact StepComplete.complete_pop s a rest h_op h_gas h_stack h_cap h_run h_np
  | push0 h_op h_gas h_cap =>
      exact StepComplete.complete_push0 s h_op h_gas h_cap h_run h_np
  | pushN k data immWidth h_k_pos h_op h_gas h_cap =>
      exact StepComplete.complete_pushN s k data immWidth h_k_pos h_op h_gas h_cap h_run h_np
  | dup n v h_op h_gas h_get h_cap =>
      exact StepComplete.complete_dup s n v h_op h_gas h_get h_cap h_run h_np
  | swap n stk' h_op h_gas h_swap h_cap =>
      exact StepComplete.complete_swap s n stk' h_op h_gas h_swap h_cap h_run h_np
  | mload offset rest h_op h_stack h_gas h_cap =>
      exact StepComplete.complete_mload s offset rest h_op h_stack h_gas h_cap h_run h_np
  | mstore offset value rest h_op h_stack h_gas h_cap =>
      exact StepComplete.complete_mstore s offset value rest h_op h_stack h_gas h_cap h_run h_np
  | mstore8 offset value rest h_op h_stack h_gas h_cap =>
      exact StepComplete.complete_mstore8 s offset value rest h_op h_stack h_gas h_cap h_run h_np
  | msize h_op h_gas h_cap =>
      exact StepComplete.complete_msize s h_op h_gas h_cap h_run h_np
  | mcopy destOff srcOff sz rest h_op h_stack h_gas h_cap =>
      exact StepComplete.complete_mcopy s destOff srcOff sz rest h_op h_stack h_gas h_cap h_run h_np
  | sload key rest h_op h_gas h_stack h_cap =>
      exact StepComplete.complete_sload s key rest h_op h_gas h_stack h_cap h_run h_np
  | sstore key value rest h_op h_perm h_stack h_sentry h_gas h_cap =>
      exact StepComplete.complete_sstore s key value rest h_op h_perm h_stack h_sentry h_gas h_cap
        h_run h_np
  | tload key rest h_op h_gas h_stack h_cap =>
      exact StepComplete.complete_tload s key rest h_op h_gas h_stack h_cap h_run h_np
  | tstore key value rest h_op h_perm h_gas h_stack h_cap =>
      exact StepComplete.complete_tstore s key value rest h_op h_perm h_gas h_stack h_cap h_run h_np
  | jump dest rest h_op h_gas h_stack h_valid h_cap =>
      exact StepComplete.complete_jump s dest rest h_op h_gas h_stack h_valid h_cap h_run h_np
  | jumpi_taken dest cond rest h_op h_gas h_stack h_cond h_valid h_cap =>
      exact StepComplete.complete_jumpi_taken s dest cond rest h_op h_gas h_stack h_cond h_valid
        h_cap h_run h_np
  | jumpi_notTaken dest cond rest h_op h_gas h_stack h_cond h_cap =>
      exact StepComplete.complete_jumpi_notTaken s dest cond rest h_op h_gas h_stack h_cond h_cap
        h_run h_np
  | pc h_op h_gas h_cap =>
      exact StepComplete.complete_pc s h_op h_gas h_cap h_run h_np
  | gas h_op h_gas h_cap =>
      exact StepComplete.complete_gas s h_op h_gas h_cap h_run h_np
  | jumpdest h_op h_gas h_cap =>
      exact StepComplete.complete_jumpdest s h_op h_gas h_cap h_run h_np
  | stop h_op h_cap =>
      exact StepComplete.complete_stop s h_op h_cap h_run h_np
  | return_ offset size rest h_op h_stack h_gas h_cap =>
      exact StepComplete.complete_return_ s offset size rest h_op h_stack h_gas h_cap h_run h_np
  | revert offset size rest h_op h_stack h_gas h_cap =>
      exact StepComplete.complete_revert s offset size rest h_op h_stack h_gas h_cap h_run h_np
  | callStatic gasArg toArg value argsOff argsLen retOff retLen rest h_op h_stack h_perm h_value
    h_gas h_cap =>
      exact StepComplete.complete_callStatic s gasArg toArg value argsOff argsLen retOff retLen
        rest h_op h_stack h_perm h_value h_gas h_cap h_run h_np
  | call gasArg toArg value argsOff argsLen retOff retLen rest forwarded h_op h_stack h_static
    h_gas h_take h_fwd h_afford h_cap =>
      exact StepComplete.complete_call s gasArg toArg value argsOff argsLen retOff retLen rest
        forwarded h_op h_stack h_static h_gas h_take h_fwd h_afford h_cap h_run h_np
  | callFail gasArg toArg value argsOff argsLen retOff retLen rest h_op h_stack h_static h_gas
    h_afford h_fail h_cap =>
      exact StepComplete.complete_callFail s gasArg toArg value argsOff argsLen retOff retLen rest
        h_op h_stack h_static h_gas h_afford h_fail h_cap h_run h_np
  | callcode gasArg toArg value argsOff argsLen retOff retLen rest forwarded h_op h_stack h_gas
    h_take h_fwd h_afford h_cap =>
      exact StepComplete.complete_callcode s gasArg toArg value argsOff argsLen retOff retLen rest
        forwarded h_op h_stack h_gas h_take h_fwd h_afford h_cap h_run h_np
  | callcodeFail gasArg toArg value argsOff argsLen retOff retLen rest h_op h_stack h_gas h_afford
    h_fail h_cap =>
      exact StepComplete.complete_callcodeFail s gasArg toArg value argsOff argsLen retOff retLen
        rest h_op h_stack h_gas h_afford h_fail h_cap h_run h_np
  | delegatecall gasArg toArg argsOff argsLen retOff retLen rest forwarded h_op h_stack h_gas
    h_take h_fwd h_afford h_cap =>
      exact StepComplete.complete_delegatecall s gasArg toArg argsOff argsLen retOff retLen rest
        forwarded h_op h_stack h_gas h_take h_fwd h_afford h_cap h_run h_np
  | delegatecallFail gasArg toArg argsOff argsLen retOff retLen rest h_op h_stack h_gas h_afford
    h_fail h_cap =>
      exact StepComplete.complete_delegatecallFail s gasArg toArg argsOff argsLen retOff retLen
        rest h_op h_stack h_gas h_afford h_fail h_cap h_run h_np
  | staticcall gasArg toArg argsOff argsLen retOff retLen rest forwarded h_op h_stack h_gas h_take
    h_fwd h_afford h_cap =>
      exact StepComplete.complete_staticcall s gasArg toArg argsOff argsLen retOff retLen rest
        forwarded h_op h_stack h_gas h_take h_fwd h_afford h_cap h_run h_np
  | staticcallFail gasArg toArg argsOff argsLen retOff retLen rest h_op h_stack h_gas h_afford
    h_fail h_cap =>
      exact StepComplete.complete_staticcallFail s gasArg toArg argsOff argsLen retOff retLen rest
        h_op h_stack h_gas h_afford h_fail h_cap h_run h_np
  | createStatic value offset size rest h_op h_stack h_perm h_gas h_cap =>
      exact StepComplete.complete_createStatic s value offset size rest h_op h_stack h_perm h_gas
        h_cap h_run h_np
  | createFail value offset size rest h_op h_stack h_perm h_gas h_fail h_size h_cap =>
      exact StepComplete.complete_createFail s value offset size rest h_op h_stack h_perm h_gas
        h_fail h_size h_cap h_run h_np
  | createCollision value offset size rest forwarded h_op h_stack h_perm h_gas h_take h_fwd h_coll
    h_size h_cap =>
      exact StepComplete.complete_createCollision s value offset size rest forwarded h_op h_stack
        h_perm h_gas h_take h_fwd h_coll h_size h_cap h_run h_np
  | create value offset size rest forwarded h_op h_stack h_perm h_gas h_take h_fwd h_nocoll h_size
    h_cap =>
      exact StepComplete.complete_create s value offset size rest forwarded h_op h_stack h_perm
        h_gas h_take h_fwd h_nocoll h_size h_cap h_run h_np
  | create2Static value offset size salt rest h_op h_stack h_perm h_gas h_cap =>
      exact StepComplete.complete_create2Static s value offset size salt rest h_op h_stack h_perm
        h_gas h_cap h_run h_np
  | create2Fail value offset size salt rest h_op h_stack h_perm h_gas h_fail h_size h_cap =>
      exact StepComplete.complete_create2Fail s value offset size salt rest h_op h_stack h_perm
        h_gas h_fail h_size h_cap h_run h_np
  | create2Collision value offset size salt rest forwarded h_op h_stack h_perm h_gas h_take h_fwd
    h_coll h_size h_cap =>
      exact StepComplete.complete_create2Collision s value offset size salt rest forwarded h_op
        h_stack h_perm h_gas h_take h_fwd h_coll h_size h_cap h_run h_np
  | create2 value offset size salt rest forwarded h_op h_stack h_perm h_gas h_take h_fwd h_nocoll
    h_size h_cap =>
      exact StepComplete.complete_create2 s value offset size salt rest forwarded h_op h_stack
        h_perm h_gas h_take h_fwd h_nocoll h_size h_cap h_run h_np
  | selfDestructStatic beneficiary rest h_op h_stack h_perm h_gas h_cap =>
      exact StepComplete.complete_selfDestructStatic s beneficiary rest h_op h_stack h_perm h_gas
        h_cap h_run h_np
  | selfDestruct beneficiary rest h_op h_stack h_perm h_gas h_cap =>
      exact StepComplete.complete_selfDestruct s beneficiary rest h_op h_stack h_perm h_gas h_cap
        h_run h_np
  | log n offset size topics rest h_op h_perm h_topics_n h_stack h_gas h_cap =>
      exact StepComplete.complete_log s n offset size topics rest h_op h_perm h_topics_n h_stack
        h_gas h_cap h_run h_np
  | dupN n v h_op h_gas h_get h_cap =>
      exact StepComplete.complete_dupN s n v h_op h_gas h_get h_cap h_run h_np
  | swapN n stk' h_op h_gas h_swap h_cap =>
      exact StepComplete.complete_swapN s n stk' h_op h_gas h_swap h_cap h_run h_np
  | exchange b stk' h_op h_gas h_swap h_cap =>
      exact StepComplete.complete_exchange s b stk' h_op h_gas h_swap h_cap h_run h_np
  | decodeFailure h_none =>
      exact StepComplete.complete_decodeFailure s h_none h_run h_np
  | invalidOpcode h_op h_cap =>
      exact StepComplete.complete_invalidOpcode s h_op h_cap h_run h_np
  | outOfGas op cost h_op h_cap h_reach h_cost_ub h_gas =>
      exact StepComplete.complete_outOfGas s op cost h_op h_cap h_reach h_cost_ub h_gas h_run h_np
  | initCodeSizeOog op value offset size rest h_op h_create h_cap h_gas h_stack h_len h_perm
      h_large =>
      exact StepComplete.complete_initCodeSizeOog s op value offset size rest h_op h_create
        h_cap h_gas h_stack h_len h_perm h_large h_run h_np
  | stackUnderflow op h_op h_cap h_gas h_reach h_under =>
      exact StepComplete.complete_stackUnderflow s op h_op h_cap h_gas h_reach h_under h_run h_np
  | stackOverflow op h_op h_pop_ok h_over =>
      exact StepComplete.complete_stackOverflow s op h_op h_pop_ok h_over h_run h_np
  | staticModeViolation op h_op h_mut h_cap h_gas h_reach h_perm =>
      exact StepComplete.complete_staticModeViolation s op h_op h_mut h_cap h_gas h_reach h_perm
        h_run h_np
  | jumpBadDest dest rest h_op h_cap h_gas h_stack h_bad =>
      exact StepComplete.complete_jumpBadDest s dest rest h_op h_cap h_gas h_stack h_bad h_run h_np
  | jumpiBadDest dest cond rest h_op h_cap h_gas h_stack h_cond h_bad =>
      exact StepComplete.complete_jumpiBadDest s dest cond rest h_op h_cap h_gas h_stack h_cond
        h_bad h_run h_np
  | returndatacopyOob destOff srcOff sz rest h_op h_cap h_gas h_stack h_oob =>
      exact StepComplete.complete_returndatacopyOob s destOff srcOff sz rest h_op h_cap h_gas
        h_stack h_oob h_run h_np

/-- Completeness of the resume layer: a `StepReturn` transition is
    exactly the `stepF` step on the halted frame. -/
theorem stepReturn_complete {s s' : State} (h : StepReturn s s') :
    stepF s = s' := by
  cases h with
  | callReturnSuccess f rest h_halt h_stack h_kind =>
    refine stepF_eq_ok ?_
    rw [stepFE_resume (by rcases h_halt with h | h <;> simp [h]) h_stack]
    rcases h_halt with h | h <;> simp [State.resumeByHalt, h, h_kind]
  | callReturnRevert f rest h_halt h_stack h_kind =>
    refine stepF_eq_ok ?_
    rw [stepFE_resume (by simp [h_halt]) h_stack]
    simp [State.resumeByHalt, h_halt, h_kind]
  | callReturnException f rest e h_halt h_stack h_kind =>
    refine stepF_eq_ok ?_
    rw [stepFE_resume (by simp [h_halt]) h_stack]
    simp [State.resumeByHalt, h_halt, h_kind]
  | createReturnSuccess f rest newAddr h_halt h_stack h_kind =>
    refine stepF_eq_ok ?_
    rw [stepFE_resume (by rcases h_halt with h | h <;> simp [h]) h_stack]
    rcases h_halt with h | h <;> simp [State.resumeByHalt, h, h_kind]
  | createReturnRevert f rest newAddr h_halt h_stack h_kind =>
    refine stepF_eq_ok ?_
    rw [stepFE_resume (by simp [h_halt]) h_stack]
    simp [State.resumeByHalt, h_halt, h_kind]
  | createReturnException f rest newAddr e h_halt h_stack h_kind =>
    refine stepF_eq_ok ?_
    rw [stepFE_resume (by simp [h_halt]) h_stack]
    simp [State.resumeByHalt, h_halt, h_kind]

/-- **Completeness**: every relational small-step transition is exactly
    the transition the executable `stepF` computes. Converse of
    `stepF_sound`. -/
theorem step_complete {s s' : State} (h : Step s s') : stepF s = s' := by
  cases h with
  | running h_run h_np hr => exact stepRunning_complete h_run h_np hr
  | precompileSuccess out gasUsed h_run h_isPrec h_prec =>
    refine stepF_eq_ok ?_
    unfold stepFE
    simp only [Id.run, h_run]
    split
    · rename_i hp
      have h_prec' : Precompile.run s.executionEnv.fork s.executionEnv.codeAddr
          s.executionEnv.calldata s.gasAvailable hp = .success out gasUsed := h_prec
      simp only [h_prec']
    · rename_i hp; rw [h_isPrec] at hp; cases hp
  | precompileOog h_run h_isPrec h_prec =>
    refine stepF_eq_ok ?_
    unfold stepFE
    simp only [Id.run, h_run]
    split
    · rename_i hp
      have h_prec' : Precompile.run s.executionEnv.fork s.executionEnv.codeAddr
          s.executionEnv.calldata s.gasAvailable hp = .outOfGas := h_prec
      simp only [h_prec']
    · rename_i hp; rw [h_isPrec] at hp; cases hp
  | returning hr => exact stepReturn_complete hr

/-- **Determinism** of the small-step relation: a state has at most one
    successor. Immediate from `step_complete` — both successors are
    `stepF s`. -/
theorem step_deterministic {s s₁ s₂ : State}
    (h₁ : Step s s₁) (h₂ : Step s s₂) : s₁ = s₂ :=
  (step_complete h₁).symm.trans (step_complete h₂)

/-- On non-done states, `Step` is exactly the graph of `stepF`:
    soundness (`stepF_sound`) gives the ⟸ direction, completeness
    (`step_complete`) the ⟹ one. -/
theorem step_iff_stepF {s s' : State} (h_nd : ¬ s.isDone) :
    Step s s' ↔ stepF s = s' :=
  ⟨step_complete, fun h => h ▸ stepF_sound s h_nd⟩

/-!
### Axiom-footprint guard

Same discipline as `Equiv.lean`: pin the axioms of the headline theorems
so a stray `sorry` (a build *warning*) or a new `axiom` (no warning at
all) turns into a hard build error.
-/

/-- info: 'EvmSemantics.EVM.step_complete' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms step_complete

/-- info: 'EvmSemantics.EVM.step_deterministic' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms step_deterministic

end EVM
end EvmSemantics
