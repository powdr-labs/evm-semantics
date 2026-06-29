module

public import EvmSemantics.EVM.Step
public import EvmSemantics.GasFreeEVM.Step
public import EvmSemantics.EVM.BigStep
public import EvmSemantics.GasFreeEVM.BigStep

/-!
`EvmSemantics.GasFreeEVM.Equiv` — the equivalence between the gas-aware
`EVM.Step` / `EVM.Eval` and the gas-free `GasFreeEVM.Step` /
`GasFreeEVM.Eval`.

This module is being built up incrementally:

* **Session 2 (this file)** — the *easy* direction `EVM.Step → GasFreeEVM.Step`
  modulo a `dropGas` projection on the state, plus the lift to `EVM.Eval`.
  This is the gas-erasure direction: every gas-aware transition has a
  gas-free counterpart, except for the `outOfGas` halt rule, which has
  no NG equivalent (the gas-free semantics simply doesn't model OOG).
* **Session 3+** — the *hard* direction
  `GasFreeEVM.Eval s r → ∃ g, EVM.Eval { s with gasAvailable := g } r`:
  from a gas-free termination proof, construct a sufficient gas budget.
  This is the user-facing direction for proving smart-contract
  correctness.

The `Frame.dropGas` / `State.dropGas` projections clear `gasAvailable`
on the active frame *and* on every suspended caller frame in `callStack`
— `dropGas` is the "ignore gas everywhere" projection. They live in the
`EvmSemantics.EVM.State` namespace alongside the other state helpers.
-/

@[expose] public section

namespace EvmSemantics
namespace EVM

----------------------------------------------------------------------------
-- `dropGas` projections: clear gasAvailable on the active frame and on
-- every suspended caller in `callStack`. The active frame's `activeWords`
-- *is* preserved (memory-expansion advancement happens in both Step and
-- the gas-free Step via `consumeMemExp` / `advanceMem`).
----------------------------------------------------------------------------

namespace Frame

/-- Drop the caller frame's `gasAvailable`. -/
def dropGas (f : Frame) : Frame := { f with gasAvailable := 0 }

end Frame

namespace State

/-- Clear `gasAvailable` on the active frame and on every suspended caller
    in `callStack`. Used to project a gas-aware state into the gas-free
    world: two states that agree modulo gas have the same `dropGas`. -/
def dropGas (s : State) : State :=
  { s with
      gasAvailable := 0
      callStack    := s.callStack.map Frame.dropGas }

/-- `dropGas` is the identity on `decodedOp` (it doesn't touch code or pc). -/
@[simp] theorem dropGas_decodedOp (s : State) : s.dropGas.decodedOp = s.decodedOp := rfl

/-- `dropGas` preserves the stack. -/
@[simp] theorem dropGas_stack (s : State) : s.dropGas.stack = s.stack := rfl

/-- `dropGas` preserves the halt kind. -/
@[simp] theorem dropGas_halt (s : State) : s.dropGas.halt = s.halt := rfl

/-- `dropGas` preserves the fork. -/
@[simp] theorem dropGas_fork (s : State) : s.dropGas.fork = s.fork := rfl

end State

----------------------------------------------------------------------------
-- Commutation lemmas: dropGas commutes with consumeGas / consumeMemExp /
-- replaceStackAndIncrPC / haltWith etc., possibly up to substitution of
-- the consume* helpers by their NG analogues (advanceMem, identity).
----------------------------------------------------------------------------

namespace State

/-- `consumeGas` is invisible under `dropGas`: both states reduce to the same
    `{ s with gasAvailable := 0 }`. -/
@[simp] theorem consumeGas_dropGas (s : State) (n : Nat) (h : n ≤ s.gasAvailable) :
    (s.consumeGas n h).dropGas = s.dropGas := by
  simp [State.dropGas, State.consumeGas]

/-- `consumeMemExp` projects to `advanceMem` under `dropGas`: both advance the
    activeWords mark to the same value; the gas component is erased. -/
@[simp] theorem consumeMemExp_dropGas (s : State) (offset sz : Nat)
    (h : s.canExpandMemory offset sz) :
    (s.consumeMemExp offset sz h).dropGas = s.dropGas.advanceMem offset sz := by
  simp [State.dropGas, State.consumeMemExp, State.advanceMem, State.consumeGas]

/-- Two-range version of `consumeMemExp_dropGas`. -/
@[simp] theorem consumeMemExp2_dropGas (s : State) (off1 sz1 off2 sz2 : Nat)
    (h : s.canExpandMemory2 off1 sz1 off2 sz2) :
    (s.consumeMemExp2 off1 sz1 off2 sz2 h).dropGas =
      s.dropGas.advanceMem2 off1 sz1 off2 sz2 := by
  simp [State.dropGas, State.consumeMemExp2, State.advanceMem2, State.consumeGas]

/-- `replaceStackAndIncrPC` commutes with `dropGas`. -/
@[simp] theorem replaceStackAndIncrPC_dropGas (s : State) (l : List UInt256) (pcΔ : Nat := 1) :
    (s.replaceStackAndIncrPC l (pcΔ := pcΔ)).dropGas =
      s.dropGas.replaceStackAndIncrPC l (pcΔ := pcΔ) := by
  simp [State.dropGas, State.replaceStackAndIncrPC]

/-- `incrPC` commutes with `dropGas`. -/
@[simp] theorem incrPC_dropGas (s : State) : s.incrPC.dropGas = s.dropGas.incrPC := by
  simp [State.dropGas, State.incrPC]

/-- `haltWith` commutes with `dropGas`. -/
@[simp] theorem haltWith_dropGas (s : State) (e : ExecutionException) :
    (s.haltWith e).dropGas = s.dropGas.haltWith e := by
  simp [State.dropGas, State.haltWith]

/-- `enterCall` commutes with `dropGas` modulo the forwarded-gas argument
    being dropped to `0`. -/
theorem enterCall_dropGas (s : State) (rest : List UInt256)
    (tgt : AccountAddress) (value : UInt256) (calldata calleeCode : ByteArray)
    (childGas retOffset retSize : Nat) :
    (s.enterCall rest tgt value calldata calleeCode childGas retOffset retSize).dropGas =
      s.dropGas.enterCall rest tgt value calldata calleeCode 0 retOffset retSize := by
  simp [State.dropGas, State.enterCall, Frame.dropGas, State.calleeEnvForCall]

/-- `resumeSuccess` commutes with `dropGas`. -/
@[simp] theorem resumeSuccess_dropGas
    (child : State) (f : Frame) (rest : List Frame) :
    (child.resumeSuccess f rest).dropGas =
      child.dropGas.resumeSuccess f.dropGas (rest.map Frame.dropGas) := by
  simp [State.dropGas, State.resumeSuccess, State.resumeWith, Frame.dropGas]

/-- `resumeRevert` commutes with `dropGas`. -/
@[simp] theorem resumeRevert_dropGas
    (child : State) (f : Frame) (rest : List Frame) :
    (child.resumeRevert f rest).dropGas =
      child.dropGas.resumeRevert f.dropGas (rest.map Frame.dropGas) := by
  simp [State.dropGas, State.resumeRevert, State.resumeWith, Frame.dropGas]

/-- `resumeException` commutes with `dropGas`. -/
@[simp] theorem resumeException_dropGas
    (child : State) (f : Frame) (rest : List Frame) :
    (child.resumeException f rest).dropGas =
      child.dropGas.resumeException f.dropGas (rest.map Frame.dropGas) := by
  simp [State.dropGas, State.resumeException, State.resumeWith, Frame.dropGas]

end State

----------------------------------------------------------------------------
-- The easy direction: EVM.Step → GasFreeEVM.Step (modulo dropGas, modulo OOG).
----------------------------------------------------------------------------

/-- Workhorse for `StepRunning.to_NG`: produces the gas-free witness
    directly (no disjunction), given that the gas-aware step wasn't an
    `outOfGas` halt. The OOG case is the only constructor whose output
    is `s.haltWith .OutOfGas`, so it gets dispatched by contradiction;
    every other constructor maps mechanically to its NG counterpart via
    `simpa using GasFreeEVM.StepRunning.X s.dropGas …`, with the
    `@[simp]` `dropGas`-commutation lemmas above doing all the work.

    **Status:** the 26 `StopArith` + `CompareBitwise` constructors are
    closed; the remaining ~70 are `sorry`. -/
theorem StepRunning.to_NG_inner {s s' : State} (h : StepRunning s s')
    (h_not_oog : s' ≠ s.haltWith .OutOfGas) :
    EvmSemantics.GasFreeEVM.StepRunning s.dropGas s'.dropGas := by
  -- Each non-OOG case is dispatched by `simpa using .NAME _ … ‹_› ‹_›`:
  -- the `_`s let Lean infer state/value/stack arguments from the goal's
  -- expected output (after the `@[simp]` `dropGas`-commutation lemmas
  -- rewrite it into NG-shape), and the `‹_›` slots find `h_op` and
  -- `h_stack` in the local context by type. Naming the constructor
  -- (`.add`, `.mul`, …) provides robustness — if `cases` were ever to
  -- emit a different constructor set, this proof would localize the
  -- error to the exact case rather than silently misfiring.
  cases h with
  | outOfGas => exact absurd rfl h_not_oog
  | stop h_op =>
    have h_eq : ({ s with halt := .Success, hReturn := .empty } : State).dropGas
              = { s.dropGas with halt := .Success, hReturn := .empty } := by
      simp [State.dropGas]
    rw [h_eq]
    exact EvmSemantics.GasFreeEVM.StepRunning.stop _ (by simpa using h_op)
  -- StopArith (excluding STOP, handled above).
  | add a b rest h_op _ h_stack => simpa using .add _ _ _ _ ‹_› ‹_›
  | mul a b rest h_op _ h_stack => simpa using .mul _ _ _ _ ‹_› ‹_›
  | sub a b rest h_op _ h_stack => simpa using .sub _ _ _ _ ‹_› ‹_›
  | div a b rest h_op _ h_stack => simpa using .div _ _ _ _ ‹_› ‹_›
  | sdiv a b rest h_op _ h_stack => simpa using .sdiv _ _ _ _ ‹_› ‹_›
  | mod a b rest h_op _ h_stack => simpa using .mod _ _ _ _ ‹_› ‹_›
  | smod a b rest h_op _ h_stack => simpa using .smod _ _ _ _ ‹_› ‹_›
  | addmod a b n rest h_op _ h_stack => simpa using .addmod _ _ _ _ _ ‹_› ‹_›
  | mulmod a b n rest h_op _ h_stack => simpa using .mulmod _ _ _ _ _ ‹_› ‹_›
  | exp a b rest h_op _ h_stack _ => simpa using .exp _ _ _ _ ‹_› ‹_›
  | signextend b x rest h_op _ h_stack => simpa using .signextend _ _ _ _ ‹_› ‹_›
  -- CompareBitwise.
  | lt a b rest h_op _ h_stack => simpa using .lt _ _ _ _ ‹_› ‹_›
  | gt a b rest h_op _ h_stack => simpa using .gt _ _ _ _ ‹_› ‹_›
  | slt a b rest h_op _ h_stack => simpa using .slt _ _ _ _ ‹_› ‹_›
  | sgt a b rest h_op _ h_stack => simpa using .sgt _ _ _ _ ‹_› ‹_›
  | eq a b rest h_op _ h_stack => simpa using .eq _ _ _ _ ‹_› ‹_›
  | iszero a rest h_op _ h_stack => simpa using .iszero _ _ _ ‹_› ‹_›
  | and a b rest h_op _ h_stack => simpa using .and _ _ _ _ ‹_› ‹_›
  | or a b rest h_op _ h_stack => simpa using .or _ _ _ _ ‹_› ‹_›
  | xor_ a b rest h_op _ h_stack => simpa using .xor_ _ _ _ _ ‹_› ‹_›
  | not a rest h_op _ h_stack => simpa using .not _ _ _ ‹_› ‹_›
  | byte_ i x rest h_op _ h_stack => simpa using .byte_ _ _ _ _ ‹_› ‹_›
  | shl shift v rest h_op _ h_stack => simpa using .shl _ _ _ _ ‹_› ‹_›
  | shr shift v rest h_op _ h_stack => simpa using .shr _ _ _ _ ‹_› ‹_›
  | sar shift v rest h_op _ h_stack => simpa using .sar _ _ _ _ ‹_› ‹_›
  -- Env reads (stackless).
  | address h_op _ => simpa using .address _ ‹_›
  | origin h_op _ => simpa using .origin _ ‹_›
  | caller h_op _ => simpa using .caller _ ‹_›
  | callvalue h_op _ => simpa using .callvalue _ ‹_›
  | calldatasize h_op _ => simpa using .calldatasize _ ‹_›
  | codesize h_op _ => simpa using .codesize _ ‹_›
  | gasprice h_op _ => simpa using .gasprice _ ‹_›
  | returndatasize h_op _ => simpa using .returndatasize _ ‹_›
  -- Env reads (1 stack arg).
  | balance addr rest h_op _ h_stack => simpa using .balance _ _ _ ‹_› ‹_›
  | calldataload i rest h_op _ h_stack => simpa using .calldataload _ _ _ ‹_› ‹_›
  | extcodesize addr rest h_op _ h_stack => simpa using .extcodesize _ _ _ ‹_› ‹_›
  | extcodehash addr rest h_op _ h_stack => simpa using .extcodehash _ _ _ ‹_› ‹_›
  -- Block reads (stackless).
  | coinbase h_op _ => simpa using .coinbase _ ‹_›
  | timestamp h_op _ => simpa using .timestamp _ ‹_›
  | number h_op _ => simpa using .number _ ‹_›
  | prevrandao h_op _ => simpa using .prevrandao _ ‹_›
  | gaslimit h_op _ => simpa using .gaslimit _ ‹_›
  | chainid h_op _ => simpa using .chainid _ ‹_›
  | selfbalance h_op _ => simpa using .selfbalance _ ‹_›
  | basefee h_op _ => simpa using .basefee _ ‹_›
  | blobbasefee h_op _ => simpa using .blobbasefee _ ‹_›
  -- Block reads (1 stack arg).
  | blockhash n rest h_op _ h_stack => simpa using .blockhash _ _ _ ‹_› ‹_›
  | blobhash i rest hash h_op _ h_stack h_get =>
    simpa using .blobhash _ _ _ _ ‹_› ‹_› ‹_›
  | blobhash_oob i rest h_op _ h_stack h_oob =>
    simpa using .blobhash_oob _ _ _ ‹_› ‹_› ‹_›
  -- Stack / memory-flow simple reads (stackless or 1-arg).
  | pop a rest h_op _ h_stack => simpa using .pop _ _ _ ‹_› ‹_›
  | push0 h_op _ => simpa using .push0 _ ‹_›
  | pc h_op _ => simpa using .pc _ ‹_›
  -- `gas` is intentionally deferred: the gas-aware `GAS` opcode pushes
  -- `UInt256.ofNat (s.gasAvailable - baseCost)`, whereas the gas-free
  -- version pushes `UInt256.ofNat s.gasAvailable`. These values differ
  -- by `baseCost s.fork .GAS`, which the `dropGas` projection cannot
  -- close: it erases the gas field to `0` but doesn't undo the
  -- subtraction inside the pushed `UInt256`. The right fix here is
  -- arguably to drop `gas` from `StepRunningNG` (like we did for
  -- `outOfGas`) — it doesn't make sense to read the remaining gas in a
  -- gas-free semantics. Deferring to a future session.
  | msize h_op => simpa using .msize _ ‹_›
  | jumpdest h_op _ => simpa using .jumpdest _ ‹_›
  -- Storage reads (transient and persistent), 1 stack arg.
  | sload key rest h_op _ h_stack => simpa using .sload _ _ _ ‹_› ‹_›
  | tload key rest h_op _ h_stack => simpa using .tload _ _ _ ‹_› ‹_›
  -- Exception rules with no special structure.
  | decodeFailure h_none => simpa using .decodeFailure _ ‹_›
  | invalidOpcode h_op => simpa using .invalidOpcode _ ‹_›
  | stackUnderflow op h_op h_under => simpa using .stackUnderflow _ _ ‹_› ‹_›
  | stackOverflow op h_op h_pop_ok h_over =>
    simpa using .stackOverflow _ _ ‹_› ‹_› ‹_›
  | staticModeViolation op h_op h_mut h_perm =>
    simpa using .staticModeViolation _ _ ‹_› ‹_› ‹_›
  | returndatacopyOob destOff srcOff sz rest h_op _ h_stack h_oob =>
    simpa using .returndatacopyOob _ _ _ _ _ ‹_› ‹_› ‹_›
  -- Memory-touching ops where the output is `(s.advanceMem …).replaceStackAndIncrPC …`
  -- — the `consumeMemExp_dropGas` simp lemma bridges to NG-shape.
  | keccak256 offset size rest h_op _ h_stack _ _ =>
    simpa using .keccak256 _ _ _ _ ‹_› ‹_›
  | calldatacopy destOff srcOff sz rest h_op _ h_stack _ _ =>
    simpa using .calldatacopy _ _ _ _ _ ‹_› ‹_›
  | codecopy destOff srcOff sz rest h_op _ h_stack _ _ =>
    simpa using .codecopy _ _ _ _ _ ‹_› ‹_›
  | extcodecopy addr destOff srcOff sz rest h_op _ h_stack _ _ =>
    simpa using .extcodecopy _ _ _ _ _ _ ‹_› ‹_›
  | returndatacopy destOff srcOff sz rest h_op _ h_stack h_inbounds _ _ =>
    simpa using .returndatacopy _ _ _ _ _ ‹_› ‹_› ‹_›
  -- MLOAD is deferred: it binds `μ' : MachineState` as a parameter
  -- (so the gas-aware and gas-free versions reference different `μ'`
  -- values via `consumeMemExp` vs `advanceMem` in the `h_load`
  -- hypothesis), and the `‹_›` placeholder can't unify them.
  | mstore offset value rest h_op _ h_stack _ =>
    simpa using .mstore _ _ _ _ ‹_› ‹_›
  | mstore8 offset value rest h_op _ h_stack _ =>
    simpa using .mstore8 _ _ _ _ ‹_› ‹_›
  | mcopy destOff srcOff sz rest h_op _ h_stack _ _ =>
    simpa using .mcopy _ _ _ _ _ ‹_› ‹_›
  | return_ offset size rest h_op _ h_stack _ =>
    simpa using .return_ _ _ _ _ ‹_› ‹_›
  | revert offset size rest h_op _ h_stack _ =>
    simpa using .revert _ _ _ _ ‹_› ‹_›
  -- Storage writes need `h_perm` (static-mode guard) too.
  | sstore key value rest h_op h_perm _ h_stack _ _ =>
    simpa using .sstore _ _ _ _ ‹_› ‹_› ‹_›
  | tstore key value rest h_op h_perm _ h_stack =>
    simpa using .tstore _ _ _ _ ‹_› ‹_› ‹_›
  -- Control flow.
  | jump dest rest h_op _ h_stack h_valid =>
    simpa using .jump _ _ _ ‹_› ‹_› ‹_›
  | jumpi_taken dest cond rest h_op _ h_stack h_cond h_valid =>
    simpa using .jumpi_taken _ _ _ _ ‹_› ‹_› ‹_› ‹_›
  | jumpi_notTaken dest cond rest h_op _ h_stack h_cond =>
    simpa using .jumpi_notTaken _ _ _ _ ‹_› ‹_› ‹_›
  | jumpBadDest dest rest h_op _ h_stack h_bad =>
    simpa using .jumpBadDest _ _ _ ‹_› ‹_› ‹_›
  | jumpiBadDest dest cond rest h_op _ h_stack h_cond h_bad =>
    simpa using .jumpiBadDest _ _ _ _ ‹_› ‹_› ‹_› ‹_›
  -- Parametric stack ops.
  | pushN k data immWidth h_k_pos h_op _ =>
    simpa using .pushN _ _ _ _ ‹_› ‹_›
  | dup n v h_op _ h_get =>
    simpa using .dup _ _ _ ‹_› ‹_›
  | swap n stk' h_op _ h_swap =>
    simpa using .swap _ _ _ ‹_› ‹_›
  | dupN n v h_op _ h_get =>
    simpa using .dupN _ _ _ ‹_› ‹_›
  | swapN n stk' h_op _ h_swap =>
    simpa using .swapN _ _ _ ‹_› ‹_›
  | exchange b stk' h_op _ h_swap =>
    simpa using .exchange _ _ _ ‹_› ‹_›
  -- CALL family.
  | callStatic gasArg toArg value argsOff argsLen retOff retLen rest
      h_op h_stack h_perm h_value =>
    simpa using .callStatic _ _ _ _ _ _ _ _ _ ‹_› ‹_› ‹_› ‹_›
  -- LOG defers — `simp`'s normalisation of the substate / log entry mix
  -- hits the max-recursion limit. Likely a `simp only [...]` with a
  -- narrower set, or a hand `have h_eq` rewrite, would work.
  -- `call` / `callFail` defer — the gas-aware versions take `s' s2 s3 s4`
  -- intermediates and prove `h_take`/`h_fail`/`h_fwd` *about those
  -- intermediates*, whereas the gas-free versions take a single `s` and
  -- prove the conditions about `s` directly. Bridging requires
  -- substituting the gas-only intermediate states, which simp would
  -- need to chain across many consumeGas calls.
  | _ => sorry

/-- Gas-erasure for the per-opcode small-step rules. Either the gas-aware
    `Step` was an `outOfGas` halt (no NG counterpart) or the corresponding
    `GasFreeEVM.StepRunning` derivation holds on the gas-dropped states.
    The disjunction wrapping happens once here; the case-split (~95
    constructors) is in `to_NG_inner`. -/
theorem StepRunning.to_NG {s s' : State} (h : StepRunning s s') :
    s' = s.haltWith .OutOfGas ∨
      EvmSemantics.GasFreeEVM.StepRunning s.dropGas s'.dropGas := by
  by_cases h_oog : s' = s.haltWith .OutOfGas
  · exact .inl h_oog
  · exact .inr (h.to_NG_inner h_oog)

/-- Gas-erasure for the call-return resume rules. -/
theorem StepReturn.to_NG {s s' : State} (h : StepReturn s s') :
    EvmSemantics.GasFreeEVM.StepReturn s.dropGas s'.dropGas := by
  cases h with
  | callReturnSuccess f rest h_halt h_stack =>
    rw [State.resumeSuccess_dropGas]
    exact EvmSemantics.GasFreeEVM.StepReturn.callReturnSuccess
      s.dropGas f.dropGas (rest.map Frame.dropGas)
      (by simpa using h_halt) (by simp [State.dropGas, h_stack])
  | callReturnRevert f rest h_halt h_stack =>
    rw [State.resumeRevert_dropGas]
    exact EvmSemantics.GasFreeEVM.StepReturn.callReturnRevert
      s.dropGas f.dropGas (rest.map Frame.dropGas)
      (by simpa using h_halt) (by simp [State.dropGas, h_stack])
  | callReturnException f rest e h_halt h_stack =>
    rw [State.resumeException_dropGas]
    exact EvmSemantics.GasFreeEVM.StepReturn.callReturnException
      s.dropGas f.dropGas (rest.map Frame.dropGas) e
      (by simpa using h_halt) (by simp [State.dropGas, h_stack])

/-- Gas-erasure for the wrapper. -/
theorem Step.to_NG {s s' : State} (h : Step s s') :
    s' = s.haltWith .OutOfGas ∨
      EvmSemantics.GasFreeEVM.Step s.dropGas s'.dropGas := by
  cases h with
  | running hr inner =>
    rcases StepRunning.to_NG inner with hoog | hng
    · left; exact hoog
    · right
      apply EvmSemantics.GasFreeEVM.Step.running ?_ hng
      simpa using hr
  | returning inner =>
    right
    exact .returning (StepReturn.to_NG inner)

end EVM
end EvmSemantics
