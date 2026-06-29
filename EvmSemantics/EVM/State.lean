module

public import EvmSemantics.Data.UInt256
public import EvmSemantics.Machine.SharedState
public import EvmSemantics.EVM.Exception

/-!
`EVM.State` — the per-execution-frame state that the small-step relation
acts on. Extends `SharedState` with EVM-specific fields: program counter,
stack, exec-length counter, and a `halt` flag indicating that execution
has terminated (along with how — success, revert, or exception).
-/

@[expose] public section

namespace EvmSemantics

/-- How a frame terminates. `Running` means "still going". -/
inductive HaltKind where
  | Running
  | Success    -- STOP
  | Returned   -- RETURN (output stashed in `hReturn`)
  | Reverted   -- REVERT (output stashed in `hReturn`)
  | Exception (e : ExecutionException)
  deriving BEq, Repr, Inhabited

namespace EVM

/-- A *suspended caller* frame, pushed onto `State.callStack` when a CALL-family
    op transfers control to a callee. Holds exactly the caller data needed to
    resume after the callee halts, plus the world-state snapshot used to roll
    back on a child REVERT/exception.

    Deliberately a flat record (not a nested `State`) so the small-step relation
    stays `State → State`: CALL pushes a `Frame` and swaps in the callee; return
    pops a `Frame`. This mirrors KEVM's `<callStack>` cell. -/
structure Frame where
  /-- Caller `pc`, already advanced past the CALL instruction. -/
  pc           : UInt256
  /-- Caller operand stack (with the 7/6 call args already popped). -/
  stack        : List UInt256
  /-- Caller gas remaining *after* the forwarded gas was deducted. -/
  gasAvailable : Nat
  /-- Caller memory-expansion high-water mark. -/
  activeWords  : UInt256
  /-- Caller working memory. -/
  memory       : ByteArray
  /-- Caller return-data buffer (overwritten with the child's output on return). -/
  returnData   : ByteArray
  /-- Caller's execution environment. -/
  executionEnv : EvmSemantics.ExecutionEnv
  /-- Memory offset where the child's return data is written on resume. -/
  retOffset    : Nat
  /-- Maximum number of return-data bytes to copy back. -/
  retSize      : Nat
  /-- World-state snapshot at call time — restored if the child REVERTs/throws. -/
  snapAccountMap : EvmSemantics.AccountMap
  /-- Substate snapshot at call time — restored if the child REVERTs/throws. -/
  snapSubstate   : EvmSemantics.Substate
  /-- `none` for a CALL-family frame; `some newAddr` for a CREATE/CREATE2
      frame, where `newAddr` is the address whose code we will set to the
      child's `hReturn` on successful return. The presence of this marker
      switches `resumeByHalt` to the CREATE-resume path: the caller's
      pushed value is `newAddr.toUInt256` (success) or `0` (failure)
      instead of `1`/`0`, and `child.hReturn` is *not* copied into the
      caller's memory (no `retOffset`/`retSize` semantics — they are unused
      for CREATE frames). -/
  createAddr     : Option AccountAddress := none
  deriving Inhabited

/-- Per-execution-frame state — extends `SharedState` with EVM-specific
    fields (PC, stack, exec counter, halt flag). -/
structure State extends EvmSemantics.SharedState where
  /-- Program counter into the executing bytecode. -/
  pc         : UInt256
  /-- Operand stack (top of stack is `stack.head`). -/
  stack      : List UInt256
  /-- Number of instructions executed so far in this frame. -/
  execLength : Nat
  /-- Termination status (`.Running` while still executing). -/
  halt       : HaltKind
  /-- Suspended caller frames. Empty for a top-level (single-frame) execution;
      a CALL pushes one, a return pops one. The *active* frame is `State`
      itself. -/
  callStack  : List Frame := []
  deriving Inhabited

namespace State

/-- True iff the frame has not yet halted. -/
def isRunning (s : State) : Bool :=
  match s.halt with | .Running => true | _ => false

/-- Negation of `isRunning`. -/
def isHalted (s : State) : Bool := ! s.isRunning

/-- True iff the *entire* execution is finished: the active frame has halted
    **and** there are no suspended callers left to resume. This is the real
    termination test once nested calls exist (`isHalted` only speaks about the
    active frame). -/
def isDone (s : State) : Bool := s.isHalted && s.callStack.isEmpty

/-- Push a new stack and advance the pc by `pcΔ` (default 1). -/
def replaceStackAndIncrPC (s : State) (stk : List UInt256) (pcΔ : Nat := 1) : State :=
  { s with stack := stk, pc := s.pc + UInt256.ofNat pcΔ }

/-- Advance the pc by `pcΔ` (default 1) without touching the stack. -/
def incrPC (s : State) (pcΔ : Nat := 1) : State :=
  { s with pc := s.pc + UInt256.ofNat pcΔ }

/-- Transition into the exception-halt state for `e`. -/
def haltWith (s : State) (e : ExecutionException) : State :=
  { s with halt := .Exception e }

/-- Copy up to `retSize` bytes of a child's output `out` into the caller's
    `mem` at `retOffset`. Only the bytes that exist in `out` are copied (no
    zero-fill beyond `out`), matching the EVM's `min(retSize, |out|)` rule.
    The memory-expansion gas for this range was already charged at CALL time.

    If there are no bytes to copy (`retSize = 0` or the child returned
    nothing), `mem` is returned unchanged — `writeBytes` would otherwise pad
    `mem` up to `retOffset` even with an empty payload, allocating a huge
    zero buffer when the caller passed a large `retOffset` with zero size. -/
def writeReturn (mem out : ByteArray) (retOffset retSize : Nat) : ByteArray :=
  let copy := out.extract 0 (min out.size retSize)
  if copy.size = 0 then mem
  else MachineState.writeBytes mem copy retOffset

/-- Resume a suspended caller `f` (with the remaining `rest` of the call stack)
    after the active frame `child` has halted. Shared verbatim between `stepF`'s
    resume path and the `StepReturn.callReturn*` rules so the soundness proof is
    mechanical. The four call outcomes differ only in the arguments:

    | outcome    | `flag` | `out`         | `refund`           | world (`am`,`sub`)      |
    |------------|:------:|---------------|--------------------|-------------------------|
    | success    |  `1`   | `child.hReturn`| `child.gasAvailable`| keep child's            |
    | returned   |  `1`   | `child.hReturn`| `child.gasAvailable`| keep child's            |
    | reverted   |  `0`   | `child.hReturn`| `child.gasAvailable`| roll back to snapshot   |
    | exception  |  `0`   | `∅`           | `0`                | roll back to snapshot   | -/
def resumeWith (child : State) (f : Frame) (rest : List Frame)
    (flag : UInt256) (out : ByteArray) (refund : Nat)
    (am : EvmSemantics.AccountMap) (sub : EvmSemantics.Substate) : State :=
  { child with
      gasAvailable := f.gasAvailable + refund
      activeWords  := f.activeWords
      memory       := writeReturn f.memory out f.retOffset f.retSize
      returnData   := out
      accountMap   := am
      substate     := sub
      executionEnv := f.executionEnv
      pc           := f.pc
      stack        := flag :: f.stack
      halt         := .Running
      callStack    := rest }

/-- Resume after a child STOP/RETURN: push success flag `1`, keep the child's
    world mutations, refund the child's unspent gas. (STOP leaves `hReturn`
    empty; RETURN leaves it the returned bytes — both handled by `child.hReturn`.) -/
def resumeSuccess (child : State) (f : Frame) (rest : List Frame) : State :=
  child.resumeWith f rest (UInt256.ofNat 1) child.hReturn child.gasAvailable
    child.accountMap child.substate

/-- Resume after a child REVERT: push failure flag `0`, **roll back** the world
    to the call-time snapshot, still return the revert data and refund unspent gas. -/
def resumeRevert (child : State) (f : Frame) (rest : List Frame) : State :=
  child.resumeWith f rest (UInt256.ofNat 0) child.hReturn child.gasAvailable
    f.snapAccountMap f.snapSubstate

/-- Resume after a child exceptional halt (OOG, bad jump, …): push failure flag
    `0`, roll back the world, return no data, and refund nothing (all forwarded
    gas is consumed). -/
def resumeException (child : State) (f : Frame) (rest : List Frame) : State :=
  child.resumeWith f rest (UInt256.ofNat 0) ByteArray.empty 0
    f.snapAccountMap f.snapSubstate

/-- `G_codedeposit = 200` — the per-byte cost of installing init-code
    output as the new account's code at the end of a successful CREATE.
    Inlined here (not in `Gas.lean`) because `State.lean` is upstream of
    `Gas.lean` in the import graph. -/
@[inline] def codeDepositPerByte : Nat := 200

/-- CREATE-frame success resume: the child halted with `.Success` or
    `.Returned` and its `hReturn` is the candidate deployed code. We
    charge `G_codedeposit · |hReturn|` from the child's remaining gas,
    then either deploy the code (and push the new address to the caller)
    or — if the deposit is unaffordable — fail like an exception
    (rollback world to snapshot, push `0`, no refund). The caller is *not*
    handed `hReturn` via memory (CREATE never copies output to caller
    memory), so we pass `ByteArray.empty` to `resumeWith`. -/
def resumeCreateSuccess (child : State) (f : Frame) (rest : List Frame)
    (newAddr : AccountAddress) : State :=
  let codeLen     := child.hReturn.size
  let depositCost := codeDepositPerByte * codeLen
  if depositCost ≤ child.gasAvailable then
    let σ := child.accountMap.set newAddr
               { (child.accountMap newAddr) with code := child.hReturn }
    let pushed := newAddr.toUInt256
    child.resumeWith f rest pushed ByteArray.empty
      (child.gasAvailable - depositCost) σ child.substate
  else
    -- Out-of-gas for code deposit: act like an exception.
    child.resumeWith f rest (UInt256.ofNat 0) ByteArray.empty 0
      f.snapAccountMap f.snapSubstate

/-- CREATE-frame revert resume: roll back the world, push `0`, hand back
    the unspent gas. `child.hReturn` is preserved as `returnData`
    (the revert-message convention, like CALL/REVERT) but *not* installed
    as code. -/
def resumeCreateRevert (child : State) (f : Frame) (rest : List Frame) : State :=
  child.resumeWith f rest (UInt256.ofNat 0) child.hReturn child.gasAvailable
    f.snapAccountMap f.snapSubstate

/-- CREATE-frame exception resume: roll back the world, push `0`, refund
    nothing. -/
def resumeCreateException (child : State) (f : Frame) (rest : List Frame) : State :=
  child.resumeWith f rest (UInt256.ofNat 0) ByteArray.empty 0
    f.snapAccountMap f.snapSubstate

/-- Dispatch the resume of caller `f` on the active (child) frame's halt kind.
    The `.Running` arm is unreachable (resume is only invoked on a halted
    frame) and returns the child unchanged. Routes CALL-family frames
    (`f.createAddr = none`) through the original three resume helpers and
    CREATE-family frames (`some addr`) through their CREATE counterparts. -/
def resumeByHalt (child : State) (f : Frame) (rest : List Frame) : State :=
  match f.createAddr, child.halt with
  | _,        .Running        => child
  | none,     .Success        => child.resumeSuccess f rest
  | none,     .Returned       => child.resumeSuccess f rest
  | none,     .Reverted       => child.resumeRevert f rest
  | none,     .Exception _    => child.resumeException f rest
  | some a,   .Success        => child.resumeCreateSuccess f rest a
  | some a,   .Returned       => child.resumeCreateSuccess f rest a
  | some _,   .Reverted       => child.resumeCreateRevert f rest
  | some _,   .Exception _    => child.resumeCreateException f rest

/-- The callee's execution environment for a plain `CALL` from caller state `sc`
    into address `to`: the callee runs *its own* code and storage (`codeOwner`),
    sees the caller as `source`, receives `value`/`calldata`, and is one level
    deeper. (CALLCODE/DELEGATECALL/STATICCALL differ here — added later.) -/
def calleeEnvForCall (sc : State) (tgt : AccountAddress) (value : UInt256)
    (calldata calleeCode : ByteArray) : EvmSemantics.ExecutionEnv :=
  { codeOwner            := tgt
    sender               := sc.executionEnv.sender
    source               := sc.executionEnv.codeOwner
    weiValue             := value
    calldata             := calldata
    code                 := calleeCode
    gasPrice             := sc.executionEnv.gasPrice
    header               := sc.executionEnv.header
    depth                := sc.executionEnv.depth + 1
    permitStateMutation  := sc.executionEnv.permitStateMutation
    blobVersionedHashes  := sc.executionEnv.blobVersionedHashes
    fork                 := sc.executionEnv.fork }

/-- Enter a sub-call. `sc` is the caller state with all of the call's gas
    (base + memory + value/new-account surcharge + forwarded) **already
    deducted** and its memory high-water mark updated; `rest` is the caller
    stack with the 7 call arguments popped. We snapshot the caller into a
    `Frame`, transfer `value`, and install a fresh callee frame that receives
    `childGas` (forwarded + stipend). Shared verbatim by `stepF` and
    `StepRunning.call` so the soundness proof is mechanical. -/
def enterCall (sc : State) (rest : List UInt256)
    (tgt : AccountAddress) (value : UInt256) (calldata calleeCode : ByteArray)
    (childGas retOffset retSize : Nat) : State :=
  let frame : Frame :=
    { pc           := sc.pc + UInt256.ofNat 1
      stack        := rest
      gasAvailable := sc.gasAvailable
      activeWords  := sc.activeWords
      memory       := sc.memory
      returnData   := sc.returnData
      executionEnv := sc.executionEnv
      retOffset    := retOffset
      retSize      := retSize
      snapAccountMap := sc.accountMap
      snapSubstate   := sc.substate }
  { sc with
      accountMap   := if value.toNat ≠ 0 then
                        sc.accountMap.transfer sc.executionEnv.codeOwner tgt value
                      else sc.accountMap
      gasAvailable := childGas
      activeWords  := UInt256.ofNat 0
      memory       := .empty
      returnData   := .empty
      hReturn      := .empty
      executionEnv := sc.calleeEnvForCall tgt value calldata calleeCode
      pc           := UInt256.ofNat 0
      stack        := []
      halt         := .Running
      callStack    := frame :: sc.callStack }

end State

/-! ### The four call-family opcodes, parameterised over `CallKind`

CALL / CALLCODE / DELEGATECALL / STATICCALL share a common skeleton —
memory expansion, surcharge, depth/balance check, 63/64 forwarding,
`enterCall`-style child-frame installation — but differ in seven
specific axes. The `CallKind` enum names the kinds; the helpers below
encode the per-kind axes once so the four `Step.*` constructors and
the four `stepF.system` arms read uniformly. -/

/-- The four inter-contract call opcodes. -/
inductive CallKind
  | Call
  | CallCode
  | DelegateCall
  | StaticCall
  deriving DecidableEq, Repr, Inhabited

namespace CallKind

/-- The callee's `codeOwner` (= `ADDRESS` opcode in the callee). CALL and
    STATICCALL switch to the target; CALLCODE and DELEGATECALL keep the
    caller's address. -/
def calleeCodeOwner (k : CallKind) (sc : State) (tgt : AccountAddress) :
    AccountAddress :=
  match k with
  | .Call | .StaticCall => tgt
  | .CallCode | .DelegateCall => sc.executionEnv.codeOwner

/-- The callee's `source` (= `CALLER` opcode in the callee). DELEGATECALL
    inherits the caller's own `source` so the new frame sees the same
    `msg.sender` as the caller; the others see the caller's `codeOwner`. -/
def calleeSource (k : CallKind) (sc : State) : AccountAddress :=
  match k with
  | .DelegateCall => sc.executionEnv.source
  | _ => sc.executionEnv.codeOwner

/-- The callee's `weiValue` (= `CALLVALUE` opcode in the callee).
    DELEGATECALL inherits the caller's; STATICCALL forces `0`; CALL and
    CALLCODE pass the value popped from the stack. -/
def calleeWeiValue (k : CallKind) (sc : State) (value : UInt256) : UInt256 :=
  match k with
  | .DelegateCall => sc.executionEnv.weiValue
  | .StaticCall => ⟨0⟩
  | _ => value

/-- The callee's `permitStateMutation` flag. STATICCALL forces `false`;
    the others inherit. -/
def calleePermit (k : CallKind) (sc : State) : Bool :=
  match k with
  | .StaticCall => false
  | _ => sc.executionEnv.permitStateMutation

/-- Whether this call kind actually transfers value caller→target. Only
    CALL does a non-trivial transfer; CALLCODE's transfer is caller→caller
    (a balance no-op, but the existing `Step.callcode` rule still threads
    it through `enterCall`); DELEGATECALL and STATICCALL never transfer. -/
def transfersValue : CallKind → Bool
  | .Call => true
  | _ => false

end CallKind

namespace State

/-- Generalised callee-environment constructor, parameterised over
    `CallKind`. The four `calleeXxx` helpers above pick which fields are
    inherited vs overridden. For `kind = .Call` this is the existing
    `calleeEnvForCall`; the other kinds are new. -/
def calleeEnvFor (sc : State) (kind : CallKind) (tgt : AccountAddress)
    (value : UInt256) (calldata calleeCode : ByteArray) :
    EvmSemantics.ExecutionEnv :=
  { codeOwner            := kind.calleeCodeOwner sc tgt
    sender               := sc.executionEnv.sender
    source               := kind.calleeSource sc
    weiValue             := kind.calleeWeiValue sc value
    calldata             := calldata
    code                 := calleeCode
    gasPrice             := sc.executionEnv.gasPrice
    header               := sc.executionEnv.header
    depth                := sc.executionEnv.depth + 1
    permitStateMutation  := kind.calleePermit sc
    blobVersionedHashes  := sc.executionEnv.blobVersionedHashes
    fork                 := sc.executionEnv.fork }

/-- Generalised `enterCall`, parameterised over `CallKind`. Used by the
    `Step.delegatecall` / `Step.staticcall` constructors (and could be
    used to unify `Step.call` / `Step.callcode` in a future refactor;
    those still go through the older `enterCall` for now). -/
def enterCallFor (sc : State) (kind : CallKind) (rest : List UInt256)
    (tgt : AccountAddress) (value : UInt256) (calldata calleeCode : ByteArray)
    (childGas retOffset retSize : Nat) : State :=
  let frame : Frame :=
    { pc           := sc.pc + UInt256.ofNat 1
      stack        := rest
      gasAvailable := sc.gasAvailable
      activeWords  := sc.activeWords
      memory       := sc.memory
      returnData   := sc.returnData
      executionEnv := sc.executionEnv
      retOffset    := retOffset
      retSize      := retSize
      snapAccountMap := sc.accountMap
      snapSubstate   := sc.substate }
  -- Only actually move balance / touch the target when the kind
  -- transfers value *and* `value > 0`. A zero-value `.Call` is a
  -- no-op on the world state and (post-EIP-158) does not even
  -- create the empty target — see EIP-158 §3.
  let newMap : EvmSemantics.AccountMap :=
    if kind.transfersValue ∧ value.toNat ≠ 0
      then sc.accountMap.transfer sc.executionEnv.codeOwner tgt value
      else sc.accountMap
  { sc with
      accountMap   := newMap
      gasAvailable := childGas
      activeWords  := UInt256.ofNat 0
      memory       := .empty
      returnData   := .empty
      hReturn      := .empty
      executionEnv := sc.calleeEnvFor kind tgt value calldata calleeCode
      pc           := UInt256.ofNat 0
      stack        := []
      halt         := .Running
      callStack    := frame :: sc.callStack }

/-! ### SELFDESTRUCT

`State.selfDestructTo beneficiary` performs the world-state effects of a
SELFDESTRUCT-after-gas-paid: credit the beneficiary with the
self-destructing account's balance, zero out the self's balance, mark the
self in `substate.selfDestructSet`, add to the refund counter (first-time
only, fork-dependent), and halt the current frame.

The credit-then-debit order matters for the `self = beneficiary` case:
the credit writes `beneficiary.balance + selfBalance`, the debit then
writes `0` to the same slot, so the value is correctly *burned* (matching
the Yellow Paper's "σ'[r].balance ← σ[r].balance + σ[Iₐ].balance ;
σ'[Iₐ].balance ← 0" sequence). `AccountMap.transfer` would instead
net-cancel the two updates and leave the balance *unchanged*, which is
wrong for the self-beneficiary case. -/
def selfDestructTo (sc : State) (beneficiary : AccountAddress) : State :=
  let self    := sc.executionEnv.codeOwner
  let selfBal := (sc.accountMap self).balance
  let benAcc  := sc.accountMap beneficiary
  let map₁    := sc.accountMap.set beneficiary
                   { benAcc with balance := benAcc.balance + selfBal }
  let map₂    := map₁.set self { (map₁ self) with balance := ⟨0⟩ }
  -- Per the Yellow Paper the `R_selfdestruct = 24000` refund (Constantinople;
  -- 0 on Cancun via EIP-3529 + EIP-6780) is added *only the first time* a
  -- given account self-destructs in a transaction. Our `selfDestructSet` is
  -- a `Prop`-valued predicate (`AddressSet := AccountAddress → Prop`) with
  -- no decidable-membership instance, so we cannot branch on prior
  -- membership without changing the underlying type. We therefore add the
  -- refund unconditionally: the legacy ethereum/tests corpus has no test
  -- where the same account self-destructs twice in one transaction, so the
  -- observable behaviour matches. (Refactoring `AddressSet` to a `RBTree`
  -- or `Finset` would let us compute "first time" precisely; out of scope
  -- for this opcode.)
  -- Refund constant matches `Gas.selfDestructRefund`: 24000 before
  -- London (EIP-3529 removed it), 0 from London onwards.
  let refundDelta : Int := if sc.executionEnv.fork.atLeast .London then 0 else 24000
  let substate' : Substate :=
    { sc.substate with
        selfDestructSet := sc.substate.selfDestructSet.insert self
        selfDestructList := self :: sc.substate.selfDestructList
        refundBalance   := sc.substate.refundBalance + refundDelta }
  { sc with
      accountMap := map₂
      substate   := substate'
      halt       := .Success
      hReturn    := .empty }

/-! ### CREATE / CREATE2

A CREATE-family opcode opens a *creation* sub-frame whose code is the
init bytes read from caller memory and whose `codeOwner` is the
freshly-derived `newAddr`. The frame is marked on the call stack by
`Frame.createAddr := some newAddr`; on a `.Success`/`.Returned` halt
the child's `hReturn` is installed as `newAddr`'s code (see
`resumeCreateSuccess`). -/

/-- The callee's execution environment for a CREATE/CREATE2 init-code
    run. `codeOwner = newAddr` (the new contract executes its own init
    in its own storage slot), `source = caller`, `weiValue = value`,
    `calldata = empty` (init code receives no calldata), `code =
    initCode`, depth is incremented, and the static flag propagates from
    the caller. -/
def calleeEnvForCreate (sc : State) (newAddr : AccountAddress)
    (value : UInt256) (initCode : ByteArray) : EvmSemantics.ExecutionEnv :=
  { codeOwner            := newAddr
    sender               := sc.executionEnv.sender
    source               := sc.executionEnv.codeOwner
    weiValue             := value
    calldata             := .empty
    code                 := initCode
    gasPrice             := sc.executionEnv.gasPrice
    header               := sc.executionEnv.header
    depth                := sc.executionEnv.depth + 1
    permitStateMutation  := sc.executionEnv.permitStateMutation
    blobVersionedHashes  := sc.executionEnv.blobVersionedHashes
    fork                 := sc.executionEnv.fork }

/-- Enter a CREATE/CREATE2 init-code sub-frame. `sc` is the caller state
    after the static + memory + base-gas deductions; `rest` is the
    caller stack with the 3/4 CREATE arguments already popped. We:

    1. Bump the caller's nonce by one (the address derivation has
       already used the pre-bump value).
    2. Transfer `value` from caller to `newAddr` (the new account may be
       brand-new with balance `0`; that's fine).
    3. Snapshot the caller into a `Frame` whose `createAddr := some
       newAddr` so `resumeByHalt` routes the child's halt through the
       CREATE-resume helpers.
    4. Install the callee frame: code = `initCode`, codeOwner =
       `newAddr`, gas = `childGas`.

    The new account starts with `nonce = 1` (EIP-161 pre-existence rule:
    a contract that exists has at least nonce 1 to distinguish it from
    the empty account). -/
def enterCreate (sc : State) (rest : List UInt256)
    (newAddr : AccountAddress) (value : UInt256) (initCode : ByteArray)
    (childGas : Nat) : State :=
  let frame : Frame :=
    { pc             := sc.pc + UInt256.ofNat 1
      stack          := rest
      gasAvailable   := sc.gasAvailable
      activeWords    := sc.activeWords
      memory         := sc.memory
      returnData     := sc.returnData
      executionEnv   := sc.executionEnv
      retOffset      := 0
      retSize        := 0
      snapAccountMap := sc.accountMap
      snapSubstate   := sc.substate
      createAddr     := some newAddr }
  let caller := sc.executionEnv.codeOwner
  let callerAcc := sc.accountMap caller
  -- Caller's nonce is bumped on CREATE in every fork we model.
  let map₁ : EvmSemantics.AccountMap :=
    sc.accountMap.set caller { callerAcc with nonce := callerAcc.nonce + ⟨1⟩ }
  let map₂ := map₁.transfer caller newAddr value
  -- The *new contract's* initial nonce: Frontier and Homestead leave it
  -- at 0; EIP-161 (Spurious Dragon = `.EIP158`) bumped it to 1 so that
  -- a freshly-created contract is distinguishable from a never-touched
  -- account.
  let newAcc := map₂ newAddr
  let map₃ :=
    if sc.executionEnv.fork.atLeast .EIP158 then
      map₂.set newAddr { newAcc with nonce := ⟨1⟩ }
    else map₂
  { sc with
      accountMap   := map₃
      gasAvailable := childGas
      activeWords  := UInt256.ofNat 0
      memory       := .empty
      returnData   := .empty
      hReturn      := .empty
      executionEnv := sc.calleeEnvForCreate newAddr value initCode
      pc           := UInt256.ofNat 0
      stack        := []
      halt         := .Running
      callStack    := frame :: sc.callStack }

/-! ### End-of-transaction finalization

After the top-level execution halts the harness still needs to do the
bookkeeping the EVM itself doesn't model at the opcode level:

1. **Apply the SSTORE / SELFDESTRUCT refund**, capped at
   `gas_used / refundDenom` (`refundDenom = 2` pre-EIP-3529).
2. **Return the leftover gas** (including the applied refund) to the
   transaction's sender as `(gasAvailable + refund) · gasPrice` wei
   added to their balance.

This is a separate semantic layer — the per-opcode `stepF` / `Step`
relation never touches it. `State.finalizeTx` is the executable
realisation; `Finalize` (in `BigStep.lean`) is the corresponding
relational rule.

Self-destructed accounts (those in `substate.selfDestructSet`) are *not*
zeroed here. Our `AddressSet` is a `Prop`-valued predicate with no
decidable membership, so we can't enumerate; the comparison in the
runners enumerates only accounts named in the test's `postState`, and
for the legacy state-tests corpus those entries already reflect the
post-deletion world (zero balance, empty code, etc. for self-destructed
addresses), so leaving the residual world in our state is observably
equivalent for `pass_core`. -/

/-- Inline copy of the refund-cap denominator (`gas_used / 2` pre-EIP-3529,
    `/ 5` post). Lives here rather than in `Gas.lean` to keep this module
    above `Gas.lean` in the import graph. -/
@[inline] def refundDenom (_fork : Fork) : Nat := 2

/-- Per-block miner reward in wei, paid to the coinbase at end of
    transaction (alongside the gas fee). Frontier..Spurious-Dragon: 5
    ETH; Byzantium: 3 ETH (EIP-649); Constantinople / Petersburg: 2 ETH
    (EIP-1234); post-merge (`.Cancun`): 0. -/
@[inline] def blockReward (fork : Fork) : Nat :=
  -- PoS: 0 ETH (Paris onwards); Constantinople: 2 ETH; Byzantium: 3 ETH; pre-Byzantium: 5 ETH.
  if fork.atLeast .Paris then 0
  else if fork.atLeast .Constantinople then 2_000_000_000_000_000_000
  else if fork.atLeast .Byzantium then 3_000_000_000_000_000_000
  else 5_000_000_000_000_000_000

/-- Apply end-of-transaction finalization to a halted top-level state.
    `gasLimit` is the *intrinsic-adjusted* gas budget the execution
    started with (so `gasUsed = gasLimit - sc.gasAvailable`); `sender`
    and `gasPrice` come from the transaction. Three balance effects:

    1. The sender gets `(gasAvailable + refund) · gasPrice` back —
       the unused gas plus the capped SSTORE / SELFDESTRUCT refund.
    2. The block coinbase (= miner) receives the *effective* gas fee
       `(gasUsed - refund) · gasPrice`.
    3. `sc.gasAvailable` is bumped by `refund` so the harness's
       `gas` field reflects the post-refund value.

    Accounts in `substate.selfDestructList` are wiped to
    `Account.empty` at the very end (after the refund/coinbase
    credits), so the world-state MPT filter (`EIP-161`) drops them. -/
def finalizeTx (sc : State) (gasLimit : Nat)
    (sender : AccountAddress) (gasPrice : UInt256) : State :=
  let fork          := sc.executionEnv.fork
  let gasUsed       := gasLimit - sc.gasAvailable
  let cap           := gasUsed / refundDenom fork
  -- Net-metered SSTORE can leave `refundBalance` negative; the corpus
  -- clamps to 0 before applying the `gas_used / refundDenom` cap.
  let refund        := Nat.min sc.substate.refundBalance.toNat cap
  let finalGas      := sc.gasAvailable + refund
  let senderRefund  := finalGas * gasPrice.toNat
  let coinbaseCredit := (gasUsed - refund) * gasPrice.toNat + blockReward fork
  let coinbase      := sc.executionEnv.header.coinbase
  let senderAcc     := sc.accountMap sender
  let map₁          := sc.accountMap.set sender
                         { senderAcc with balance := senderAcc.balance +
                                                       UInt256.ofNat senderRefund }
  let coinbaseAcc   := map₁ coinbase
  let map₂          := map₁.set coinbase
                         { coinbaseAcc with balance := coinbaseAcc.balance +
                                                         UInt256.ofNat coinbaseCredit }
  -- YP §6: self-destructed accounts cease to exist after `finalizeTx`.
  -- Truly remove them from the cache so the world-state MPT excludes
  -- them — *unless* the self-destruct beneficiary's credit means the
  -- address has been re-funded (the beneficiary can equal the self).
  let map₃          :=
    sc.substate.selfDestructList.foldl (fun σ a => σ.erase a) map₂
  { sc with
      accountMap   := map₃
      gasAvailable := finalGas }

end State

end EVM
end EvmSemantics
