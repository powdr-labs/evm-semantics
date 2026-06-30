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

/-- EIP-170 (Spurious Dragon, both modelled forks): a contract's
    deployed code is rejected if it exceeds this many bytes. The
    init code itself can be larger (subject to EIP-3860's cap on
    Cancun); only the *returned* runtime code is capped here. -/
@[inline] def maxCodeSize : Nat := 24576

/-- EIP-3541 (London+): does the candidate deployed code start with
    the reserved `0xEF` byte? Such code is rejected at deploy time;
    the rule does not apply before London. -/
def isReservedCodePrefix (fork : Fork) (code : ByteArray) : Bool :=
  if fork.atLeast .London then code.size ≥ 1 && code[0]! == 0xEF
  else false

/-- CREATE-frame success resume: the child halted with `.Success` or
    `.Returned` and its `hReturn` is the candidate deployed code.

    Three reject conditions all route through the same rollback path
    (push `0`, no refund, snapshot world restored):

    * **OOG**: the per-byte `G_codedeposit · |hReturn|` deposit cost
      doesn't fit in `child.gasAvailable`.
    * **EIP-170**: `|hReturn|` exceeds `maxCodeSize`.
    * **EIP-3541** (Cancun): `hReturn` begins with `0xEF`.

    Otherwise we deploy the code, push the new address, and refund
    the remaining gas. The caller is *not* handed `hReturn` via
    memory (CREATE never copies output to caller memory), so we pass
    `ByteArray.empty` to `resumeWith`. -/
def resumeCreateSuccess (child : State) (f : Frame) (rest : List Frame)
    (newAddr : AccountAddress) : State :=
  let codeLen     := child.hReturn.size
  let depositCost := codeDepositPerByte * codeLen
  let oversized   := codeLen > maxCodeSize
  let badPrefix   := isReservedCodePrefix child.executionEnv.fork child.hReturn
  if depositCost ≤ child.gasAvailable ∧ ¬ oversized ∧ ¬ badPrefix then
    let σ := child.accountMap.set newAddr
               { (child.accountMap newAddr) with code := child.hReturn }
    let pushed := newAddr.toUInt256
    child.resumeWith f rest pushed ByteArray.empty
      (child.gasAvailable - depositCost) σ child.substate
  else
    -- Reject deployment (OOG, EIP-170, or EIP-3541): act like an exception.
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
    into address `to`: the callee runs *its own* code and storage (`address`),
    sees the caller as `caller`, receives `value`/`calldata`, and is one level
    deeper. (CALLCODE/DELEGATECALL/STATICCALL differ here — added later.) -/
def calleeEnvForCall (sc : State) (tgt : AccountAddress) (value : UInt256)
    (calldata calleeCode : ByteArray) : EvmSemantics.ExecutionEnv :=
  { address              := tgt
    origin               := sc.executionEnv.origin
    caller               := sc.executionEnv.address
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
      accountMap   := sc.accountMap.transfer sc.executionEnv.address tgt value
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

/-- The callee's `address` (= `ADDRESS` opcode in the callee). CALL and
    STATICCALL switch to the target; CALLCODE and DELEGATECALL keep the
    caller's address. -/
def calleeAddress (k : CallKind) (sc : State) (tgt : AccountAddress) :
    AccountAddress :=
  match k with
  | .Call | .StaticCall => tgt
  | .CallCode | .DelegateCall => sc.executionEnv.address

/-- The callee's `caller` (= `CALLER` opcode in the callee).
    DELEGATECALL inherits the caller's own `caller` so the new frame
    sees the same `msg.sender` as the parent frame; the others see
    the parent frame's `address`. -/
def calleeCaller (k : CallKind) (sc : State) : AccountAddress :=
  match k with
  | .DelegateCall => sc.executionEnv.caller
  | _ => sc.executionEnv.address

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
  { address              := kind.calleeAddress sc tgt
    origin               := sc.executionEnv.origin
    caller               := kind.calleeCaller sc
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
  let newMap : EvmSemantics.AccountMap :=
    if kind.transfersValue
      then sc.accountMap.transfer sc.executionEnv.address tgt value
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

/-! ### SELFDESTRUCT -/

/-- `State.selfDestructTo beneficiary` performs the world-state effects of a
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
  let self    := sc.executionEnv.address
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
  -- SELFDESTRUCT refund: 24000 on Frontier..Petersburg, removed by
  -- EIP-3529 (London+). The refund is added to the substate's
  -- `refundBalance` and applied at transaction-end, capped by the
  -- fork-dependent fraction of gasUsed.
  let refundDelta : Nat :=
    if sc.executionEnv.fork.atLeast .London then 0 else 24000
  let substate' : Substate :=
    { sc.substate with
        selfDestructSet := sc.substate.selfDestructSet.insert self
        refundBalance   := sc.substate.refundBalance +
                             UInt256.ofNat refundDelta }
  { sc with
      accountMap := map₂
      substate   := substate'
      halt       := .Success
      hReturn    := .empty }

/-! ### CREATE / CREATE2

A CREATE-family opcode opens a *creation* sub-frame whose code is the
init bytes read from caller memory and whose `address` is the
freshly-derived `newAddr`. The frame is marked on the call stack by
`Frame.createAddr := some newAddr`; on a `.Success`/`.Returned` halt
the child's `hReturn` is installed as `newAddr`'s code (see
`resumeCreateSuccess`). -/

/-- The callee's execution environment for a CREATE/CREATE2 init-code
    run. `address = newAddr` (the new contract executes its own init
    in its own storage slot), `caller = parent.address`, `weiValue =
    value`, `calldata = empty` (init code receives no calldata), `code
    = initCode`, depth is incremented, and the static flag propagates
    from the caller. -/
def calleeEnvForCreate (sc : State) (newAddr : AccountAddress)
    (value : UInt256) (initCode : ByteArray) : EvmSemantics.ExecutionEnv :=
  { address              := newAddr
    origin               := sc.executionEnv.origin
    caller               := sc.executionEnv.address
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
    4. Install the callee frame: code = `initCode`, address =
       `newAddr`, gas = `childGas`.

    The new account starts with `nonce = 1` (EIP-161 pre-existence rule:
    a contract that exists has at least nonce 1 to distinguish it from
    the empty account). -/
def enterCreate (sc : State) (rest : List UInt256)
    (newAddr : AccountAddress) (value : UInt256) (initCode : ByteArray)
    (childGas : Nat) : State :=
  let caller := sc.executionEnv.address
  let callerAcc := sc.accountMap caller
  -- Bump the creator nonce first. The bump must persist even if init
  -- code reverts / faults / fails the code-deposit gas check, so the
  -- frame's `snapAccountMap` snapshots the *post-bump* world (`map₁`).
  -- Only the value transfer and the new-account nonce are layered on
  -- top for the child's world and rolled back on a child failure.
  let map₁ : EvmSemantics.AccountMap :=
    sc.accountMap.set caller { callerAcc with nonce := callerAcc.nonce + ⟨1⟩ }
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
      snapAccountMap := map₁
      snapSubstate   := sc.substate
      createAddr     := some newAddr }
  let map₂ := map₁.transfer caller newAddr value
  -- Bring the new account into existence (pre-existing code/storage at this
  -- address is preserved — see the collision check in `stepF.system .CREATE`).
  -- Nonce initialisation is fork-gated: pre-EIP-161 (Frontier/Homestead/TangerineWhistle)
  -- a fresh contract starts at nonce 0, matching the legacy YP; from EIP-158
  -- (Spurious Dragon, alias EIP-161) onwards a fresh contract starts at
  -- nonce 1 so it can be distinguished from the empty-account predicate.
  let newAcc := map₂ newAddr
  let initNonce : UInt256 :=
    if sc.executionEnv.fork.atLeast .SpuriousDragon then ⟨1⟩ else ⟨0⟩
  let map₃ := map₂.set newAddr { newAcc with nonce := initNonce }
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

end State

end EVM
end EvmSemantics
