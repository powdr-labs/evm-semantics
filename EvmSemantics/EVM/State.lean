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
    The memory-expansion gas for this range was already charged at CALL time. -/
def writeReturn (mem out : ByteArray) (retOffset retSize : Nat) : ByteArray :=
  MachineState.writeBytes mem (out.extract 0 (min out.size retSize)) retOffset

/-- Resume a suspended caller `f` (with the remaining `rest` of the call stack)
    after the active frame `child` has halted. Shared verbatim between `stepF`'s
    resume path and the `Step.callReturn*` rules so the soundness proof is
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

/-- Dispatch the resume of caller `f` on the active (child) frame's halt kind.
    The `.Running` arm is unreachable (resume is only invoked on a halted
    frame) and returns the child unchanged. -/
def resumeByHalt (child : State) (f : Frame) (rest : List Frame) : State :=
  match child.halt with
  | .Running     => child
  | .Success     => child.resumeSuccess f rest
  | .Returned    => child.resumeSuccess f rest
  | .Reverted    => child.resumeRevert f rest
  | .Exception _ => child.resumeException f rest

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
    `childGas` (forwarded + stipend). Shared verbatim by `stepF` and `Step.call`
    so the soundness proof is mechanical. -/
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
      accountMap   := sc.accountMap.transfer sc.executionEnv.codeOwner tgt value
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

end EVM
end EvmSemantics
