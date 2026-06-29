module

public import EvmSemantics

@[expose] public section

open EvmSemantics EvmSemantics.EVM

/-- A tiny initial state to demo on. -/
def initState (code : ByteArray) (gas : Nat) : State :=
  let env : ExecutionEnv :=
    { address := 0, origin := 0, caller := 0, weiValue := ⟨0⟩
      calldata := .empty, code := code
      gasPrice := ⟨0⟩, header := default, depth := 0, permitStateMutation := true
      blobVersionedHashes := #[]
      fork                := .Cancun }
  { toMachineState :=
      { gasAvailable := gas, activeWords := ⟨0⟩
        memory := .empty, returnData := .empty, hReturn := .empty }
    accountMap := AccountMap.empty
    substate := Substate.empty
    executionEnv := env
    pc := ⟨0⟩
    stack := []
    execLength := 0
    halt := .Running }

/-- Iterate `stepF` until the state halts or we hit a step bound.

    `stepF` reports an in-frame exception as `Except.error` rather than as a
    `halt := .Exception` state. When that happens *inside a sub-call* (the
    call stack is non-empty) it is **not** a top-level abort — the callee
    faulted, so we resume the caller with `0` (and roll its world back to the
    snapshot). This is the executable bridge to the relational
    `callReturnException` rule. Only a fault at the top frame (empty call
    stack) aborts the whole run. -/
partial def run (s : State) (fuel : Nat) : Except ExecutionException State :=
  if fuel = 0 then .error .OutOfFuel else
    -- Loop until the whole execution is *done* (halted with an empty call
    -- stack); a nested CALL leaves the active frame halted with callers still
    -- suspended, and `stepF` resumes them.
    if s.isDone then .ok s else
      match stepF s with
      | .ok s'   => run s' (fuel - 1)
      | .error e =>
        match s.callStack with
        | []        => .error e
        | f :: rest =>
          run (({ s with halt := .Exception e }).resumeException f rest) (fuel - 1)

/-- The demo program: `PUSH1 0x05 PUSH1 0x03 ADD STOP`. -/
def demoCode : ByteArray := ⟨#[0x60, 0x05, 0x60, 0x03, 0x01, 0x00]⟩

def main : IO Unit := do
  IO.println "EvmSemantics — demo: PUSH1 5 ; PUSH1 3 ; ADD ; STOP"
  IO.println s!"  bytecode: {repr demoCode.toList}"
  let s₀ := initState demoCode 100
  match run s₀ 32 with
  | .ok s' =>
    IO.println s!"  halt:  {repr s'.halt}"
    IO.println s!"  stack: {repr (s'.stack.map UInt256.toNat)}"
    IO.println s!"  gas:   {s'.gasAvailable}"
    IO.println s!"  pc:    {s'.pc.toNat}"
  | .error e =>
    IO.println s!"  ERROR: {repr e}"
