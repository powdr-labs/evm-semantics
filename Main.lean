module

public import EvmSemantics

@[expose] public section

open EvmSemantics EvmSemantics.EVM

/-- A tiny initial state to demo on. -/
def initState (code : ByteArray) (gas : Nat) : State :=
  let env : ExecutionEnv :=
    { codeOwner := 0, sender := 0, source := 0, weiValue := ⟨0⟩
      calldata := .empty, code := code
      gasPrice := ⟨0⟩, header := default, depth := 0, permitStateMutation := true
      blobVersionedHashes := #[] }
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

/-- Iterate `stepF` until the state halts or we hit a step bound. -/
partial def run (s : State) (fuel : Nat) : Except ExecutionException State :=
  if fuel = 0 then .error .OutOfFuel else
    match s.halt with
    | .Running =>
      match stepF s with
      | .ok s'  => run s' (fuel - 1)
      | .error e => .error e
    | _ => .ok s

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
