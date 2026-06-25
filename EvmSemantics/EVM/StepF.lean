module

public import EvmSemantics.EVM.Step

/-!
`stepF` — the executable shadow of the `Step` relation.

`stepF : State → Except ExecutionException State` runs one EVM
instruction and either returns the successor state or an exception.
It mirrors the constructors of `Step` op-by-op. The intent is twofold:

1. **Demo / smoke testing.** Lets us run small bytecodes end-to-end and
   inspect outputs.
2. **Soundness target.** The lemma `stepF_sound : stepF s = .ok s' →
   Step s s'` (in `Equiv.lean`) is proven against this function.

The implementation is **split into per-`Operation`-constructor helpers**
(`stepF.stopArith`, `stepF.compBit`, …) so each piece is small,
self-contained, and individually reasonable. The top-level `stepF`
performs the halt-check / decode / gas-check and dispatches to the
appropriate helper.

Each helper takes both the original state `s` (for reads from `s.stack`,
`s.memory`, etc.) and the gas-consumed state `s'` (used to construct the
successor). Out-of-scope opcodes (CALL family, CREATE family,
SELFDESTRUCT) are mapped to `InvalidInstruction` in v1.

The LOG branch uses an auxiliary `popN` helper (defined in section 9
below) to pop the variable number of topics. `popN_correct` proves it
preserves the list invariant `topics.length = k ∧ stk = topics ++ rest`,
which `log_sound` uses to recover the witness list expected by `Step.log`.
-/

@[expose] public section

namespace EvmSemantics
namespace EVM

/-- Sugar for the stack-underflow exception result. -/
def underflow : Except ExecutionException State := .error .StackUnderflow
/-- Sugar for the static-mode-violation exception result. -/
def static    : Except ExecutionException State := .error .StaticModeViolation

namespace stepF

----------------------------------------------------------------------------
-- 1. Stop + Arithmetic (StopArithOps, 12 ops).
----------------------------------------------------------------------------

/-- Execute one StopArithOps opcode (STOP + 11 arithmetic ops). -/
def stopArith (s s' : State) : Operation.StopArithOps → Except ExecutionException State
  | .STOP => .ok { s with halt := .Success, hReturn := .empty }
  | .ADD => match s.stack with
    | a :: b :: rest => .ok (s'.replaceStackAndIncrPC ((a + b) :: rest))
    | _ => underflow
  | .MUL => match s.stack with
    | a :: b :: rest => .ok (s'.replaceStackAndIncrPC ((a * b) :: rest))
    | _ => underflow
  | .SUB => match s.stack with
    | a :: b :: rest => .ok (s'.replaceStackAndIncrPC ((a - b) :: rest))
    | _ => underflow
  | .DIV => match s.stack with
    | a :: b :: rest => .ok (s'.replaceStackAndIncrPC ((a / b) :: rest))
    | _ => underflow
  | .SDIV => match s.stack with
    | a :: b :: rest =>
      .ok (s'.replaceStackAndIncrPC (UInt256.sdiv a b :: rest))
    | _ => underflow
  | .MOD => match s.stack with
    | a :: b :: rest => .ok (s'.replaceStackAndIncrPC ((a % b) :: rest))
    | _ => underflow
  | .SMOD => match s.stack with
    | a :: b :: rest =>
      .ok (s'.replaceStackAndIncrPC (UInt256.smod a b :: rest))
    | _ => underflow
  | .ADDMOD => match s.stack with
    | a :: b :: n :: rest => .ok (s'.replaceStackAndIncrPC (UInt256.addMod a b n :: rest))
    | _ => underflow
  | .MULMOD => match s.stack with
    | a :: b :: n :: rest => .ok (s'.replaceStackAndIncrPC (UInt256.mulMod a b n :: rest))
    | _ => underflow
  | .EXP => match s.stack with
    | a :: b :: rest => .ok (s'.replaceStackAndIncrPC (UInt256.exp a b :: rest))
    | _ => underflow
  | .SIGNEXTEND => match s.stack with
    | b :: x :: rest => .ok (s'.replaceStackAndIncrPC (UInt256.signExtend b x :: rest))
    | _ => underflow

----------------------------------------------------------------------------
-- 2. Comparison & bitwise (CompareBitwiseOps, 14 ops).
----------------------------------------------------------------------------

/-- Execute one CompareBitwiseOps opcode (LT/GT/EQ + bitwise + shifts). -/
def compBit (s s' : State) : Operation.CompareBitwiseOps → Except ExecutionException State
  | .LT => match s.stack with
    | a :: b :: rest => .ok (s'.replaceStackAndIncrPC (UInt256.lt a b :: rest))
    | _ => underflow
  | .GT => match s.stack with
    | a :: b :: rest => .ok (s'.replaceStackAndIncrPC (UInt256.gt a b :: rest))
    | _ => underflow
  | .SLT => match s.stack with
    | a :: b :: rest => .ok (s'.replaceStackAndIncrPC (UInt256.slt a b :: rest))
    | _ => underflow
  | .SGT => match s.stack with
    | a :: b :: rest => .ok (s'.replaceStackAndIncrPC (UInt256.sgt a b :: rest))
    | _ => underflow
  | .EQ => match s.stack with
    | a :: b :: rest => .ok (s'.replaceStackAndIncrPC (UInt256.eq a b :: rest))
    | _ => underflow
  | .ISZERO => match s.stack with
    | a :: rest => .ok (s'.replaceStackAndIncrPC (UInt256.isZero a :: rest))
    | _ => underflow
  | .AND => match s.stack with
    | a :: b :: rest => .ok (s'.replaceStackAndIncrPC (UInt256.land a b :: rest))
    | _ => underflow
  | .OR => match s.stack with
    | a :: b :: rest => .ok (s'.replaceStackAndIncrPC (UInt256.lor a b :: rest))
    | _ => underflow
  | .XOR => match s.stack with
    | a :: b :: rest => .ok (s'.replaceStackAndIncrPC (UInt256.xor a b :: rest))
    | _ => underflow
  | .NOT => match s.stack with
    | a :: rest => .ok (s'.replaceStackAndIncrPC (UInt256.lnot a :: rest))
    | _ => underflow
  | .BYTE => match s.stack with
    | i :: x :: rest => .ok (s'.replaceStackAndIncrPC (UInt256.byteAt i x :: rest))
    | _ => underflow
  | .SHL => match s.stack with
    | sh :: v :: rest => .ok (s'.replaceStackAndIncrPC (UInt256.shiftLeft v sh :: rest))
    | _ => underflow
  | .SHR => match s.stack with
    | sh :: v :: rest => .ok (s'.replaceStackAndIncrPC (UInt256.shiftRight v sh :: rest))
    | _ => underflow
  | .SAR => match s.stack with
    | sh :: v :: rest => .ok (s'.replaceStackAndIncrPC (UInt256.sar v sh :: rest))
    | _ => underflow

----------------------------------------------------------------------------
-- 3. Keccak (1 op).
----------------------------------------------------------------------------

/-- Execute the single KeccakOps opcode (KECCAK256). -/
def keccak (s s' : State) : Operation.KeccakOps → Except ExecutionException State
  | .KECCAK256 => match s.stack with
    | offset :: size :: rest =>
      let bs := MachineState.readPadded s.memory offset.toNat size.toNat
      .ok (s'.replaceStackAndIncrPC (EvmSemantics.keccak256 bs :: rest))
    | _ => underflow

----------------------------------------------------------------------------
-- 4. Environment reads (EnvOps, 16 ops).
----------------------------------------------------------------------------

/-- Execute one EnvOps opcode (ADDRESS / CALL* / CODE* / RETURNDATA*). -/
def env (s s' : State) : Operation.EnvOps → Except ExecutionException State
  | .ADDRESS =>
    .ok (s'.replaceStackAndIncrPC (s.executionEnv.codeOwner.toUInt256 :: s.stack))
  | .BALANCE => match s.stack with
    | a :: rest =>
      .ok (s'.replaceStackAndIncrPC
            ((s.accountMap (AccountAddress.ofUInt256 a)).balance :: rest))
    | _ => underflow
  | .ORIGIN => .ok (s'.replaceStackAndIncrPC (s.executionEnv.sender.toUInt256 :: s.stack))
  | .CALLER => .ok (s'.replaceStackAndIncrPC (s.executionEnv.source.toUInt256 :: s.stack))
  | .CALLVALUE => .ok (s'.replaceStackAndIncrPC (s.executionEnv.weiValue :: s.stack))
  | .CALLDATALOAD => match s.stack with
    | i :: rest =>
      let bs := MachineState.readPadded s.executionEnv.calldata i.toNat 32
      let word := bs.toList.foldl (fun acc b => acc * 256 + b.toNat) 0
      .ok (s'.replaceStackAndIncrPC (UInt256.ofNat word :: rest))
    | _ => underflow
  | .CALLDATASIZE =>
    .ok (s'.replaceStackAndIncrPC (UInt256.ofNat s.executionEnv.calldata.size :: s.stack))
  | .CALLDATACOPY => match s.stack with
    | destOff :: srcOff :: sz :: rest =>
      let bytes := MachineState.readPadded s.executionEnv.calldata srcOff.toNat sz.toNat
      let μ' : MachineState :=
        { s.toMachineState with
            memory := MachineState.writeBytes s.memory bytes destOff.toNat
            activeWords := UInt256.ofNat
                            (MachineState.activeWordsAfter
                              s.activeWords.toNat destOff.toNat sz.toNat) }
      .ok ({ s' with toMachineState := μ' }.replaceStackAndIncrPC rest)
    | _ => underflow
  | .CODESIZE =>
    .ok (s'.replaceStackAndIncrPC (UInt256.ofNat s.executionEnv.code.size :: s.stack))
  | .CODECOPY => match s.stack with
    | destOff :: srcOff :: sz :: rest =>
      let bytes := MachineState.readPadded s.executionEnv.code srcOff.toNat sz.toNat
      let μ' : MachineState :=
        { s.toMachineState with
            memory := MachineState.writeBytes s.memory bytes destOff.toNat
            activeWords := UInt256.ofNat
                            (MachineState.activeWordsAfter
                              s.activeWords.toNat destOff.toNat sz.toNat) }
      .ok ({ s' with toMachineState := μ' }.replaceStackAndIncrPC rest)
    | _ => underflow
  | .GASPRICE => .ok (s'.replaceStackAndIncrPC (s.executionEnv.gasPrice :: s.stack))
  | .EXTCODESIZE => match s.stack with
    | a :: rest =>
      let sz := (s.accountMap (AccountAddress.ofUInt256 a)).code.size
      .ok (s'.replaceStackAndIncrPC (UInt256.ofNat sz :: rest))
    | _ => underflow
  | .EXTCODECOPY => match s.stack with
    | a :: destOff :: srcOff :: sz :: rest =>
      let code := (s.accountMap (AccountAddress.ofUInt256 a)).code
      let bytes := MachineState.readPadded code srcOff.toNat sz.toNat
      let μ' : MachineState :=
        { s.toMachineState with
            memory := MachineState.writeBytes s.memory bytes destOff.toNat
            activeWords := UInt256.ofNat
                            (MachineState.activeWordsAfter
                              s.activeWords.toNat destOff.toNat sz.toNat) }
      .ok ({ s' with toMachineState := μ' }.replaceStackAndIncrPC rest)
    | _ => underflow
  | .RETURNDATASIZE =>
    .ok (s'.replaceStackAndIncrPC (UInt256.ofNat s.returnData.size :: s.stack))
  | .RETURNDATACOPY => match s.stack with
    | destOff :: srcOff :: sz :: rest =>
      if srcOff.toNat + sz.toNat > s.returnData.size then
        .error .InvalidMemoryAccess
      else
        let bytes := MachineState.readPadded s.returnData srcOff.toNat sz.toNat
        let μ' : MachineState :=
          { s.toMachineState with
              memory := MachineState.writeBytes s.memory bytes destOff.toNat
              activeWords := UInt256.ofNat
                              (MachineState.activeWordsAfter
                                s.activeWords.toNat destOff.toNat sz.toNat) }
        .ok ({ s' with toMachineState := μ' }.replaceStackAndIncrPC rest)
    | _ => underflow
  | .EXTCODEHASH => match s.stack with
    | a :: rest =>
      .ok (s'.replaceStackAndIncrPC
            ((s.accountMap (AccountAddress.ofUInt256 a)).codeHash :: rest))
    | _ => underflow

----------------------------------------------------------------------------
-- 5. Block-context reads (BlockOps, 11 ops).
----------------------------------------------------------------------------

/-- Execute one BlockOps opcode (block-context reads + BLOB*). -/
def block (s s' : State) : Operation.BlockOps → Except ExecutionException State
  | .BLOCKHASH => match s.stack with
    | n :: rest =>
      .ok (s'.replaceStackAndIncrPC (s.executionEnv.header.blockHash n :: rest))
    | _ => underflow
  | .COINBASE =>
    .ok (s'.replaceStackAndIncrPC (s.executionEnv.header.coinbase.toUInt256 :: s.stack))
  | .TIMESTAMP =>
    .ok (s'.replaceStackAndIncrPC (s.executionEnv.header.timestamp :: s.stack))
  | .NUMBER =>
    .ok (s'.replaceStackAndIncrPC (s.executionEnv.header.number :: s.stack))
  | .PREVRANDAO =>
    .ok (s'.replaceStackAndIncrPC (s.executionEnv.header.prevRandao :: s.stack))
  | .GASLIMIT =>
    .ok (s'.replaceStackAndIncrPC (s.executionEnv.header.gasLimit :: s.stack))
  | .CHAINID =>
    .ok (s'.replaceStackAndIncrPC (s.executionEnv.header.chainId :: s.stack))
  | .SELFBALANCE =>
    .ok (s'.replaceStackAndIncrPC
          ((s.accountMap s.executionEnv.codeOwner).balance :: s.stack))
  | .BASEFEE =>
    .ok (s'.replaceStackAndIncrPC (s.executionEnv.header.baseFeePerGas :: s.stack))
  | .BLOBHASH => match s.stack with
    | i :: rest =>
      let h := (s.executionEnv.blobVersionedHashes[i.toNat]?).getD ⟨0⟩
      .ok (s'.replaceStackAndIncrPC (h :: rest))
    | _ => underflow
  | .BLOBBASEFEE =>
    .ok (s'.replaceStackAndIncrPC (s.executionEnv.header.blobBaseFee :: s.stack))

----------------------------------------------------------------------------
-- 6. Stack / memory / storage / flow (StackMemFlowOps, 15 ops).
----------------------------------------------------------------------------

/-- Execute one StackMemFlowOps opcode. -/
def stackMemFlow (s s' : State) :
    Operation.StackMemFlowOps → Except ExecutionException State
  | .POP => match s.stack with
    | _ :: rest => .ok (s'.replaceStackAndIncrPC rest)
    | _ => underflow
  | .MLOAD => match s.stack with
    | offset :: rest =>
      let (v, μ') := MachineState.mload s.toMachineState offset
      .ok ({ s' with toMachineState := μ' }.replaceStackAndIncrPC (v :: rest))
    | _ => underflow
  | .MSTORE => match s.stack with
    | offset :: value :: rest =>
      let μ' := MachineState.mstore s.toMachineState offset value
      .ok ({ s' with toMachineState := μ' }.replaceStackAndIncrPC rest)
    | _ => underflow
  | .MSTORE8 => match s.stack with
    | offset :: value :: rest =>
      let μ' := MachineState.mstore8 s.toMachineState offset value
      .ok ({ s' with toMachineState := μ' }.replaceStackAndIncrPC rest)
    | _ => underflow
  | .SLOAD => match s.stack with
    | key :: rest =>
      .ok (s'.replaceStackAndIncrPC
            ((s.accountMap s.executionEnv.codeOwner).storage key :: rest))
    | _ => underflow
  | .SSTORE =>
    if ¬ s.executionEnv.permitStateMutation then static
    else match s.stack with
    | key :: value :: rest =>
      let addr := s.executionEnv.codeOwner
      let acc := s.accountMap addr
      let acc' := { acc with storage := acc.storage.set key value }
      let σ' := s.accountMap.set addr acc'
      .ok ({ s' with accountMap := σ' }.replaceStackAndIncrPC rest)
    | _ => underflow
  | .JUMP => match s.stack with
    | dest :: rest =>
      match Decode.decodeAt s.executionEnv.code dest.toNat with
      | some (.JUMPDEST, none) => .ok { s' with pc := dest, stack := rest }
      | _ => .error .BadJumpDestination
    | _ => underflow
  | .JUMPI => match s.stack with
    | dest :: cond :: rest =>
      if cond.toNat = 0 then
        .ok (s'.replaceStackAndIncrPC rest)
      else
        match Decode.decodeAt s.executionEnv.code dest.toNat with
        | some (.JUMPDEST, none) => .ok { s' with pc := dest, stack := rest }
        | _ => .error .BadJumpDestination
    | _ => underflow
  | .PC       => .ok (s'.replaceStackAndIncrPC (s.pc :: s.stack))
  | .JUMPDEST => .ok s'.incrPC
  | .MSIZE    =>
    .ok (s'.replaceStackAndIncrPC (MachineState.msize s.toMachineState :: s.stack))
  | .GAS      => .ok (s'.replaceStackAndIncrPC (UInt256.ofNat s.gasAvailable :: s.stack))
  | .TLOAD => match s.stack with
    | key :: rest =>
      .ok (s'.replaceStackAndIncrPC
            ((s.accountMap s.executionEnv.codeOwner).tstorage key :: rest))
    | _ => underflow
  | .TSTORE =>
    if ¬ s.executionEnv.permitStateMutation then static
    else match s.stack with
    | key :: value :: rest =>
      let addr := s.executionEnv.codeOwner
      let acc := s.accountMap addr
      let acc' := { acc with tstorage := acc.tstorage.set key value }
      let σ' := s.accountMap.set addr acc'
      .ok ({ s' with accountMap := σ' }.replaceStackAndIncrPC rest)
    | _ => underflow
  | .MCOPY => match s.stack with
    | destOff :: srcOff :: sz :: rest =>
      let μ' := MachineState.mcopy s.toMachineState destOff srcOff sz
      .ok ({ s' with toMachineState := μ' }.replaceStackAndIncrPC rest)
    | _ => underflow

----------------------------------------------------------------------------
-- 7. PUSH / DUP / SWAP (single-field structures).
----------------------------------------------------------------------------

/-- Execute a PUSH (PUSH0 through PUSH32). -/
def push (s s' : State) (op : Operation.PushOp)
    (argOpt : Option (UInt256 × Nat)) : Except ExecutionException State :=
  match op.width.val, argOpt with
  | 0, _              => .ok (s'.replaceStackAndIncrPC (⟨0⟩ :: s.stack))
  | _+1, some (d, n)  => .ok (s'.replaceStackAndIncrPC (d :: s.stack) (pcΔ := n + 1))
  | _+1, none         => .error .InvalidInstruction

/-- Execute a DUP (DUP1 through DUP16). -/
def dup (s s' : State) (op : Operation.DupOp) : Except ExecutionException State :=
  match s.stack[op.idx.val]? with
  | some v => .ok (s'.replaceStackAndIncrPC (v :: s.stack))
  | none   => underflow

/-- Execute a SWAP (SWAP1 through SWAP16). -/
def swap (s s' : State) (op : Operation.SwapOp) : Except ExecutionException State :=
  match s.stack.exchange 0 (op.idx.val + 1) with
  | some stk' => .ok (s'.replaceStackAndIncrPC stk')
  | none      => underflow

----------------------------------------------------------------------------
-- 8. EIP-8024: DUPN / SWAPN / EXCHANGE.
----------------------------------------------------------------------------

/-- Execute the EIP-8024 DUPN opcode. -/
def dupN (s s' : State) (op : Operation.DupNOp) : Except ExecutionException State :=
  match s.stack[op.n.val]? with
  | some v => .ok (s'.replaceStackAndIncrPC (v :: s.stack) (pcΔ := 2))
  | none   => underflow

/-- Execute the EIP-8024 SWAPN opcode. -/
def swapN (s s' : State) (op : Operation.SwapNOp) : Except ExecutionException State :=
  match s.stack.exchange 0 (op.n.val + 1) with
  | some stk' => .ok (s'.replaceStackAndIncrPC stk' (pcΔ := 2))
  | none      => underflow

/-- Execute the EIP-8024 EXCHANGE opcode. -/
def exchange (s s' : State) (op : Operation.ExchangeOp) : Except ExecutionException State :=
  match s.stack.exchange (op.n + 1) (op.m + 1) with
  | some stk' => .ok (s'.replaceStackAndIncrPC stk' (pcΔ := 2))
  | none      => underflow

----------------------------------------------------------------------------
-- 9. Logging (LOG0-LOG4).
----------------------------------------------------------------------------

/-- Pop the top `k` elements of `stk` (preserving their order in the
    output list); returns `none` if `stk` has fewer than `k` elements.

    The order is recovered by accumulating into `acc` (which fills in
    reverse) and reversing once at the base case. The companion lemma
    `popN_correct` (below) certifies the relation
    `popN stk k = some (topics, rest) ↔ topics.length = k ∧ stk = topics ++ rest`,
    which is what `log_sound` needs to reconstruct the `Step.log` witness. -/
def popN (stk : Stack UInt256) (k : Nat) : Option (List UInt256 × Stack UInt256) :=
  go stk k []
where
  /-- Tail-recursive worker: accumulate the popped elements into `acc`
      (in reverse), reversing once at the base case. -/
  go (stk : Stack UInt256) (k : Nat) (acc : List UInt256) :
      Option (List UInt256 × Stack UInt256) :=
    match k, stk with
    | 0, rest          => some (acc.reverse, rest)
    | _+1, top :: rest => go rest (k-1) (top :: acc)
    | _+1, []          => none

/-- Generalisation of `popN_correct` to the accumulator-passing `go`.
    States that the `taken` prefix popped off `stk` exists, has length `k`,
    and that the final `topics` list equals `acc.reverse ++ taken`. The
    base case `acc = []` gives `popN_correct`. -/
theorem popN_go_correct (k : Nat) :
    ∀ (stk : Stack UInt256) (acc topics rest : List UInt256),
    popN.go stk k acc = some (topics, rest) →
    ∃ taken : List UInt256,
      taken.length = k ∧ stk = taken ++ rest ∧ topics = acc.reverse ++ taken := by
  induction k with
  | zero =>
    intro stk acc topics rest h
    unfold popN.go at h
    simp at h
    obtain ⟨h_topics, h_rest⟩ := h
    refine ⟨[], rfl, ?_, ?_⟩
    · simp [← h_rest]
    · simp [← h_topics]
  | succ k ih =>
    intro stk acc topics rest h
    match stk with
    | [] => unfold popN.go at h; simp at h
    | top :: rest_stk =>
      unfold popN.go at h
      simp at h
      obtain ⟨taken, h_len, h_eq, h_topics⟩ := ih rest_stk (top :: acc) topics rest h
      refine ⟨top :: taken, ?_, ?_, ?_⟩
      · simp [h_len]
      · simp [h_eq]
      · simp [h_topics]

/-- Correctness of `popN`: if `popN stk k = some (topics, rest)` then the
    output list has the requested length and partitions the input stack
    into a prefix (`topics`) and a suffix (`rest`). -/
theorem popN_correct (stk : Stack UInt256) (k : Nat) (topics rest : List UInt256)
    (h : popN stk k = some (topics, rest)) :
    topics.length = k ∧ stk = topics ++ rest := by
  unfold popN at h
  obtain ⟨taken, h_len, h_eq, h_topics⟩ := popN_go_correct k stk [] topics rest h
  simp at h_topics
  subst h_topics
  exact ⟨h_len, h_eq⟩

/-- Execute a LOG (LOG0 through LOG4). -/
def log (s s' : State) (op : Operation.LogOp) : Except ExecutionException State :=
  if ¬ s.executionEnv.permitStateMutation then static
  else
    match s.stack with
    | offset :: size :: rest =>
      match popN rest op.topics.val with
      | some (topics, rest') =>
        let entry : LogEntry :=
          { address := s.executionEnv.codeOwner
            topics  := topics.toArray
            data    := MachineState.readPadded s.memory offset.toNat size.toNat }
        .ok ({ s' with substate := s.substate.appendLog entry }.replaceStackAndIncrPC rest')
      | none => underflow
    | _ => underflow

----------------------------------------------------------------------------
-- 10. System (SystemOps): RETURN, REVERT, INVALID, plus out-of-scope ops.
----------------------------------------------------------------------------

/-- Execute one SystemOps opcode (RETURN/REVERT/INVALID; CREATE/CALL family stubbed). -/
def system (s s' : State) : Operation.SystemOps → Except ExecutionException State
  | .RETURN => match s.stack with
    | offset :: size :: rest =>
      let bs := MachineState.readPadded s.memory offset.toNat size.toNat
      .ok { s' with halt := .Returned, hReturn := bs, stack := rest }
    | _ => underflow
  | .REVERT => match s.stack with
    | offset :: size :: rest =>
      let bs := MachineState.readPadded s.memory offset.toNat size.toNat
      .ok { s' with halt := .Reverted, hReturn := bs, stack := rest }
    | _ => underflow
  | .INVALID => .error .InvalidInstruction
  -- Out-of-scope in v1.
  | .CREATE | .CREATE2 | .CALL | .CALLCODE
  | .DELEGATECALL | .STATICCALL | .SELFDESTRUCT => .error .InvalidInstruction

end stepF

----------------------------------------------------------------------------
-- Top-level dispatcher.
----------------------------------------------------------------------------

/-- Top-level executable shadow — halt/decode/gas dispatch into per-group helpers. -/
def stepF (s : State) : Except ExecutionException State := Id.run do
  match s.halt with
  | .Running =>
    match s.decoded with
    | none => .error .InvalidInstruction
    | some (op, argOpt) =>
      let cost := Gas.cost op
      if h_g : cost ≤ s.gasAvailable then
        let s' := s.consumeGas cost h_g
        match op with
        | .StopArith op    => stepF.stopArith    s s' op
        | .CompBit op      => stepF.compBit      s s' op
        | .Keccak op       => stepF.keccak       s s' op
        | .Env op          => stepF.env          s s' op
        | .Block op        => stepF.block        s s' op
        | .StackMemFlow op => stepF.stackMemFlow s s' op
        | .Push op         => stepF.push         s s' op argOpt
        | .Dup op          => stepF.dup          s s' op
        | .Swap op         => stepF.swap         s s' op
        | .DupN op         => stepF.dupN         s s' op
        | .SwapN op        => stepF.swapN        s s' op
        | .Exchange op     => stepF.exchange     s s' op
        | .Log op          => stepF.log          s s' op
        | .System op       => stepF.system       s s' op
      else
        .error .OutOfGas
  | _ => .error .InvalidInstruction

end EVM
end EvmSemantics
