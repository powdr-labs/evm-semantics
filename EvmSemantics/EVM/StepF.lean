module

public import EvmSemantics.EVM.Step
public import EvmSemantics.EVM.Precompile
public import EvmSemantics.Data.Rlp

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
successor). The CALL family, CREATE/CREATE2, SELFDESTRUCT, and LOG are
all implemented — `stepF` mirrors the entire `StepRunning` rule set.

The LOG branch uses an auxiliary `popN` helper (defined in section 9
below) to pop the variable number of topics. `popN_correct` proves it
preserves the list invariant `topics.length = k ∧ stk = topics ++ rest`,
which `log_sound` uses to recover the witness list expected by
`StepRunning.log`.

`stepF` charges dynamic gas in **chained** form
(`((g - base) - memDelta) - kwc`), via `consumeGas` and `consumeMemExp`.
The bundled `Gas.<op>Total` totals used by `StepRunning` (single
`Nat`-valued sum: base + memory expansion + per-word / per-byte
dynamic) equal the chain by `Nat.sub_add_eq`; the soundness proof in
`Equiv.lean` bridges between the two forms.
-/

@[expose] public section

namespace EvmSemantics
namespace EVM

/-- Sugar for the stack-underflow exception result. -/
def underflow : Except ExecutionException State := .error .StackUnderflow
/-- Sugar for the static-mode-violation exception result. -/
def static    : Except ExecutionException State := .error .StaticModeViolation

namespace State

/-- Subtract `n` from the available gas. The proof `h` witnesses that the
    subtraction does not underflow; without it `consumeGas` would silently
    saturate at `0`, divorcing the function from its precondition. The
    proof is currently unused in the body (Nat subtraction is total) but
    keeps the call sites from accidentally subtracting too much. -/
@[nolint unusedArguments]
def consumeGas (s : State) (n : Nat) (_h : n ≤ s.gasAvailable) : State :=
  { s with gasAvailable := s.gasAvailable - n }

/-- `s` has enough gas to pay the memory-expansion cost for touching
    `[offset, offset+sz)`. Used as the precondition of `consumeMemExp` and
    by `stepF.chargeMem`. -/
abbrev canExpandMemory (s : State) (offset sz : Nat) : Prop :=
  MachineState.memExpansionDelta s.activeWords.toNat offset sz ≤ s.gasAvailable

/-- Two-range version of `canExpandMemory`, for MCOPY (read and write ranges). -/
abbrev canExpandMemory2 (s : State) (off1 sz1 off2 sz2 : Nat) : Prop :=
  MachineState.memExpansionDelta2 s.activeWords.toNat off1 sz1 off2 sz2 ≤ s.gasAvailable

/-- Charge memory-expansion gas for the byte range `[offset, offset+sz)` and
    advance the active-words high-water mark. The hypothesis `h` witnesses
    that the expansion cost fits in the available gas (it is *not* combined
    with op cost — callers are expected to first `consumeGas` for the op and
    then call this on the resulting state, mirroring `stepF.chargeMem`). -/
def consumeMemExp (s : State) (offset sz : Nat) (h : s.canExpandMemory offset sz) : State :=
  let new := MachineState.activeWordsAfter s.activeWords.toNat offset sz
  let cost := MachineState.memCost new - MachineState.memCost s.activeWords.toNat
  { (s.consumeGas cost h) with activeWords := UInt256.ofNat new }

/-- Two-range version of `consumeMemExp`, used by MCOPY which touches both
    the source read range and the destination write range. Charges expansion
    gas for the union of the two ranges. -/
def consumeMemExp2 (s : State) (off1 sz1 off2 sz2 : Nat)
    (h : s.canExpandMemory2 off1 sz1 off2 sz2) : State :=
  let new1 := MachineState.activeWordsAfter s.activeWords.toNat off1 sz1
  let new2 := MachineState.activeWordsAfter new1 off2 sz2
  let cost := MachineState.memCost new2 - MachineState.memCost s.activeWords.toNat
  { (s.consumeGas cost h) with activeWords := UInt256.ofNat new2 }

/-- Push a new stack and advance the pc by `pcΔ` (default 1). -/
def replaceStackAndIncrPC (s : State) (stk : List UInt256) (pcΔ : Nat := 1) : State :=
  { s with stack := stk, pc := s.pc + UInt256.ofNat pcΔ }

/-- Advance the pc by `pcΔ` (default 1) without touching the stack. -/
def incrPC (s : State) (pcΔ : Nat := 1) : State :=
  { s with pc := s.pc + UInt256.ofNat pcΔ }

end State

/-- Charge Yellow-Paper memory-expansion gas for touching `[offset, offset+sz)`
    on `s`, and advance the active-words high-water mark accordingly.  Returns
    `.error .OutOfGas` if the expansion would exhaust the remaining gas (which
    is also what protects the runtime from OOM on absurd offsets/sizes — see
    `MachineState.memExpansionDelta`). -/
def chargeMem (s : State) (offset sz : Nat) : Except ExecutionException State :=
  if h : s.canExpandMemory offset sz then
    .ok (s.consumeMemExp offset sz h)
  else
    .error .OutOfGas

/-- Two-range version of `chargeMem`, used by MCOPY which touches both the
    source-read and destination-write ranges. -/
def chargeMem2 (s : State) (off1 sz1 off2 sz2 : Nat) : Except ExecutionException State :=
  if h : s.canExpandMemory2 off1 sz1 off2 sz2 then
    .ok (s.consumeMemExp2 off1 sz1 off2 sz2 h)
  else
    .error .OutOfGas

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
    | a :: b :: rest =>
      -- Dynamic per-byte exponent cost: `50 · byteLen(b)` (EIP-160).
      let dyn := Gas.expByteCost s.fork b
      if h : dyn ≤ s'.gasAvailable then
        .ok ((s'.consumeGas dyn h).replaceStackAndIncrPC (UInt256.expFast a b :: rest))
      else .error .OutOfGas
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
      match chargeMem s' offset.toNat size.toNat with
      | .ok s'' =>
        let dyn := Gas.keccakWordCost size
        if h : dyn ≤ s''.gasAvailable then
          let s''' := s''.consumeGas dyn h
          let bs := MachineState.readPadded s.memory offset.toNat size.toNat
          .ok (s'''.replaceStackAndIncrPC (EvmSemantics.keccak256 bs :: rest))
        else .error .OutOfGas
      | .error e => .error e
    | _ => underflow

----------------------------------------------------------------------------
-- 4. Environment reads (EnvOps, 16 ops).
----------------------------------------------------------------------------

/-- Execute one EnvOps opcode (ADDRESS / CALL* / CODE* / RETURNDATA*). -/
def env (s s' : State) : Operation.EnvOps → Except ExecutionException State
  | .ADDRESS =>
    .ok (s'.replaceStackAndIncrPC (s.executionEnv.address.toUInt256 :: s.stack))
  | .BALANCE => match s.stack with
    | a :: rest =>
      .ok (s'.replaceStackAndIncrPC
            ((s.accountMap (AccountAddress.ofUInt256 a)).balance :: rest))
    | _ => underflow
  | .ORIGIN => .ok (s'.replaceStackAndIncrPC (s.executionEnv.origin.toUInt256 :: s.stack))
  | .CALLER => .ok (s'.replaceStackAndIncrPC (s.executionEnv.caller.toUInt256 :: s.stack))
  | .CALLVALUE => .ok (s'.replaceStackAndIncrPC (s.executionEnv.weiValue :: s.stack))
  | .CALLDATALOAD => match s.stack with
    | i :: rest =>
      -- A `readPadded` of a fixed 32 bytes allocates 32 bytes regardless of the
      -- offset `i` (out-of-range reads zero-pad), so no bound is needed here.
      let bs := MachineState.readPadded s.executionEnv.calldata i.toNat 32
      let word := bs.toList.foldl (fun acc b => acc * 256 + b.toNat) 0
      .ok (s'.replaceStackAndIncrPC (UInt256.ofNat word :: rest))
    | _ => underflow
  | .CALLDATASIZE =>
    .ok (s'.replaceStackAndIncrPC (UInt256.ofNat s.executionEnv.calldata.size :: s.stack))
  | .CALLDATACOPY => match s.stack with
    | destOff :: srcOff :: sz :: rest =>
      match chargeMem s' destOff.toNat sz.toNat with
      | .ok s'' =>
        let dyn := Gas.copyWordCost sz
        if h : dyn ≤ s''.gasAvailable then
          let s''' := s''.consumeGas dyn h
          let bytes := MachineState.readPadded s.executionEnv.calldata srcOff.toNat sz.toNat
          let μ' : MachineState :=
            { s'''.toMachineState with
                memory := MachineState.writeBytes s.memory bytes destOff.toNat }
          .ok ({ s''' with toMachineState := μ' }.replaceStackAndIncrPC rest)
        else .error .OutOfGas
      | .error e => .error e
    | _ => underflow
  | .CODESIZE =>
    .ok (s'.replaceStackAndIncrPC (UInt256.ofNat s.executionEnv.code.size :: s.stack))
  | .CODECOPY => match s.stack with
    | destOff :: srcOff :: sz :: rest =>
      match chargeMem s' destOff.toNat sz.toNat with
      | .ok s'' =>
        let dyn := Gas.copyWordCost sz
        if h : dyn ≤ s''.gasAvailable then
          let s''' := s''.consumeGas dyn h
          let bytes := MachineState.readPadded s.executionEnv.code srcOff.toNat sz.toNat
          let μ' : MachineState :=
            { s'''.toMachineState with
                memory := MachineState.writeBytes s.memory bytes destOff.toNat }
          .ok ({ s''' with toMachineState := μ' }.replaceStackAndIncrPC rest)
        else .error .OutOfGas
      | .error e => .error e
    | _ => underflow
  | .GASPRICE => .ok (s'.replaceStackAndIncrPC (s.executionEnv.gasPrice :: s.stack))
  | .EXTCODESIZE => match s.stack with
    | a :: rest =>
      let sz := (s.accountMap (AccountAddress.ofUInt256 a)).code.size
      .ok (s'.replaceStackAndIncrPC (UInt256.ofNat sz :: rest))
    | _ => underflow
  | .EXTCODECOPY => match s.stack with
    | a :: destOff :: srcOff :: sz :: rest =>
      match chargeMem s' destOff.toNat sz.toNat with
      | .ok s'' =>
        let dyn := Gas.copyWordCost sz
        if h : dyn ≤ s''.gasAvailable then
          let s''' := s''.consumeGas dyn h
          let code := (s.accountMap (AccountAddress.ofUInt256 a)).code
          let bytes := MachineState.readPadded code srcOff.toNat sz.toNat
          let μ' : MachineState :=
            { s'''.toMachineState with
                memory := MachineState.writeBytes s.memory bytes destOff.toNat }
          .ok ({ s''' with toMachineState := μ' }.replaceStackAndIncrPC rest)
        else .error .OutOfGas
      | .error e => .error e
    | _ => underflow
  | .RETURNDATASIZE =>
    .ok (s'.replaceStackAndIncrPC (UInt256.ofNat s.returnData.size :: s.stack))
  | .RETURNDATACOPY => match s.stack with
    | destOff :: srcOff :: sz :: rest =>
      -- Spec-mandated OOB check on the return-data buffer (it is NOT
      -- memory and is bounded by `returnData.size`, not by gas).
      if srcOff.toNat + sz.toNat > s.returnData.size then
        .error .InvalidMemoryAccess
      else
        match chargeMem s' destOff.toNat sz.toNat with
        | .ok s'' =>
          let dyn := Gas.copyWordCost sz
          if h : dyn ≤ s''.gasAvailable then
            let s''' := s''.consumeGas dyn h
            let bytes := MachineState.readPadded s.returnData srcOff.toNat sz.toNat
            let μ' : MachineState :=
              { s'''.toMachineState with
                  memory := MachineState.writeBytes s.memory bytes destOff.toNat }
            .ok ({ s''' with toMachineState := μ' }.replaceStackAndIncrPC rest)
          else .error .OutOfGas
        | .error e => .error e
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
          ((s.accountMap s.executionEnv.address).balance :: s.stack))
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
      match chargeMem s' offset.toNat 32 with
      | .ok s'' =>
        let (v, μ') := MachineState.mload s''.toMachineState offset
        .ok ({ s'' with toMachineState := μ' }.replaceStackAndIncrPC (v :: rest))
      | .error e => .error e
    | _ => underflow
  | .MSTORE => match s.stack with
    | offset :: value :: rest =>
      match chargeMem s' offset.toNat 32 with
      | .ok s'' =>
        let μ' := MachineState.mstore s''.toMachineState offset value
        .ok ({ s'' with toMachineState := μ' }.replaceStackAndIncrPC rest)
      | .error e => .error e
    | _ => underflow
  | .MSTORE8 => match s.stack with
    | offset :: value :: rest =>
      match chargeMem s' offset.toNat 1 with
      | .ok s'' =>
        let μ' := MachineState.mstore8 s''.toMachineState offset value
        .ok ({ s'' with toMachineState := μ' }.replaceStackAndIncrPC rest)
      | .error e => .error e
    | _ => underflow
  | .SLOAD => match s.stack with
    | key :: rest =>
      .ok (s'.replaceStackAndIncrPC
            ((s.accountMap s.executionEnv.address).storage key :: rest))
    | _ => underflow
  | .SSTORE =>
    if ¬ s.executionEnv.permitStateMutation then static
    -- EIP-2200 stipend sentry: at Cancun, halt OOG if gasleft ≤ 2300,
    -- *regardless* of whether the actual `sstoreCost` would fit.
    else if Gas.sstoreSentry s.fork s'.gasAvailable then
      .error .OutOfGas
    else match s.stack with
    | key :: value :: rest =>
      let addr     := s.executionEnv.address
      let acc      := s.accountMap addr
      let current  := acc.storage key
      let original := s.substate.originalStorage addr key
      let cost     := Gas.sstoreCost s.fork original current value
      if h : cost ≤ s'.gasAvailable then
        let acc' := { acc with storage := acc.storage.set key value }
        let σ'   := s.accountMap.set addr acc'
        -- Accumulate the EIP-1283 / EIP-2200 / EIP-3529 refund delta into
        -- `Substate.refundBalance`. `Gas.sstoreRefund` returns a signed
        -- `Int` (the delta is negative on the "un-clear" path), so we
        -- saturate at 0: `refundBalance` is a `UInt256` and the YP caps
        -- the *applied* refund at `gas_used / refundDenom` anyway, so
        -- intermediate negatives are bounded by the positives the same
        -- transaction accrued earlier.
        let refDelta := Gas.sstoreRefund s.fork original current value
        let rb : Int := (s.substate.refundBalance.toNat : Int) + refDelta
        let rb' : Nat := if rb < 0 then 0 else rb.toNat
        let sub' : Substate :=
          { s.substate with refundBalance := UInt256.ofNat rb' }
        .ok ({ (s'.consumeGas cost h) with
                 accountMap := σ', substate := sub' }.replaceStackAndIncrPC rest)
      else .error .OutOfGas
    | _ => underflow
  | .JUMP => match s.stack with
    | dest :: rest =>
      if Decode.isValidJumpDest s.executionEnv.code dest.toNat then
        .ok { s' with pc := dest, stack := rest }
      else .error .BadJumpDestination
    | _ => underflow
  | .JUMPI => match s.stack with
    | dest :: cond :: rest =>
      if cond.toNat = 0 then
        .ok (s'.replaceStackAndIncrPC rest)
      else if Decode.isValidJumpDest s.executionEnv.code dest.toNat then
        .ok { s' with pc := dest, stack := rest }
      else .error .BadJumpDestination
    | _ => underflow
  | .PC       => .ok (s'.replaceStackAndIncrPC (s.pc :: s.stack))
  | .JUMPDEST => .ok s'.incrPC
  | .MSIZE    =>
    .ok (s'.replaceStackAndIncrPC (MachineState.msize s.toMachineState :: s.stack))
  -- GAS pushes the remaining gas *after* this opcode's own cost is deducted
  -- (Yellow Paper §9.4.7 / EIP-150): so we read `s'.gasAvailable`, not the
  -- pre-dispatch `s.gasAvailable`.
  | .GAS      => .ok (s'.replaceStackAndIncrPC (UInt256.ofNat s'.gasAvailable :: s.stack))
  | .TLOAD => match s.stack with
    | key :: rest =>
      .ok (s'.replaceStackAndIncrPC
            ((s.accountMap s.executionEnv.address).tstorage key :: rest))
    | _ => underflow
  | .TSTORE =>
    if ¬ s.executionEnv.permitStateMutation then static
    else match s.stack with
    | key :: value :: rest =>
      let addr := s.executionEnv.address
      let acc := s.accountMap addr
      let acc' := { acc with tstorage := acc.tstorage.set key value }
      let σ' := s.accountMap.set addr acc'
      .ok ({ s' with accountMap := σ' }.replaceStackAndIncrPC rest)
    | _ => underflow
  | .MCOPY => match s.stack with
    | destOff :: srcOff :: sz :: rest =>
      -- MCOPY touches both `[srcOff, srcOff+sz)` (read) and
      -- `[destOff, destOff+sz)` (write); we charge expansion for the union.
      match chargeMem2 s' destOff.toNat sz.toNat srcOff.toNat sz.toNat with
      | .ok s'' =>
        let dyn := Gas.copyWordCost sz
        if h : dyn ≤ s''.gasAvailable then
          let s''' := s''.consumeGas dyn h
          let μ' := MachineState.mcopy s'''.toMachineState destOff srcOff sz
          .ok ({ s''' with toMachineState := μ' }.replaceStackAndIncrPC rest)
        else .error .OutOfGas
      | .error e => .error e
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
    which is what `log_sound` needs to reconstruct the `StepRunning.log`
    witness. -/
def popN (stk : List UInt256) (k : Nat) : Option (List UInt256 × List UInt256) :=
  go stk k []
where
  /-- Tail-recursive worker: accumulate the popped elements into `acc`
      (in reverse), reversing once at the base case. -/
  go (stk : List UInt256) (k : Nat) (acc : List UInt256) :
      Option (List UInt256 × List UInt256) :=
    match k, stk with
    | 0, rest          => some (acc.reverse, rest)
    | _+1, top :: rest => go rest (k-1) (top :: acc)
    | _+1, []          => none

/-- Generalisation of `popN_correct` to the accumulator-passing `go`.
    States that the `taken` prefix popped off `stk` exists, has length `k`,
    and that the final `topics` list equals `acc.reverse ++ taken`. The
    base case `acc = []` gives `popN_correct`. -/
theorem popN_go_correct (k : Nat) :
    ∀ (stk : List UInt256) (acc topics rest : List UInt256),
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
theorem popN_correct (stk : List UInt256) (k : Nat) (topics rest : List UInt256)
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
      match chargeMem s' offset.toNat size.toNat with
      | .ok s'' =>
        let dyn := Gas.logDataCost size
        if h : dyn ≤ s''.gasAvailable then
          match popN rest op.topics.val with
          | some (topics, rest') =>
            let entry : LogEntry :=
              { address := s.executionEnv.address
                topics  := topics.toArray
                data    := MachineState.readPadded s.memory offset.toNat size.toNat }
            .ok ({ (s''.consumeGas dyn h) with substate := s.substate.appendLog entry }
                   |>.replaceStackAndIncrPC rest')
          | none => underflow
        else .error .OutOfGas
      | .error e => .error e
    | _ => underflow

----------------------------------------------------------------------------
-- 10. System (SystemOps): RETURN, REVERT, INVALID, plus out-of-scope ops.
----------------------------------------------------------------------------

/-- Execute one SystemOps opcode (RETURN/REVERT/INVALID; CREATE/CALL family stubbed). -/
def system (s s' : State) : Operation.SystemOps → Except ExecutionException State
  | .RETURN => match s.stack with
    | offset :: size :: rest =>
      match chargeMem s' offset.toNat size.toNat with
      | .ok s'' =>
        let bs := MachineState.readPadded s.memory offset.toNat size.toNat
        .ok { s'' with halt := .Returned, hReturn := bs, stack := rest }
      | .error e => .error e
    | _ => underflow
  | .REVERT => match s.stack with
    | offset :: size :: rest =>
      match chargeMem s' offset.toNat size.toNat with
      | .ok s'' =>
        let bs := MachineState.readPadded s.memory offset.toNat size.toNat
        .ok { s'' with halt := .Reverted, hReturn := bs, stack := rest }
      | .error e => .error e
    | _ => underflow
  | .INVALID => .error .InvalidInstruction
  | .CALL => match s.stack with
    | gasArg :: toArg :: value :: argsOff :: argsLen :: retOff :: retLen :: rest =>
      -- Static-mode check: a value-transferring CALL would mutate balances
      -- and so is rejected outright in a static frame. Zero-value CALLs are
      -- still permitted (they cannot mutate state by themselves, and the
      -- static flag propagates into the callee frame).
      if ¬ s.executionEnv.permitStateMutation ∧ value.toNat ≠ 0 then static
      else
      -- `s'` already paid the base (`G_call`) fee. Charge memory expansion for
      -- both the args and return ranges, then the value/new-account surcharge.
      match chargeMem2 s' argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat with
      | .error e => .error e
      | .ok s2 =>
        let tgt      := AccountAddress.ofUInt256 toArg
        let callee   := s2.accountMap tgt
        let valNZ    : Bool := value.toNat != 0
        let surcharge := Gas.callSurcharge s.fork valNZ callee.isEmpty
        if hsc : surcharge ≤ s2.gasAvailable then
          let s3 := s2.consumeGas surcharge hsc
          let caller := s3.accountMap s3.executionEnv.address
          -- Depth limit or insufficient balance ⇒ the call is not taken: the
          -- forwarded gas is *not* spent and `0` is pushed. The caller's
          -- `returnData` buffer is cleared (every CALL-family opcode resets
          -- it, including this pre-execution failure path). YP §H.2: when
          -- the call would have transferred non-zero `value` the 2300-gas
          -- stipend that the surcharge had earmarked for the callee is
          -- refunded to the caller, since no callee runs to receive it.
          if s3.executionEnv.depth ≥ 1024 ∨ caller.balance < value then
            let s3' :=
              if valNZ then
                { s3 with gasAvailable := s3.gasAvailable + Gas.callStipend }
              else s3
            .ok ({ s3' with returnData := .empty }.replaceStackAndIncrPC
                   (UInt256.ofNat 0 :: rest))
          else
            -- EIP-150: forward at most 63/64 of the remaining gas. Per
            -- `Gas.forwardGas`, pre-EIP-150 (Frontier/Homestead) is
            -- *uncapped* — `gasArg` is forwarded verbatim and a
            -- `gasArg > s3.gasAvailable` falls into the `else` branch
            -- below as `OutOfGas`. Post-EIP-150 it's `min(gasArg, g - g/64)`.
            -- The callee additionally receives the 2300-gas stipend on
            -- a value-transferring CALL (funded by the `G_callvalue`
            -- surcharge already paid above).
            let forwarded := Gas.forwardGas s.fork s3.gasAvailable gasArg.toNat
            if hfw : forwarded ≤ s3.gasAvailable then
              let s4       := s3.consumeGas forwarded hfw
              let childGas := forwarded + (bif valNZ then Gas.callStipend else 0)
              let calldata := MachineState.readPadded s4.memory argsOff.toNat argsLen.toNat
              -- YP §9 precompile dispatch is handled *after* this `enterCall`
              -- by the generic precompile arm at the top of `stepF`'s
              -- running branch — see the `Precompile.isPrecompile` check
              -- there. This keeps the CALL handler oblivious to the
              -- precompile-vs-bytecode distinction.
              .ok (s4.enterCall rest tgt tgt value calldata callee.code
                     childGas retOff.toNat retLen.toNat)
            else .error .OutOfGas
        else .error .OutOfGas
    | _ => underflow
  | .CALLCODE => match s.stack with
    | gasArg :: toArg :: value :: argsOff :: argsLen :: retOff :: retLen :: rest =>
      -- CALLCODE differs from CALL in three ways: (i) no static-mode check —
      -- the value "transfer" is caller→caller, a no-op on balances and so
      -- not a state mutation; (ii) the new-account portion of the surcharge
      -- never applies (we never create an account, only borrow code); (iii)
      -- the callee runs in the caller's storage/address context.
      match chargeMem2 s' argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat with
      | .error e => .error e
      | .ok s2 =>
        let codeAddr  := AccountAddress.ofUInt256 toArg  -- where the code comes from
        let codeSrc   := s2.accountMap codeAddr
        let valNZ     : Bool := value.toNat != 0
        let surcharge := Gas.callSurcharge s.fork valNZ false
        if hsc : surcharge ≤ s2.gasAvailable then
          let s3 := s2.consumeGas surcharge hsc
          let caller := s3.accountMap s3.executionEnv.address
          -- Same YP §H.2 stipend refund as CALL: failed value-NZ
          -- CALLCODE gives 2300 back to the caller.
          if s3.executionEnv.depth ≥ 1024 ∨ caller.balance < value then
            let s3' :=
              if valNZ then
                { s3 with gasAvailable := s3.gasAvailable + Gas.callStipend }
              else s3
            .ok ({ s3' with returnData := .empty }.replaceStackAndIncrPC
                   (UInt256.ofNat 0 :: rest))
          else
            let forwarded := Gas.forwardGas s.fork s3.gasAvailable gasArg.toNat
            if hfw : forwarded ≤ s3.gasAvailable then
              let s4       := s3.consumeGas forwarded hfw
              let childGas := forwarded + (bif valNZ then Gas.callStipend else 0)
              let calldata := MachineState.readPadded s4.memory argsOff.toNat argsLen.toNat
              -- Pass the *caller's* address as the call target so
              -- `enterCall`'s self-transfer is a balance no-op and the
              -- callee's `address` stays the caller; supply the target
              -- account's code as the new frame's code. Precompile
              -- dispatch (keyed on `codeAddr`) happens at the top of
              -- the next `stepF` iteration via the generic precompile
              -- arm — but note that for CALLCODE the *frame address*
              -- stays the caller, so the precompile arm won't fire and
              -- the borrowed bytecode runs instead. (This matches the
              -- YP: CALLCODE-ing into a precompile address just runs
              -- the precompile's empty code in the caller's context.)
              .ok (s4.enterCall rest s4.executionEnv.address codeAddr value calldata
                     codeSrc.code childGas retOff.toNat retLen.toNat)
            else .error .OutOfGas
        else .error .OutOfGas
    | _ => underflow
  | .DELEGATECALL => match s.stack with
    | gasArg :: toArg :: argsOff :: argsLen :: retOff :: retLen :: rest =>
      -- DELEGATECALL pops six items (no `value`). No transfer happens; the
      -- callee runs in the caller's storage/address context AND inherits
      -- the caller's `caller` (msg.sender) and `weiValue` (CALLVALUE).
      -- No new-account surcharge applies and there's no balance check.
      match chargeMem2 s' argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat with
      | .error e => .error e
      | .ok s2 =>
        let tgt      := AccountAddress.ofUInt256 toArg
        let callee   := s2.accountMap tgt
        if s2.executionEnv.depth ≥ 1024 then
          .ok ({ s2 with returnData := .empty }.replaceStackAndIncrPC
                 (UInt256.ofNat 0 :: rest))
        else
          let forwarded := Gas.forwardGas s.fork s2.gasAvailable gasArg.toNat
          if hfw : forwarded ≤ s2.gasAvailable then
            let s3       := s2.consumeGas forwarded hfw
            let calldata := MachineState.readPadded s3.memory argsOff.toNat argsLen.toNat
            -- DELEGATECALL: no stipend (no value), so `childGas = forwarded`.
            -- Precompile dispatch (if `tgt` is in `0x01..0x09`) is the
            -- generic precompile arm's job at the top of the next
            -- iteration; the frame's `codeAddr := tgt` is set by
            -- `enterCallFor` so the arm has the right key.
            .ok (s3.enterCallFor .DelegateCall rest tgt ⟨0⟩ calldata
                   callee.code forwarded retOff.toNat retLen.toNat)
          else .error .OutOfGas
    | _ => underflow
  | .STATICCALL => match s.stack with
    | gasArg :: toArg :: argsOff :: argsLen :: retOff :: retLen :: rest =>
      -- STATICCALL pops six items (no `value`). No transfer happens; the
      -- callee runs in the *target's* context but with
      -- `permitStateMutation = false`, so any state-mutating opcode inside
      -- the callee frame raises `StaticModeViolation`.
      match chargeMem2 s' argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat with
      | .error e => .error e
      | .ok s2 =>
        let tgt      := AccountAddress.ofUInt256 toArg
        let callee   := s2.accountMap tgt
        if s2.executionEnv.depth ≥ 1024 then
          .ok ({ s2 with returnData := .empty }.replaceStackAndIncrPC
                 (UInt256.ofNat 0 :: rest))
        else
          let forwarded := Gas.forwardGas s.fork s2.gasAvailable gasArg.toNat
          if hfw : forwarded ≤ s2.gasAvailable then
            let s3       := s2.consumeGas forwarded hfw
            let calldata := MachineState.readPadded s3.memory argsOff.toNat argsLen.toNat
            -- STATICCALL: no stipend (no value), so `childGas = forwarded`.
            -- Precompile dispatch (if `tgt` is in `0x01..0x09`) is the
            -- generic precompile arm's job at the top of the next
            -- iteration.
            .ok (s3.enterCallFor .StaticCall rest tgt ⟨0⟩ calldata
                   callee.code forwarded retOff.toNat retLen.toNat)
          else .error .OutOfGas
    | _ => underflow
  | .SELFDESTRUCT => match s.stack with
    | beneficiary :: _ =>
      -- Static-mode rejects unconditionally: SELFDESTRUCT mutates state
      -- (balance transfer + scheduled deletion) so it cannot run in a
      -- static frame even if the beneficiary equals self.
      if ¬ s.executionEnv.permitStateMutation then static
      else
        -- `s'` already paid the base fee (`G_selfdestruct = 5000`). Charge
        -- the new-account surcharge: 25000 iff the beneficiary is empty
        -- AND self carries balance (= the transfer brings a fresh account
        -- into existence). Then commit the transfer + halt via
        -- `State.selfDestructTo`.
        let benAddr := AccountAddress.ofUInt256 beneficiary
        let ben     := s.accountMap benAddr
        let selfBal : Bool := (s.accountMap s.executionEnv.address).balance.toNat != 0
        let surcharge := Gas.selfDestructSurcharge s.fork ben.isEmpty selfBal
        if hsc : surcharge ≤ s'.gasAvailable then
          .ok ((s'.consumeGas surcharge hsc).selfDestructTo benAddr)
        else .error .OutOfGas
    | _ => underflow
  | .CREATE => match s.stack with
    | value :: offset :: size :: rest =>
      if ¬ s.executionEnv.permitStateMutation then static
      else
        match chargeMem s' offset.toNat size.toNat with
        | .error e => .error e
        | .ok s2 =>
          if s2.executionEnv.depth ≥ 1024 ∨
              (s2.accountMap s2.executionEnv.address).balance < value then
            .ok ({ s2 with returnData := .empty }.replaceStackAndIncrPC
                   (UInt256.ofNat 0 :: rest))
          else
            -- Derive `newAddr` via `createAddress`. The encoder is
            -- `Option`-typed: it returns `none` only when the payload
            -- would exceed `2^64` bytes, which is unreachable here
            -- ([20-byte address, ≤32-byte nonce] tops out at ~55
            -- bytes). We map a `none` to `InvalidInstruction` for
            -- completeness, but a gas-bounded execution never reaches it.
            match createAddress s2.executionEnv.address
                    (s2.accountMap s2.executionEnv.address).nonce.toNat with
            | none => .error .InvalidInstruction
            | some newAddr =>
              -- EIP-150 forwards 63/64 of the post-cost gas to the
              -- child; that amount is taken from the caller *regardless
              -- of whether creation succeeds or collides*, since on
              -- collision the child returns zero gas. Hence we consume
              -- `forwarded` before splitting on the collision check.
              if hfw : Gas.allButOneSixtyFourth s.fork s2.gasAvailable ≤ s2.gasAvailable then
                let forwarded := Gas.allButOneSixtyFourth s.fork s2.gasAvailable
                let s3 := s2.consumeGas forwarded hfw
                -- Address-collision check: if `newAddr` already hosts code
                -- or has nonce > 0 the create *fails* with the caller's
                -- nonce still bumped (push 0, no transfer, no frame).
                -- Discriminated via a `Bool` (`Account.isContract`) so
                -- the Equiv proof can split cleanly on the match.
                match (s3.accountMap newAddr).isContract with
                | true =>
                  let caller    := s3.executionEnv.address
                  let callerAcc := s3.accountMap caller
                  let σ' := s3.accountMap.set caller
                              { callerAcc with nonce := callerAcc.nonce + ⟨1⟩ }
                  .ok ({ s3 with accountMap := σ', returnData := .empty
                       }.replaceStackAndIncrPC (UInt256.ofNat 0 :: rest))
                | false =>
                  .ok (s3.enterCreate rest newAddr value
                         (MachineState.readPadded s3.memory offset.toNat size.toNat)
                         forwarded)
              else .error .OutOfGas
    | _ => underflow
  | .CREATE2 => match s.stack with
    | value :: offset :: size :: salt :: rest =>
      if ¬ s.executionEnv.permitStateMutation then static
      else
        match chargeMem s' offset.toNat size.toNat with
        | .error e => .error e
        | .ok s2 =>
          let hashCost := Gas.create2HashCost size.toNat
          if hh : hashCost ≤ s2.gasAvailable then
            let s2' := s2.consumeGas hashCost hh
            if s2'.executionEnv.depth ≥ 1024 ∨
                (s2'.accountMap s2'.executionEnv.address).balance < value then
              .ok ({ s2' with returnData := .empty }.replaceStackAndIncrPC
                     (UInt256.ofNat 0 :: rest))
            else
              -- See CREATE above: forward gas is consumed even on collision.
              if hfw : Gas.allButOneSixtyFourth s.fork s2'.gasAvailable ≤ s2'.gasAvailable then
                let forwarded := Gas.allButOneSixtyFourth s.fork s2'.gasAvailable
                let s3 := s2'.consumeGas forwarded hfw
                match (s3.accountMap (create2Address s3.executionEnv.address salt
                         (MachineState.readPadded s3.memory
                            offset.toNat size.toNat))).isContract with
                | true =>
                  let caller    := s3.executionEnv.address
                  let callerAcc := s3.accountMap caller
                  let σ' := s3.accountMap.set caller
                              { callerAcc with nonce := callerAcc.nonce + ⟨1⟩ }
                  .ok ({ s3 with accountMap := σ', returnData := .empty
                       }.replaceStackAndIncrPC (UInt256.ofNat 0 :: rest))
                | false =>
                  let initCode := MachineState.readPadded s3.memory offset.toNat size.toNat
                  .ok (s3.enterCreate rest
                         (create2Address s3.executionEnv.address salt initCode)
                         value initCode forwarded)
              else .error .OutOfGas
          else .error .OutOfGas
    | _ => underflow

end stepF

----------------------------------------------------------------------------
-- Top-level dispatcher.
----------------------------------------------------------------------------

/-- Top-level executable shadow — halt/decode/gas dispatch into per-group
    helpers — in *Except-returning* form. This is the version covered by
    `stepFE_sound` in `Equiv.lean`; the public `stepF` below wraps it
    into a total `State → State` shape by folding in-frame exceptions
    into `halt := .Exception e` so callers can drive a loop purely off
    `isDone` without case-splitting on the result. -/
def stepFE (s : State) : Except ExecutionException State := Id.run do
  match s.halt with
  | .Running =>
    -- YP §9 precompile dispatch.  If the *currently-executing frame*
    -- borrows code from a precompile address (per the per-fork
    -- predicate `Precompile.isPrecompile`), invoke the precompile in
    -- place of decoding `s.code`.  This single arm covers every
    -- entry path: `CALL` / `STATICCALL` (where `codeAddr = address`),
    -- `CALLCODE` / `DELEGATECALL` (where `codeAddr` is the
    -- borrowed-from address ≠ `address`), and a transaction whose
    -- `to` is itself a precompile (where `buildInitState` sets
    -- `codeAddr := tx.recipient`).
    match h_isPrec : Precompile.isPrecompile s.executionEnv.fork
                       s.executionEnv.codeAddr with
    | true =>
      match Precompile.run s.executionEnv.fork s.executionEnv.codeAddr
              s.executionEnv.calldata s.gasAvailable h_isPrec with
      | .success out gasUsed =>
        .ok { s with
                halt         := .Returned
                hReturn      := out
                gasAvailable := s.gasAvailable - gasUsed }
      | .outOfGas =>
        .ok { s with
                halt         := .Exception .OutOfGas
                hReturn      := ByteArray.empty
                gasAvailable := 0 }
    | false =>
    match s.decoded with
    | none => .error .InvalidInstruction
    | some (op, argOpt) =>
      -- Enforce the YP's 1024-deep stack cap before consuming gas: an op
      -- that would leave more than 1024 items on the stack
      -- (`len(stack) - δ_pop + α_push > 1024`) halts with `StackOverflow`
      -- without spending its base cost. The underflow side (`len(stack) <
      -- δ_pop`) is still caught inside each per-group helper, where the
      -- pattern-match on `stack` falls through to the `underflow` arm.
      if s.stack.length + op.pushArity > 1024 + op.popArity then
        .error .StackOverflow
      else
      let cost := Gas.baseCost s.fork op
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
  | _ =>
    -- The active frame has halted. If suspended callers remain, resume the
    -- top one (this is the executable mirror of the `StepReturn.callReturn*`
    -- rules); otherwise the whole execution is done — there is no
    -- transition, so return `s` unchanged (`stepF` becomes the identity
    -- on done states, which means `Tx.run`-style loops just need
    -- `isDone` as their exit condition).
    match s.callStack with
    | []        => .ok s
    | f :: rest => .ok (s.resumeByHalt f rest)

/-- Public small-step: a *total* `State → State` shadow of `stepFE`.

    The only adapter on top of `stepFE` is folding in-frame exceptions
    into `halt := .Exception e` on the active frame. The next call to
    `stepF` then sees a halted state with a non-empty call stack and
    routes through `resumeByHalt` — i.e. exceptions now flow through
    the exact same path as `.Reverted` halts. The done-state-identity
    behaviour falls out of `stepFE` itself (which returns `.ok s` when
    the active frame is halted and the call stack is empty), so
    drivers can loop `s := stepF s` until `isDone` with no case-split
    on the result. -/
@[inline] def stepF (s : State) : State :=
  match stepFE s with
  | .ok s'  => s'
  | .error e => { s with halt := .Exception e }

end EVM
end EvmSemantics
