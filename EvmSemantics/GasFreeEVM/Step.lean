module

public import EvmSemantics.EVM.Step

/-!
`EvmSemantics.GasFreeEVM.Step` — the **gas-free** parallel to
`EvmSemantics.EVM.Step`.

Three inductives mirror those in `EVM/Step.lean`:

* **`StepRunning`** carries the per-opcode logic with the same shape as
  `EVM.StepRunning`, but with every `h_gas` / `h_mem` / `h_dyn_gas`
  premise dropped and the `consumeGas` / `consumeMemExp` calls in the
  output replaced by `s` (gas) or `State.advanceMem` /
  `State.advanceMem2` (active-words advance, no gas).
* **`StepReturn`** holds the three `callReturn*` resume rules, with the
  same shape as `EVM.StepReturn`.
* **`Step`** is the wrapper, parallel to `EVM.Step.running` /
  `EVM.Step.returning`.

Most state helpers (`consumeGas`, `consumeMemExp`, `decodedOp`, `fork`,
…) live in `EVM/Step.lean`'s `State` namespace. The two gas-free
analogues `State.advanceMem` / `advanceMem2` (which advance the
active-words mark *without* charging gas) are defined here — they're
only needed by `StepRunning`'s memory-touching constructors.

The gas-aware `EVM.Step` is the source of truth; this module is its
image under the projection that erases gas accounting.
`GasFreeEVM/Equiv.lean` is intended to close the equivalence theorem.
-/

@[expose] public section

open EvmSemantics.EVM

namespace EvmSemantics.EVM.State

/-- Gas-free analogue of `consumeMemExp`: advance the active-words
    high-water mark for `[offset, offset+sz)` without charging the
    expansion gas. -/
def advanceMem (s : State) (offset sz : Nat) : State :=
  { s with activeWords :=
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat offset sz) }

/-- Two-range gas-free analogue of `consumeMemExp2`. -/
def advanceMem2 (s : State) (off1 sz1 off2 sz2 : Nat) : State :=
  let new1 := MachineState.activeWordsAfter s.activeWords.toNat off1 sz1
  let new2 := MachineState.activeWordsAfter new1 off2 sz2
  { s with activeWords := UInt256.ofNat new2 }

end EvmSemantics.EVM.State

namespace EvmSemantics.GasFreeEVM


/-- Per-opcode small-step logic. One constructor per opcode for the
    success path, plus generic exception constructors at the bottom.
    Constructors do **not** carry `h_running : s.halt = .Running`; the
    running guard lives on the wrapper `Step.running`. See the file
    docstring for the overall split. -/
inductive StepRunning : State → State → Prop

  ----------------------------------------------------------------------------
  -- Stop, arithmetic.
  ----------------------------------------------------------------------------

  /-- ADD: pop `a`, `b`; push `a + b`. -/
  | add (s : State) (a b : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .ADD)
        (h_stack   : s.stack = a :: b :: rest)
      : StepRunning s (s.replaceStackAndIncrPC
                  ((a + b) :: rest))

  /-- MUL: pop `a`, `b`; push `a * b`. -/
  | mul (s : State) (a b : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .MUL)
        (h_stack   : s.stack = a :: b :: rest)
      : StepRunning s (s.replaceStackAndIncrPC
                  ((a * b) :: rest))

  /-- SUB: pop `a`, `b`; push `a - b`. -/
  | sub (s : State) (a b : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .SUB)
        (h_stack   : s.stack = a :: b :: rest)
      : StepRunning s (s.replaceStackAndIncrPC
                  ((a - b) :: rest))

  /-- DIV: pop `a`, `b`; push `a / b` (0 if `b = 0`). -/
  | div (s : State) (a b : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .DIV)
        (h_stack   : s.stack = a :: b :: rest)
      : StepRunning s (s.replaceStackAndIncrPC
                  ((a / b) :: rest))

  /-- SDIV: signed division. -/
  | sdiv (s : State) (a b : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .SDIV)
        (h_stack   : s.stack = a :: b :: rest)
      : StepRunning s (s.replaceStackAndIncrPC
                  (UInt256.sdiv a b :: rest))

  /-- MOD: pop `a`, `b`; push `a % b` (0 if `b = 0`). -/
  | mod (s : State) (a b : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .MOD)
        (h_stack   : s.stack = a :: b :: rest)
      : StepRunning s (s.replaceStackAndIncrPC
                  ((a % b) :: rest))

  /-- SMOD: signed modulo. -/
  | smod (s : State) (a b : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .SMOD)
        (h_stack   : s.stack = a :: b :: rest)
      : StepRunning s (s.replaceStackAndIncrPC
                  (UInt256.smod a b :: rest))

  /-- ADDMOD: pop `a`, `b`, `n`; push `(a + b) mod n`. -/
  | addmod (s : State) (a b n : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .ADDMOD)
        (h_stack   : s.stack = a :: b :: n :: rest)
      : StepRunning s (s.replaceStackAndIncrPC
                  (UInt256.addMod a b n :: rest))

  /-- MULMOD: pop `a`, `b`, `n`; push `(a * b) mod n`. -/
  | mulmod (s : State) (a b n : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .MULMOD)
        (h_stack   : s.stack = a :: b :: n :: rest)
      : StepRunning s (s.replaceStackAndIncrPC
                  (UInt256.mulMod a b n :: rest))

  /-- EXP: pop `a`, `b`; push `a ^ b mod 2^256`. -/
  | exp (s : State) (a b : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .EXP)
        (h_stack   : s.stack = a :: b :: rest)
      : StepRunning s (s.replaceStackAndIncrPC (UInt256.exp a b :: rest))

  /-- SIGNEXTEND: pop `b`, `x`; sign-extend `x` from byte index `b`. -/
  | signextend (s : State) (b x : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .SIGNEXTEND)
        (h_stack   : s.stack = b :: x :: rest)
      : StepRunning s (s.replaceStackAndIncrPC
                  (UInt256.signExtend b x :: rest))

  ----------------------------------------------------------------------------
  -- Comparison & bitwise.
  ----------------------------------------------------------------------------

  | lt (s : State) (a b : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .LT)
        (h_stack   : s.stack = a :: b :: rest)
      : StepRunning s (s.replaceStackAndIncrPC
                  (UInt256.lt a b :: rest))

  | gt (s : State) (a b : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .GT)
        (h_stack   : s.stack = a :: b :: rest)
      : StepRunning s (s.replaceStackAndIncrPC
                  (UInt256.gt a b :: rest))

  | slt (s : State) (a b : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .SLT)
        (h_stack   : s.stack = a :: b :: rest)
      : StepRunning s (s.replaceStackAndIncrPC
                  (UInt256.slt a b :: rest))

  | sgt (s : State) (a b : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .SGT)
        (h_stack   : s.stack = a :: b :: rest)
      : StepRunning s (s.replaceStackAndIncrPC
                  (UInt256.sgt a b :: rest))

  | eq (s : State) (a b : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .EQ)
        (h_stack   : s.stack = a :: b :: rest)
      : StepRunning s (s.replaceStackAndIncrPC
                  (UInt256.eq a b :: rest))

  | iszero (s : State) (a : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .ISZERO)
        (h_stack   : s.stack = a :: rest)
      : StepRunning s (s.replaceStackAndIncrPC
                  (UInt256.isZero a :: rest))

  | and (s : State) (a b : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .AND)
        (h_stack   : s.stack = a :: b :: rest)
      : StepRunning s (s.replaceStackAndIncrPC
                  (UInt256.land a b :: rest))

  | or (s : State) (a b : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .OR)
        (h_stack   : s.stack = a :: b :: rest)
      : StepRunning s (s.replaceStackAndIncrPC
                  (UInt256.lor a b :: rest))

  | xor_ (s : State) (a b : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .XOR)
        (h_stack   : s.stack = a :: b :: rest)
      : StepRunning s (s.replaceStackAndIncrPC
                  (UInt256.xor a b :: rest))

  | not (s : State) (a : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .NOT)
        (h_stack   : s.stack = a :: rest)
      : StepRunning s (s.replaceStackAndIncrPC
                  (UInt256.lnot a :: rest))

  | byte_ (s : State) (i x : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .BYTE)
        (h_stack   : s.stack = i :: x :: rest)
      : StepRunning s (s.replaceStackAndIncrPC
                  (UInt256.byteAt i x :: rest))

  | shl (s : State) (shift v : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .SHL)
        (h_stack   : s.stack = shift :: v :: rest)
      : StepRunning s (s.replaceStackAndIncrPC
                  (UInt256.shiftLeft v shift :: rest))

  | shr (s : State) (shift v : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .SHR)
        (h_stack   : s.stack = shift :: v :: rest)
      : StepRunning s (s.replaceStackAndIncrPC
                  (UInt256.shiftRight v shift :: rest))

  | sar (s : State) (shift v : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .SAR)
        (h_stack   : s.stack = shift :: v :: rest)
      : StepRunning s (s.replaceStackAndIncrPC
                  (UInt256.sar v shift :: rest))

  ----------------------------------------------------------------------------
  -- KECCAK256.
  ----------------------------------------------------------------------------

  /-- KECCAK256: pop offset, size; push hash of memory[offset..offset+size]. -/
  | keccak256 (s : State) (offset size : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .KECCAK256)
        (h_stack   : s.stack = offset :: size :: rest)
      : StepRunning s
          (let bytes := MachineState.readPadded s.memory offset.toNat size.toNat
           (s.advanceMem offset.toNat size.toNat).replaceStackAndIncrPC
             (EvmSemantics.keccak256 bytes :: rest))

  ----------------------------------------------------------------------------
  -- Environment reads.
  ----------------------------------------------------------------------------

  | address (s : State)
        (h_op      : s.decodedOp = some .ADDRESS)
      : StepRunning s (s.replaceStackAndIncrPC
                  (s.executionEnv.codeOwner.toUInt256 :: s.stack))

  | balance (s : State) (addr : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .BALANCE)
        (h_stack   : s.stack = addr :: rest)
      : StepRunning s (s.replaceStackAndIncrPC
                  ((s.accountMap (AccountAddress.ofUInt256 addr)).balance :: rest))

  | origin (s : State)
        (h_op      : s.decodedOp = some .ORIGIN)
      : StepRunning s (s.replaceStackAndIncrPC
                  (s.executionEnv.sender.toUInt256 :: s.stack))

  | caller (s : State)
        (h_op      : s.decodedOp = some .CALLER)
      : StepRunning s (s.replaceStackAndIncrPC
                  (s.executionEnv.source.toUInt256 :: s.stack))

  | callvalue (s : State)
        (h_op      : s.decodedOp = some .CALLVALUE)
      : StepRunning s (s.replaceStackAndIncrPC
                  (s.executionEnv.weiValue :: s.stack))

  /-- CALLDATALOAD: pop `i`; push 32 bytes of calldata starting at `i`,
      zero-padded if past the end. -/
  | calldataload (s : State) (i : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .CALLDATALOAD)
        (h_stack   : s.stack = i :: rest)
      : StepRunning s
          (let bs := MachineState.readPadded s.executionEnv.calldata i.toNat 32
           let word : Nat := bs.toList.foldl (fun acc b => acc * 256 + b.toNat) 0
           s.replaceStackAndIncrPC
             (UInt256.ofNat word :: rest))

  | calldatasize (s : State)
        (h_op      : s.decodedOp = some .CALLDATASIZE)
      : StepRunning s
          (s.replaceStackAndIncrPC
            (UInt256.ofNat s.executionEnv.calldata.size :: s.stack))

  /-- CALLDATACOPY: pop destOffset, srcOffset, size; copy calldata to memory. -/
  | calldatacopy (s : State) (destOff srcOff sz : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .CALLDATACOPY)
        (h_stack   : s.stack = destOff :: srcOff :: sz :: rest)
      : StepRunning s
          (let bytes := MachineState.readPadded s.executionEnv.calldata srcOff.toNat sz.toNat
           let s'' := s.advanceMem destOff.toNat sz.toNat
           let μ' : MachineState :=
             { s''.toMachineState with
                 memory := MachineState.writeBytes s.memory bytes destOff.toNat }
           { s'' with toMachineState := μ' }.replaceStackAndIncrPC rest)

  | codesize (s : State)
        (h_op      : s.decodedOp = some .CODESIZE)
      : StepRunning s (s.replaceStackAndIncrPC
                  (UInt256.ofNat s.executionEnv.code.size :: s.stack))

  /-- CODECOPY: pop destOffset, srcOffset, size; copy current code to memory. -/
  | codecopy (s : State) (destOff srcOff sz : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .CODECOPY)
        (h_stack   : s.stack = destOff :: srcOff :: sz :: rest)
      : StepRunning s
          (let bytes := MachineState.readPadded s.executionEnv.code srcOff.toNat sz.toNat
           let s'' := s.advanceMem destOff.toNat sz.toNat
           let μ' : MachineState :=
             { s''.toMachineState with
                 memory := MachineState.writeBytes s.memory bytes destOff.toNat }
           { s'' with toMachineState := μ' }.replaceStackAndIncrPC rest)

  | gasprice (s : State)
        (h_op      : s.decodedOp = some .GASPRICE)
      : StepRunning s (s.replaceStackAndIncrPC
                  (s.executionEnv.gasPrice :: s.stack))

  | extcodesize (s : State) (addr : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .EXTCODESIZE)
        (h_stack   : s.stack = addr :: rest)
      : StepRunning s (s.replaceStackAndIncrPC
                  (UInt256.ofNat (s.accountMap (AccountAddress.ofUInt256 addr)).code.size :: rest))

  /-- EXTCODECOPY: pop addr, destOffset, srcOffset, size; copy external
      code bytes to memory. -/
  | extcodecopy (s : State) (addr destOff srcOff sz : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .EXTCODECOPY)
        (h_stack   : s.stack = addr :: destOff :: srcOff :: sz :: rest)
      : StepRunning s
          (let extCode := (s.accountMap (AccountAddress.ofUInt256 addr)).code
           let bytes := MachineState.readPadded extCode srcOff.toNat sz.toNat
           let s'' := s.advanceMem destOff.toNat sz.toNat
           let μ' : MachineState :=
             { s''.toMachineState with
                 memory := MachineState.writeBytes s.memory bytes destOff.toNat }
           { s'' with toMachineState := μ' }.replaceStackAndIncrPC rest)

  | returndatasize (s : State)
        (h_op      : s.decodedOp = some .RETURNDATASIZE)
      : StepRunning s
          (s.replaceStackAndIncrPC
            (UInt256.ofNat s.returnData.size :: s.stack))

  /-- RETURNDATACOPY: pop destOffset, srcOffset, size; copy returndata to memory.
      Out-of-bounds reads raise `InvalidMemoryAccess` (handled in Phase 5). -/
  | returndatacopy (s : State) (destOff srcOff sz : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .RETURNDATACOPY)
        (h_stack   : s.stack = destOff :: srcOff :: sz :: rest)
        (h_inbounds : srcOff.toNat + sz.toNat ≤ s.returnData.size)
      : StepRunning s
          (let bytes := MachineState.readPadded s.returnData srcOff.toNat sz.toNat
           let s'' := s.advanceMem destOff.toNat sz.toNat
           let μ' : MachineState :=
             { s''.toMachineState with
                 memory := MachineState.writeBytes s.memory bytes destOff.toNat }
           { s'' with toMachineState := μ' }.replaceStackAndIncrPC rest)

  | extcodehash (s : State) (addr : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .EXTCODEHASH)
        (h_stack   : s.stack = addr :: rest)
      : StepRunning s (s.replaceStackAndIncrPC
                  ((s.accountMap (AccountAddress.ofUInt256 addr)).codeHash :: rest))

  ----------------------------------------------------------------------------
  -- Block-context reads.
  ----------------------------------------------------------------------------

  | blockhash (s : State) (n : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .BLOCKHASH)
        (h_stack   : s.stack = n :: rest)
      : StepRunning s (s.replaceStackAndIncrPC
                  (s.executionEnv.header.blockHash n :: rest))

  | coinbase (s : State)
        (h_op      : s.decodedOp = some .COINBASE)
      : StepRunning s (s.replaceStackAndIncrPC
                  (s.executionEnv.header.coinbase.toUInt256 :: s.stack))

  | timestamp (s : State)
        (h_op      : s.decodedOp = some .TIMESTAMP)
      : StepRunning s (s.replaceStackAndIncrPC
                  (s.executionEnv.header.timestamp :: s.stack))

  | number (s : State)
        (h_op      : s.decodedOp = some .NUMBER)
      : StepRunning s (s.replaceStackAndIncrPC
                  (s.executionEnv.header.number :: s.stack))

  | prevrandao (s : State)
        (h_op      : s.decodedOp = some .PREVRANDAO)
      : StepRunning s (s.replaceStackAndIncrPC
                  (s.executionEnv.header.prevRandao :: s.stack))

  | gaslimit (s : State)
        (h_op      : s.decodedOp = some .GASLIMIT)
      : StepRunning s (s.replaceStackAndIncrPC
                  (s.executionEnv.header.gasLimit :: s.stack))

  | chainid (s : State)
        (h_op      : s.decodedOp = some .CHAINID)
      : StepRunning s (s.replaceStackAndIncrPC
                  (s.executionEnv.header.chainId :: s.stack))

  | selfbalance (s : State)
        (h_op      : s.decodedOp = some .SELFBALANCE)
      : StepRunning s (s.replaceStackAndIncrPC
                  ((s.accountMap s.executionEnv.codeOwner).balance :: s.stack))

  | basefee (s : State)
        (h_op      : s.decodedOp = some .BASEFEE)
      : StepRunning s (s.replaceStackAndIncrPC
                  (s.executionEnv.header.baseFeePerGas :: s.stack))

  | blobhash (s : State) (i : UInt256) (rest : List UInt256) (h : UInt256)
        (h_op      : s.decodedOp = some .BLOBHASH)
        (h_stack   : s.stack = i :: rest)
        (h_get     : s.executionEnv.blobVersionedHashes[i.toNat]? = some h)
      : StepRunning s (s.replaceStackAndIncrPC
                  (h :: rest))

  /-- BLOBHASH when index is out of range — push 0. -/
  | blobhash_oob (s : State) (i : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .BLOBHASH)
        (h_stack   : s.stack = i :: rest)
        (h_oob     : s.executionEnv.blobVersionedHashes[i.toNat]? = none)
      : StepRunning s (s.replaceStackAndIncrPC
                  (⟨0⟩ :: rest))

  | blobbasefee (s : State)
        (h_op      : s.decodedOp = some .BLOBBASEFEE)
      : StepRunning s (s.replaceStackAndIncrPC
                  (s.executionEnv.header.blobBaseFee :: s.stack))

  ----------------------------------------------------------------------------
  -- Stack manipulation: POP, PUSHk, DUPn, SWAPn.
  ----------------------------------------------------------------------------

  | pop (s : State) (a : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .POP)
        (h_stack   : s.stack = a :: rest)
      : StepRunning s (s.replaceStackAndIncrPC
                  rest)

  /-- PUSH0: push `0`. -/
  | push0 (s : State)
        (h_op      : s.decodedOp = some (.Push ⟨0, by decide⟩))
      : StepRunning s
          (s.replaceStackAndIncrPC
              (⟨0⟩ :: s.stack))

  /-- PUSHk (k ≥ 1): push the immediate-decoded value `data`.

      `immWidth` is the width in bytes recorded in the decoded argument
      tuple; PC advances by `immWidth + 1` (opcode byte + `immWidth`
      immediate bytes). The decoder guarantees `immWidth = k.val` but
      that invariant is not enforced at the relation level: keeping the
      two as separate parameters avoids needing a decoder-invariant
      lemma in the soundness proof. -/
  | pushN (s : State) (k : Fin 33) (data : UInt256) (immWidth : Nat)
        (h_k_pos   : 0 < k.val)
        (h_op      : s.decoded = some (.Push ⟨k, k.isLt⟩, some (data, immWidth)))
      : StepRunning s
          (s.replaceStackAndIncrPC
            (data :: s.stack) (pcΔ := immWidth + 1))

  /-- DUPn: copy `stack[n]` (0-indexed from top) to the top. -/
  | dup (s : State) (n : Fin 16) (v : UInt256)
        (h_op      : s.decodedOp = some (.Dup ⟨n⟩))
        (h_get     : s.stack[n.val]? = some v)
      : StepRunning s
          (s.replaceStackAndIncrPC
              (v :: s.stack))

  /-- SWAPn: swap top with `stack[n+1]`. -/
  | swap (s : State) (n : Fin 16) (stk' : List UInt256)
        (h_op      : s.decodedOp = some (.Swap ⟨n⟩))
        (h_swap    : s.stack.exchange 0 (n.val + 1) = some stk')
      : StepRunning s
          (s.replaceStackAndIncrPC stk')

  ----------------------------------------------------------------------------
  -- Memory.
  ----------------------------------------------------------------------------

  /-- MLOAD: pop offset; push the 32-byte word at memory[offset]. -/
  | mload (s : State) (offset : UInt256) (rest : List UInt256)
        (v : UInt256) (μ' : MachineState)
        (h_op      : s.decodedOp = some .MLOAD)
        (h_stack   : s.stack = offset :: rest)
        (h_load    : MachineState.mload
                       (s.advanceMem offset.toNat 32).toMachineState offset = (v, μ'))
      : StepRunning s
          ({ (s.advanceMem offset.toNat 32) with toMachineState := μ' }
            |>.replaceStackAndIncrPC (v :: rest))

  /-- MSTORE: pop offset, value; write `value` as 32 bytes at memory[offset]. -/
  | mstore (s : State) (offset value : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .MSTORE)
        (h_stack   : s.stack = offset :: value :: rest)
      : StepRunning s
          (let s'' := s.advanceMem offset.toNat 32
           let μ' := MachineState.mstore s''.toMachineState offset value
           { s'' with toMachineState := μ' }.replaceStackAndIncrPC rest)

  /-- MSTORE8: pop offset, value; write the low byte of `value` at memory[offset]. -/
  | mstore8 (s : State) (offset value : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .MSTORE8)
        (h_stack   : s.stack = offset :: value :: rest)
      : StepRunning s
          (let s'' := s.advanceMem offset.toNat 1
           let μ' := MachineState.mstore8 s''.toMachineState offset value
           { s'' with toMachineState := μ' }.replaceStackAndIncrPC rest)

  | msize (s : State)
        (h_op      : s.decodedOp = some .MSIZE)
      : StepRunning s (s.replaceStackAndIncrPC
                  (MachineState.msize s.toMachineState :: s.stack))

  /-- MCOPY: pop destOffset, srcOffset, size; copy memory[src..src+sz] to dest.
      Touches *both* the read range `[srcOff, srcOff+sz)` and the write range
      `[destOff, destOff+sz)`; expansion gas is charged for their union. -/
  | mcopy (s : State) (destOff srcOff sz : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .MCOPY)
        (h_stack   : s.stack = destOff :: srcOff :: sz :: rest)
      : StepRunning s
          (let s'' := s.advanceMem2 destOff.toNat sz.toNat srcOff.toNat sz.toNat
           let μ' := MachineState.mcopy s''.toMachineState destOff srcOff sz
           { s'' with toMachineState := μ' }.replaceStackAndIncrPC rest)

  ----------------------------------------------------------------------------
  -- Storage (persistent and transient).
  ----------------------------------------------------------------------------

  /-- SLOAD: pop key; push storage[key] from the executing contract. -/
  | sload (s : State) (key : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .SLOAD)
        (h_stack   : s.stack = key :: rest)
      : StepRunning s (s.replaceStackAndIncrPC
                  (((s.accountMap s.executionEnv.codeOwner).storage key) :: rest))

  /-- SSTORE: pop key, value; write storage[key] := value. Requires
      static-mode permission. -/
  | sstore (s : State) (key value : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .SSTORE)
        (h_perm    : s.executionEnv.permitStateMutation = true)
        (h_stack   : s.stack = key :: value :: rest)
      : StepRunning s
          (let addr := s.executionEnv.codeOwner
           let acc  := s.accountMap addr
           let acc' := { acc with storage := acc.storage.set key value }
           let σ'   := s.accountMap.set addr acc'
           { s with accountMap := σ' } |>.replaceStackAndIncrPC rest)

  /-- TLOAD: like SLOAD but reads from transient storage. -/
  | tload (s : State) (key : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .TLOAD)
        (h_stack   : s.stack = key :: rest)
      : StepRunning s (s.replaceStackAndIncrPC
                  (((s.accountMap s.executionEnv.codeOwner).tstorage key) :: rest))

  /-- TSTORE: like SSTORE but writes to transient storage. -/
  | tstore (s : State) (key value : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .TSTORE)
        (h_perm    : s.executionEnv.permitStateMutation = true)
        (h_stack   : s.stack = key :: value :: rest)
      : StepRunning s
          (let addr := s.executionEnv.codeOwner
           let acc  := s.accountMap addr
           let acc' := { acc with tstorage := acc.tstorage.set key value }
           let σ'   := s.accountMap.set addr acc'
           { s with accountMap := σ' }
             |>.replaceStackAndIncrPC rest)

  ----------------------------------------------------------------------------
  -- Control flow: JUMP, JUMPI, JUMPDEST, PC, GAS.
  ----------------------------------------------------------------------------

  /-- JUMP: pop destination; set `pc := dest` if the destination is a
      `JUMPDEST` *as an instruction boundary* — a `0x5b` byte sitting inside
      a PUSH immediate is rejected by the jumpdest analysis. -/
  | jump (s : State) (dest : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .JUMP)
        (h_stack   : s.stack = dest :: rest)
        (h_valid   : Decode.isValidJumpDest s.executionEnv.code dest.toNat = true)
      : StepRunning s
          { s with pc := dest, stack := rest }

  /-- JUMPI (taken): pop dest, cond; if `cond ≠ 0` and dest is a valid
      `JUMPDEST` (instruction boundary, not push-data), set `pc := dest`. -/
  | jumpi_taken (s : State) (dest cond : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .JUMPI)
        (h_stack   : s.stack = dest :: cond :: rest)
        (h_cond    : UInt256.isTrue cond)
        (h_valid   : Decode.isValidJumpDest s.executionEnv.code dest.toNat = true)
      : StepRunning s
          { s with pc := dest, stack := rest }

  /-- JUMPI (not taken): pop dest, cond; if `cond = 0`, fall through to `pc + 1`. -/
  | jumpi_notTaken (s : State) (dest cond : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .JUMPI)
        (h_stack   : s.stack = dest :: cond :: rest)
        (h_cond    : ¬ UInt256.isTrue cond)
      : StepRunning s (s.replaceStackAndIncrPC
                  rest)

  | pc (s : State)
        (h_op      : s.decodedOp = some .PC)
      : StepRunning s (s.replaceStackAndIncrPC
                  (s.pc :: s.stack))

  /-- GAS pushes the remaining gas. In the gas-aware relation this is the
      gas *after* the opcode's own cost is deducted; in the gas-free version
      we simply push `s.gasAvailable`, whose value is unconstrained by NG
      semantics (any caller that re-injects gas can pick a budget that
      threads through the GAS instruction however they like). -/
  | gas (s : State)
        (h_op      : s.decodedOp = some .GAS)
      : StepRunning s
          (s.replaceStackAndIncrPC (UInt256.ofNat s.gasAvailable :: s.stack))

  | jumpdest (s : State)
        (h_op      : s.decodedOp = some .JUMPDEST)
      : StepRunning s (s.incrPC)

  ----------------------------------------------------------------------------
  -- Halts: STOP, RETURN, REVERT.
  ----------------------------------------------------------------------------

  | stop (s : State)
        (h_op      : s.decodedOp = some .STOP)
      : StepRunning s { s with halt := .Success, hReturn := .empty }

  | return_ (s : State) (offset size : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .RETURN)
        (h_stack   : s.stack = offset :: size :: rest)
      : StepRunning s
          (let bs := MachineState.readPadded s.memory offset.toNat size.toNat
           let s'' := s.advanceMem offset.toNat size.toNat
           { s'' with halt := .Returned, hReturn := bs, stack := rest })

  | revert (s : State) (offset size : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .REVERT)
        (h_stack   : s.stack = offset :: size :: rest)
      : StepRunning s
          (let bs := MachineState.readPadded s.memory offset.toNat size.toNat
           let s'' := s.advanceMem offset.toNat size.toNat
           { s'' with halt := .Reverted, hReturn := bs, stack := rest })

  ----------------------------------------------------------------------------
  -- CALL. The intermediate gas-charged states `s' s2 s3 s4` are introduced as
  -- explicit parameters tied down by equation hypotheses (rather than inlined),
  -- so each later hypothesis can refer to the previous state by name. This
  -- mirrors `stepF.system`'s `.CALL` arm step-for-step.
  ----------------------------------------------------------------------------

  /-- CALL with `value ≠ 0` attempted while the active frame disallows state
      mutation (static mode). Halts the frame with `StaticModeViolation` *before*
      paying any of the call's gas, mirroring `stepF.system`'s early static
      check. A zero-value CALL is still permitted in static mode. -/
  | callStatic (s : State)
        (gasArg toArg value argsOff argsLen retOff retLen : UInt256)
        (rest : List UInt256)
        (h_op       : s.decodedOp = some .CALL)
        (h_stack    : s.stack =
                        gasArg :: toArg :: value :: argsOff :: argsLen :: retOff :: retLen :: rest)
        (h_perm     : s.executionEnv.permitStateMutation = false)
        (h_value    : value.toNat ≠ 0)
      : StepRunning s (s.haltWith .StaticModeViolation)

  /-- CALL (taken): pop the 7 args; check depth limit and caller balance;
      transfer `value`; and enter the callee frame. In NG semantics the gas
      bookkeeping (base, memory expansion, surcharge, 63/64 forwarding,
      stipend) is erased — the callee is entered with `0` forwarded gas
      (the user can pick any value when re-injecting gas via `EquivNG`). -/
  | call (s : State)
        (gasArg toArg value argsOff argsLen retOff retLen : UInt256)
        (rest : List UInt256)
        (h_op      : s.decodedOp = some .CALL)
        (h_stack   : s.stack =
                       gasArg :: toArg :: value :: argsOff :: argsLen :: retOff :: retLen :: rest)
        (h_take    : ¬ (s.executionEnv.depth ≥ 1024 ∨
                        (s.accountMap s.executionEnv.codeOwner).balance < value))
      : StepRunning s
          ((s.advanceMem2 argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat).enterCall
             rest (AccountAddress.ofUInt256 toArg) value
             (MachineState.readPadded s.memory argsOff.toNat argsLen.toNat)
             (s.accountMap (AccountAddress.ofUInt256 toArg)).code
             0
             retOff.toNat retLen.toNat)

  /-- CALL (not taken): the depth limit is hit or the caller cannot afford the
      value. `0` is pushed and `returnData` is cleared. -/
  | callFail (s : State)
        (gasArg toArg value argsOff argsLen retOff retLen : UInt256)
        (rest : List UInt256)
        (h_op      : s.decodedOp = some .CALL)
        (h_stack   : s.stack =
                       gasArg :: toArg :: value :: argsOff :: argsLen :: retOff :: retLen :: rest)
        (h_fail    : s.executionEnv.depth ≥ 1024 ∨
                       (s.accountMap s.executionEnv.codeOwner).balance < value)
      : StepRunning s
          ({ s.advanceMem2 argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat
              with returnData := .empty }.replaceStackAndIncrPC
            (UInt256.ofNat 0 :: rest))

  ----------------------------------------------------------------------------
  -- Logging: LOG0–LOG4 (parametric over topic count).
  ----------------------------------------------------------------------------

  /-- LOG `n`: pop offset, size, then `n` topics; append a log entry. -/
  | log (s : State) (n : Fin 5) (offset size : UInt256)
        (topics : List UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some (.Log ⟨n⟩))
        (h_perm     : s.executionEnv.permitStateMutation = true)
        (h_topics_n : topics.length = n.val)
        (h_stack    : s.stack = offset :: size :: topics ++ rest)
      : StepRunning s
          (let entry : LogEntry :=
             { address := s.executionEnv.codeOwner
               topics  := topics.toArray
               data    := MachineState.readPadded s.memory offset.toNat size.toNat }
           let s'' := s.advanceMem offset.toNat size.toNat
           { s'' with substate := s.substate.appendLog entry }
             |>.replaceStackAndIncrPC rest)

  ----------------------------------------------------------------------------
  -- EIP-8024: DUPN, SWAPN, EXCHANGE.
  ----------------------------------------------------------------------------

  /-- DUPN with immediate `n`: duplicate `stack[n]` to the top. PC += 2. -/
  | dupN (s : State) (n : Fin 256) (v : UInt256)
        (h_op      : s.decodedOp = some (.DupN ⟨n⟩))
        (h_get     : s.stack[n.val]? = some v)
      : StepRunning s (s.replaceStackAndIncrPC
                  (v :: s.stack) (pcΔ := 2))

  /-- SWAPN with immediate `n`: swap top with `stack[n+1]`. PC += 2. -/
  | swapN (s : State) (n : Fin 256) (stk' : List UInt256)
        (h_op      : s.decodedOp = some (.SwapN ⟨n⟩))
        (h_swap    : s.stack.exchange 0 (n.val + 1) = some stk')
      : StepRunning s (s.replaceStackAndIncrPC
                  stk' (pcΔ := 2))

  /-- EXCHANGE with packed immediate `b`: swap `stack[n+1]` and `stack[m+1]`
      where `n = b >>> 4` and `m = b &&& 0xf`. PC += 2. -/
  | exchange (s : State) (b : Fin 256) (stk' : List UInt256)
        (h_op      : s.decodedOp = some (.Exchange ⟨b⟩))
        (h_swap    : s.stack.exchange
                      (b.val >>> 4 + 1)
                      ((b.val &&& 0xf) + 1) = some stk')
      : StepRunning s
          (s.replaceStackAndIncrPC
            stk' (pcΔ := 2))

  ----------------------------------------------------------------------------
  -- Exception rules.
  --
  -- These constructors halt the frame with `halt := .Exception e`. They are
  -- written *parametrically* over the operation where possible — one rule
  -- per failure mode rather than one per (op, failure-mode) pair. The
  -- non-overlap between success and exception rules comes from disjoint
  -- hypotheses (`Gas.baseCost s.fork op ≤ gas` vs. `gas < Gas.baseCost s.fork op`, etc.).
  --
  -- Several exception rules may fire simultaneously from the same state
  -- (e.g. underflow AND out-of-gas). The relational semantics is
  -- *non-deterministic* about which exception is reported. A deterministic
  -- check order can be layered on top later if desired.
  ----------------------------------------------------------------------------

  /-- Decode failure: the byte at the PC isn't a recognised opcode. -/
  | decodeFailure (s : State)
        (h_none    : s.decoded = none)
      : StepRunning s (s.haltWith .InvalidInstruction)

  /-- The explicit `INVALID` opcode (`0xfe`). -/
  | invalidOpcode (s : State)
        (h_op      : s.decodedOp = some .INVALID)
      : StepRunning s (s.haltWith .InvalidInstruction)

  -- `outOfGas` is intentionally absent from `StepRunning`: the gas-free
  -- semantics has no notion of "running out of gas", so the corresponding
  -- relational halt rule is dropped. The equivalence in `EVM/EquivNG.lean`
  -- maps `Step.running … (.outOfGas …)` to "no NG counterpart" and the
  -- gas-witness direction only synthesises non-OOG-halting `Eval`s.

  /-- Stack has fewer items than the operation requires to pop. -/
  | stackUnderflow (s : State) (op : Operation)
        (h_op      : s.decodedOp = some op)
        (h_under   : s.stack.length < op.popArity)
      : StepRunning s (s.haltWith .StackUnderflow)

  /-- Executing this operation would grow the stack beyond the 1024-item
      EVM limit. Requires `popArity ≤ length` so the subtraction is well
      defined. -/
  | stackOverflow (s : State) (op : Operation)
        (h_op      : s.decodedOp = some op)
        (h_pop_ok  : op.popArity ≤ s.stack.length)
        (h_over    : s.stack.length - op.popArity + op.pushArity > 1024)
      : StepRunning s (s.haltWith .StackOverflow)

  /-- State-mutating operation attempted while
      `executionEnv.permitStateMutation = false`. -/
  | staticModeViolation (s : State) (op : Operation)
        (h_op      : s.decodedOp = some op)
        (h_mut     : op.isStateMutating = true)
        (h_perm    : s.executionEnv.permitStateMutation = false)
      : StepRunning s (s.haltWith .StaticModeViolation)

  /-- JUMP to a destination that is not a valid `JUMPDEST`: either the byte
      there is not `0x5b`, or it sits inside PUSH immediate data and so is
      not reachable as an instruction boundary. -/
  | jumpBadDest (s : State) (dest : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .JUMP)
        (h_stack   : s.stack = dest :: rest)
        (h_bad     : Decode.isValidJumpDest s.executionEnv.code dest.toNat = false)
      : StepRunning s (s.haltWith .BadJumpDestination)

  /-- JUMPI with `cond ≠ 0` but the destination is not a valid `JUMPDEST`
      (same rule as `jumpBadDest` — push-data byte or non-`0x5b`). -/
  | jumpiBadDest (s : State) (dest cond : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .JUMPI)
        (h_stack   : s.stack = dest :: cond :: rest)
        (h_cond    : UInt256.isTrue cond)
        (h_bad     : Decode.isValidJumpDest s.executionEnv.code dest.toNat = false)
      : StepRunning s (s.haltWith .BadJumpDestination)

  /-- RETURNDATACOPY with `srcOffset + size > returnData.size`. -/
  | returndatacopyOob (s : State) (destOff srcOff sz : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .RETURNDATACOPY)
        (h_stack   : s.stack = destOff :: srcOff :: sz :: rest)
        (h_oob     : srcOff.toNat + sz.toNat > s.returnData.size)
      : StepRunning s (s.haltWith .InvalidMemoryAccess)

/-- Call-return resume relation. Fires on a *halted* active frame whose
    `callStack` is non-empty: the child has finished, so we pop the caller
    frame `f` and resume it (writing the child's return data into the
    caller's memory and pushing the success flag). Each constructor pins
    the concrete halt kind via `h_halt` and the non-empty stack via
    `h_stack`, so a `StepReturn s s'` derivation by itself implies
    `s.halt ≠ .Running ∧ s.callStack ≠ []`. -/
inductive StepReturn : State → State → Prop

  /-- Child STOP/RETURN: resume the caller with success flag `1`, keeping the
      child's world mutations and refunding its unspent gas. -/
  | callReturnSuccess (s : State) (f : Frame) (rest : List Frame)
        (h_halt  : s.halt = .Success ∨ s.halt = .Returned)
        (h_stack : s.callStack = f :: rest)
      : StepReturn s (s.resumeSuccess f rest)

  /-- Child REVERT: resume the caller with failure flag `0`, roll the world
      back to the call-time snapshot, return the revert data, refund unspent gas. -/
  | callReturnRevert (s : State) (f : Frame) (rest : List Frame)
        (h_halt  : s.halt = .Reverted)
        (h_stack : s.callStack = f :: rest)
      : StepReturn s (s.resumeRevert f rest)

  /-- Child exceptional halt: resume the caller with failure flag `0`, roll the
      world back, return no data, and refund nothing. -/
  | callReturnException (s : State) (f : Frame) (rest : List Frame)
        (e : ExecutionException)
        (h_halt  : s.halt = .Exception e)
        (h_stack : s.callStack = f :: rest)
      : StepReturn s (s.resumeException f rest)

/-- The combined small-step relation. A `Step s s'` derivation is either a
    `StepRunning` transition guarded by the precondition `s.halt = .Running`,
    or a `StepReturn` transition (which carries its own halt-kind premise
    internally). This is the two-sided shape that `Eval` / `Steps` use; the
    soundness lemmas in `Equiv.lean` produce `StepRunning` and `StepReturn`
    directly, and the headline `stepF_sound` wraps them via `.running` /
    `.returning` after dispatching on `s.halt`. -/
inductive Step : State → State → Prop
  /-- A running-state transition: the per-opcode logic encoded by
      `StepRunning`, plus the explicit `s.halt = .Running` guard that lets
      `not_from_done` rule out successors from done states. -/
  | running : ∀ {s s' : State}, s.halt = .Running → StepRunning s s' → Step s s'
  /-- A call-return transition: the inner `StepReturn` already implies
      `s.halt ≠ .Running` (each constructor pins the halt kind) and
      `s.callStack ≠ []` (each carries `h_stack : callStack = _ :: _`). -/
  | returning : ∀ {s s' : State}, StepReturn s s' → Step s s'

end EvmSemantics.GasFreeEVM
