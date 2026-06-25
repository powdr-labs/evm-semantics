module

public import EvmSemantics.Data.UInt256
public import EvmSemantics.EVM.Operation

/-!
`Decode` — the bytecode-byte → `Operation` mapping, plus the function
`decodeAt` that reads an opcode (with its immediate, if any) from the
execution-environment's bytecode at a given program counter.

For PUSH instructions, the immediate data is returned as a separate
`(UInt256 × Nat)` argument (value + width-in-bytes), matching the
reference's `decode`. For the EIP-8024 ops (DUPN/SWAPN/EXCHANGE), the
single immediate byte is folded into the `Operation` value itself
(via the `Fin 256` field on `DupNOp` / `SwapNOp` / `ExchangeOp`), so
no separate argument is needed.

The byte→opcode map mirrors the Yellow Paper instruction table; we
return `none` for any byte not assigned to a v1-supported instruction.
-/

@[expose] public section

namespace EvmSemantics
namespace EVM
namespace Decode

/-- The opcode kind at byte `b`, if any. For PUSH/DUP/SWAP the resulting
    `Operation` carries the variant index (e.g. `PUSH1` → `Operation.Push ⟨1⟩`).
    For DUPN/SWAPN/EXCHANGE the EIP-8024 immediate is *not* read here —
    `opAt` reads it and reconstructs the full `Operation`. -/
def opcodeOf (b : UInt8) : Option Operation :=
  match b.toNat with
  -- 0x00 - 0x0b : stop and arithmetic
  | 0x00 => some .STOP
  | 0x01 => some .ADD
  | 0x02 => some .MUL
  | 0x03 => some .SUB
  | 0x04 => some .DIV
  | 0x05 => some .SDIV
  | 0x06 => some .MOD
  | 0x07 => some .SMOD
  | 0x08 => some .ADDMOD
  | 0x09 => some .MULMOD
  | 0x0a => some .EXP
  | 0x0b => some .SIGNEXTEND
  -- 0x10 - 0x1d : comparison and bitwise
  | 0x10 => some .LT
  | 0x11 => some .GT
  | 0x12 => some .SLT
  | 0x13 => some .SGT
  | 0x14 => some .EQ
  | 0x15 => some .ISZERO
  | 0x16 => some .AND
  | 0x17 => some .OR
  | 0x18 => some .XOR
  | 0x19 => some .NOT
  | 0x1a => some .BYTE
  | 0x1b => some .SHL
  | 0x1c => some .SHR
  | 0x1d => some .SAR
  -- 0x20 : Keccak
  | 0x20 => some .KECCAK256
  -- 0x30 - 0x3f : environment
  | 0x30 => some .ADDRESS
  | 0x31 => some .BALANCE
  | 0x32 => some .ORIGIN
  | 0x33 => some .CALLER
  | 0x34 => some .CALLVALUE
  | 0x35 => some .CALLDATALOAD
  | 0x36 => some .CALLDATASIZE
  | 0x37 => some .CALLDATACOPY
  | 0x38 => some .CODESIZE
  | 0x39 => some .CODECOPY
  | 0x3a => some .GASPRICE
  | 0x3b => some .EXTCODESIZE
  | 0x3c => some .EXTCODECOPY
  | 0x3d => some .RETURNDATASIZE
  | 0x3e => some .RETURNDATACOPY
  | 0x3f => some .EXTCODEHASH
  -- 0x40 - 0x4a : block
  | 0x40 => some .BLOCKHASH
  | 0x41 => some .COINBASE
  | 0x42 => some .TIMESTAMP
  | 0x43 => some .NUMBER
  | 0x44 => some .PREVRANDAO
  | 0x45 => some .GASLIMIT
  | 0x46 => some .CHAINID
  | 0x47 => some .SELFBALANCE
  | 0x48 => some .BASEFEE
  | 0x49 => some .BLOBHASH
  | 0x4a => some .BLOBBASEFEE
  -- 0x50 - 0x5e : stack/memory/storage/flow
  | 0x50 => some .POP
  | 0x51 => some .MLOAD
  | 0x52 => some .MSTORE
  | 0x53 => some .MSTORE8
  | 0x54 => some .SLOAD
  | 0x55 => some .SSTORE
  | 0x56 => some .JUMP
  | 0x57 => some .JUMPI
  | 0x58 => some .PC
  | 0x59 => some .MSIZE
  | 0x5a => some .GAS
  | 0x5b => some .JUMPDEST
  | 0x5c => some .TLOAD
  | 0x5d => some .TSTORE
  | 0x5e => some .MCOPY
  -- 0x5f - 0xa4 handled below
  | 0xf0 => some .CREATE
  | 0xf1 => some .CALL
  | 0xf2 => some .CALLCODE
  | 0xf3 => some .RETURN
  | 0xf4 => some .DELEGATECALL
  | 0xf5 => some .CREATE2
  | 0xfa => some .STATICCALL
  | 0xfd => some .REVERT
  | 0xfe => some .INVALID
  | 0xff => some .SELFDESTRUCT
    -- 0xe6 - 0xe8 : EIP-8024. opcodeOf returns a placeholder with
    -- immediate = 0; the real immediate is filled in by `decodeAt`.
  | 0xe6 => some (.DupN ⟨0, by decide⟩)
  | 0xe7 => some (.SwapN ⟨0, by decide⟩)
  | 0xe8 => some (.Exchange ⟨0, by decide⟩)
  -- 0x5f - 0x7f : PUSH0 - PUSH32
  | n =>
    if h : 0x5f ≤ n ∧ n ≤ 0x7f then
      some (.Push ⟨n - 0x5f, by omega⟩)
    -- 0x80 - 0x8f : DUP1 - DUP16
    else if h : 0x80 ≤ n ∧ n ≤ 0x8f then
      some (.Dup ⟨n - 0x80, by omega⟩)
    -- 0x90 - 0x9f : SWAP1 - SWAP16
    else if h : 0x90 ≤ n ∧ n ≤ 0x9f then
      some (.Swap ⟨n - 0x90, by omega⟩)
    -- 0xa0 - 0xa4 : LOG0 - LOG4
    else if h : 0xa0 ≤ n ∧ n ≤ 0xa4 then
      some (.Log ⟨n - 0xa0, by omega⟩)
    -- 0xf0 - 0xff : system
    else
      none

/-- Read a big-endian word from a byte slice. -/
def beToNat (bs : ByteArray) : Nat :=
  bs.toList.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- Read the (opcode, optional argument-value × width) at `pc` in `code`.

    Past the end of the bytecode (`pc ≥ code.size`) the machine reads an
    implicit `STOP`: the Yellow Paper treats code as zero-padded, and `0x00`
    is `STOP`. This makes a program that simply runs off the end halt with
    success rather than `InvalidInstruction`. Within `code`, an unassigned
    byte still decodes to `none` (→ `InvalidInstruction`). -/
def decodeAt (code : ByteArray) (pc : Nat) : Option (Operation × Option (UInt256 × Nat)) :=
  if h : pc < code.size then do
    let op ← opcodeOf code[pc]
    match op with
    | .Push ⟨w, _⟩ =>
      let bs := code.extract (pc + 1) (pc + 1 + w)
      let n := beToNat bs
      return (op, some (UInt256.ofNat n, w))
    | .DupN _ =>
      -- 0xe6 followed by 1 immediate byte
      let imm := if h : pc + 1 < code.size then code[pc + 1]'h else 0
      return (.DupN ⟨imm.toNat, by have := imm.toNat_lt; omega⟩, none)
    | .SwapN _ =>
      let imm := if h : pc + 1 < code.size then code[pc + 1]'h else 0
      return (.SwapN ⟨imm.toNat, by have := imm.toNat_lt; omega⟩, none)
    | .Exchange _ =>
      let imm := if h : pc + 1 < code.size then code[pc + 1]'h else 0
      return (.Exchange ⟨imm.toNat, by have := imm.toNat_lt; omega⟩, none)
    | _ => return (op, none)
  else
    some (.STOP, none)

end Decode
end EVM
end EvmSemantics
