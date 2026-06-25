module

/-!
`Operation` — the EVM instruction set, mirrored from `EvmYul.Operations`.

We use the same hierarchical grouping but drop the `OperationType` parameter
(`τ`) since v1 only handles `.EVM`. Group names are spelled out (`BlockOps`
rather than `BOp`) — only the standard mnemonic opcode names (`ADD`, `STOP`,
…) remain short.
-/

@[expose] public section

namespace EvmSemantics

namespace Operation

/-- Stop and arithmetic operations. -/
inductive StopArithOps where
  | STOP | ADD | MUL | SUB | DIV | SDIV | MOD | SMOD
  | ADDMOD | MULMOD | EXP | SIGNEXTEND
  deriving DecidableEq, Repr, Inhabited

/-- Comparison and bitwise-logic operations. -/
inductive CompareBitwiseOps where
  | LT | GT | SLT | SGT | EQ | ISZERO
  | AND | OR | XOR | NOT | BYTE | SHL | SHR | SAR
  deriving DecidableEq, Repr, Inhabited

/-- Keccak hashing. -/
inductive KeccakOps where | KECCAK256
  deriving DecidableEq, Repr, Inhabited

/-- Environment information. -/
inductive EnvOps where
  | ADDRESS | BALANCE | ORIGIN | CALLER | CALLVALUE
  | CALLDATALOAD | CALLDATASIZE | CALLDATACOPY
  | CODESIZE | CODECOPY
  | GASPRICE | EXTCODESIZE | EXTCODECOPY
  | RETURNDATASIZE | RETURNDATACOPY
  | EXTCODEHASH
  deriving DecidableEq, Repr, Inhabited

/-- Block information. -/
inductive BlockOps where
  | BLOCKHASH | COINBASE | TIMESTAMP | NUMBER | PREVRANDAO
  | GASLIMIT | CHAINID | SELFBALANCE | BASEFEE
  | BLOBHASH | BLOBBASEFEE
  deriving DecidableEq, Repr, Inhabited

/-- Stack, memory, storage, and control-flow. -/
inductive StackMemFlowOps where
  | POP
  | MLOAD | MSTORE | MSTORE8
  | SLOAD | SSTORE
  | JUMP | JUMPI | PC | JUMPDEST
  | MSIZE | GAS
  | TLOAD | TSTORE | MCOPY
  deriving DecidableEq, Repr, Inhabited

/-- PUSH0–PUSH32. The constructor index `width : Fin 33` is the # of bytes
    pushed (PUSH0 = 0 bytes, PUSH32 = 32 bytes). -/
structure PushOp where
  width : Fin 33
  deriving DecidableEq, Repr, Inhabited

/-- DUP1–DUP16. The constructor index `idx : Fin 16` plus one is the
    stack position to copy (DUP1 copies stack[0], DUP16 copies stack[15]). -/
structure DupOp where
  idx : Fin 16
  deriving DecidableEq, Repr, Inhabited

/-- SWAP1–SWAP16. -/
structure SwapOp where
  idx : Fin 16
  deriving DecidableEq, Repr, Inhabited

/-- DUPN (EIP-8024, opcode `0xe6`) — duplicates the `n`-th stack item.
    The immediate byte `n` (`0 ≤ n ≤ 255`) is read from the bytecode at
    decode time. Per EIP-8024, immediate bytes `0x5b` and `0x60..0x7f`
    must be rejected to preserve jump-target analysis. -/
structure DupNOp where
  n : Fin 256
  deriving DecidableEq, Repr, Inhabited

/-- SWAPN (EIP-8024, opcode `0xe7`) — swaps the top with the `(n+1)`-th
    stack item. Immediate byte `n` (`0 ≤ n ≤ 255`). -/
structure SwapNOp where
  n : Fin 256
  deriving DecidableEq, Repr, Inhabited

/-- EXCHANGE (EIP-8024, opcode `0xe8`) — swaps the `(n+1)`-th and
    `(m+1)`-th stack items. The single immediate byte packs `n` in the
    high nibble and `m` in the low nibble, so both range over `[0, 15]`. -/
structure ExchangeOp where
  packed : Fin 256
  deriving DecidableEq, Repr, Inhabited

namespace ExchangeOp
/-- Decode the high-nibble operand `n`. -/
def n (op : ExchangeOp) : Nat := op.packed.val >>> 4
/-- Decode the low-nibble operand `m`. -/
def m (op : ExchangeOp) : Nat := op.packed.val &&& 0xf
end ExchangeOp

/-- LOG0–LOG4. `topics : Fin 5` is the number of topics. -/
structure LogOp where
  topics : Fin 5
  deriving DecidableEq, Repr, Inhabited

/-- System operations (calls, creates, halts, etc.). -/
inductive SystemOps where
  | CREATE | CALL | CALLCODE | RETURN | DELEGATECALL | CREATE2 | STATICCALL
  | REVERT | INVALID | SELFDESTRUCT
  deriving DecidableEq, Repr, Inhabited

end Operation

inductive Operation where
  | StopArith    : Operation.StopArithOps      → Operation
  | CompBit      : Operation.CompareBitwiseOps → Operation
  | Keccak       : Operation.KeccakOps         → Operation
  | Env          : Operation.EnvOps            → Operation
  | Block        : Operation.BlockOps          → Operation
  | StackMemFlow : Operation.StackMemFlowOps   → Operation
  | Push         : Operation.PushOp            → Operation
  | Dup          : Operation.DupOp             → Operation
  | Swap         : Operation.SwapOp            → Operation
  | DupN         : Operation.DupNOp            → Operation
  | SwapN        : Operation.SwapNOp           → Operation
  | Exchange     : Operation.ExchangeOp        → Operation
  | Log          : Operation.LogOp             → Operation
  | System       : Operation.SystemOps         → Operation
  deriving DecidableEq, Repr, Inhabited

namespace Operation

@[match_pattern] abbrev STOP       : Operation := .StopArith .STOP
@[match_pattern] abbrev ADD        : Operation := .StopArith .ADD
@[match_pattern] abbrev MUL        : Operation := .StopArith .MUL
@[match_pattern] abbrev SUB        : Operation := .StopArith .SUB
@[match_pattern] abbrev DIV        : Operation := .StopArith .DIV
@[match_pattern] abbrev SDIV       : Operation := .StopArith .SDIV
@[match_pattern] abbrev MOD        : Operation := .StopArith .MOD
@[match_pattern] abbrev SMOD       : Operation := .StopArith .SMOD
@[match_pattern] abbrev ADDMOD     : Operation := .StopArith .ADDMOD
@[match_pattern] abbrev MULMOD     : Operation := .StopArith .MULMOD
@[match_pattern] abbrev EXP        : Operation := .StopArith .EXP
@[match_pattern] abbrev SIGNEXTEND : Operation := .StopArith .SIGNEXTEND

@[match_pattern] abbrev LT     : Operation := .CompBit .LT
@[match_pattern] abbrev GT     : Operation := .CompBit .GT
@[match_pattern] abbrev SLT    : Operation := .CompBit .SLT
@[match_pattern] abbrev SGT    : Operation := .CompBit .SGT
@[match_pattern] abbrev EQ     : Operation := .CompBit .EQ
@[match_pattern] abbrev ISZERO : Operation := .CompBit .ISZERO
@[match_pattern] abbrev AND    : Operation := .CompBit .AND
@[match_pattern] abbrev OR     : Operation := .CompBit .OR
@[match_pattern] abbrev XOR    : Operation := .CompBit .XOR
@[match_pattern] abbrev NOT    : Operation := .CompBit .NOT
@[match_pattern] abbrev BYTE   : Operation := .CompBit .BYTE
@[match_pattern] abbrev SHL    : Operation := .CompBit .SHL
@[match_pattern] abbrev SHR    : Operation := .CompBit .SHR
@[match_pattern] abbrev SAR    : Operation := .CompBit .SAR

@[match_pattern] abbrev KECCAK256 : Operation := .Keccak .KECCAK256

@[match_pattern] abbrev ADDRESS        : Operation := .Env .ADDRESS
@[match_pattern] abbrev BALANCE        : Operation := .Env .BALANCE
@[match_pattern] abbrev ORIGIN         : Operation := .Env .ORIGIN
@[match_pattern] abbrev CALLER         : Operation := .Env .CALLER
@[match_pattern] abbrev CALLVALUE      : Operation := .Env .CALLVALUE
@[match_pattern] abbrev CALLDATALOAD   : Operation := .Env .CALLDATALOAD
@[match_pattern] abbrev CALLDATASIZE   : Operation := .Env .CALLDATASIZE
@[match_pattern] abbrev CALLDATACOPY   : Operation := .Env .CALLDATACOPY
@[match_pattern] abbrev CODESIZE       : Operation := .Env .CODESIZE
@[match_pattern] abbrev CODECOPY       : Operation := .Env .CODECOPY
@[match_pattern] abbrev GASPRICE       : Operation := .Env .GASPRICE
@[match_pattern] abbrev EXTCODESIZE    : Operation := .Env .EXTCODESIZE
@[match_pattern] abbrev EXTCODECOPY    : Operation := .Env .EXTCODECOPY
@[match_pattern] abbrev RETURNDATASIZE : Operation := .Env .RETURNDATASIZE
@[match_pattern] abbrev RETURNDATACOPY : Operation := .Env .RETURNDATACOPY
@[match_pattern] abbrev EXTCODEHASH    : Operation := .Env .EXTCODEHASH

@[match_pattern] abbrev BLOCKHASH   : Operation := .Block .BLOCKHASH
@[match_pattern] abbrev COINBASE    : Operation := .Block .COINBASE
@[match_pattern] abbrev TIMESTAMP   : Operation := .Block .TIMESTAMP
@[match_pattern] abbrev NUMBER      : Operation := .Block .NUMBER
@[match_pattern] abbrev PREVRANDAO  : Operation := .Block .PREVRANDAO
@[match_pattern] abbrev GASLIMIT    : Operation := .Block .GASLIMIT
@[match_pattern] abbrev CHAINID     : Operation := .Block .CHAINID
@[match_pattern] abbrev SELFBALANCE : Operation := .Block .SELFBALANCE
@[match_pattern] abbrev BASEFEE     : Operation := .Block .BASEFEE
@[match_pattern] abbrev BLOBHASH    : Operation := .Block .BLOBHASH
@[match_pattern] abbrev BLOBBASEFEE : Operation := .Block .BLOBBASEFEE

@[match_pattern] abbrev POP      : Operation := .StackMemFlow .POP
@[match_pattern] abbrev MLOAD    : Operation := .StackMemFlow .MLOAD
@[match_pattern] abbrev MSTORE   : Operation := .StackMemFlow .MSTORE
@[match_pattern] abbrev MSTORE8  : Operation := .StackMemFlow .MSTORE8
@[match_pattern] abbrev SLOAD    : Operation := .StackMemFlow .SLOAD
@[match_pattern] abbrev SSTORE   : Operation := .StackMemFlow .SSTORE
@[match_pattern] abbrev JUMP     : Operation := .StackMemFlow .JUMP
@[match_pattern] abbrev JUMPI    : Operation := .StackMemFlow .JUMPI
@[match_pattern] abbrev PC       : Operation := .StackMemFlow .PC
@[match_pattern] abbrev JUMPDEST : Operation := .StackMemFlow .JUMPDEST
@[match_pattern] abbrev MSIZE    : Operation := .StackMemFlow .MSIZE
@[match_pattern] abbrev GAS      : Operation := .StackMemFlow .GAS
@[match_pattern] abbrev TLOAD    : Operation := .StackMemFlow .TLOAD
@[match_pattern] abbrev TSTORE   : Operation := .StackMemFlow .TSTORE
@[match_pattern] abbrev MCOPY    : Operation := .StackMemFlow .MCOPY

/-- EIP-8024 DUPN with immediate operand `n`. -/
@[match_pattern] abbrev DUPN (n : Fin 256) : Operation := .DupN ⟨n⟩
/-- EIP-8024 SWAPN with immediate operand `n`. -/
@[match_pattern] abbrev SWAPN (n : Fin 256) : Operation := .SwapN ⟨n⟩
/-- EIP-8024 EXCHANGE with packed immediate `b` (high nibble = `n`,
    low nibble = `m`). -/
@[match_pattern] abbrev EXCHANGE (b : Fin 256) : Operation := .Exchange ⟨b⟩

@[match_pattern] abbrev CREATE       : Operation := .System .CREATE
@[match_pattern] abbrev CALL         : Operation := .System .CALL
@[match_pattern] abbrev CALLCODE     : Operation := .System .CALLCODE
@[match_pattern] abbrev RETURN       : Operation := .System .RETURN
@[match_pattern] abbrev DELEGATECALL : Operation := .System .DELEGATECALL
@[match_pattern] abbrev CREATE2      : Operation := .System .CREATE2
@[match_pattern] abbrev STATICCALL   : Operation := .System .STATICCALL
@[match_pattern] abbrev REVERT       : Operation := .System .REVERT
@[match_pattern] abbrev INVALID      : Operation := .System .INVALID
@[match_pattern] abbrev SELFDESTRUCT : Operation := .System .SELFDESTRUCT

end Operation

/-- # of immediate-argument bytes following the opcode in the bytecode.
    Non-zero for PUSH1..PUSH32 and the EIP-8024 ops DUPN/SWAPN/EXCHANGE. -/
def Operation.argBytes : Operation → Nat
  | .Push p  => p.width.val
  | .DupN _  => 1
  | .SwapN _ => 1
  | .Exchange _ => 1
  | _        => 0

/-- The Yellow Paper `δ` — stack-pop arity. -/
def Operation.popArity : Operation → Nat
  | .StopArith op =>
    match op with
    | .STOP => 0 | .ADD | .MUL | .SUB | .DIV | .SDIV | .MOD | .SMOD | .EXP | .SIGNEXTEND => 2
    | .ADDMOD | .MULMOD => 3
  | .CompBit op =>
    match op with
    | .ISZERO | .NOT => 1
    | _ => 2
  | .Keccak _ => 2
  | .Env op =>
    match op with
    | .ADDRESS | .ORIGIN | .CALLER | .CALLVALUE | .CALLDATASIZE | .CODESIZE
    | .GASPRICE | .RETURNDATASIZE => 0
    | .BALANCE | .CALLDATALOAD | .EXTCODESIZE | .EXTCODEHASH => 1
    | .CALLDATACOPY | .CODECOPY | .RETURNDATACOPY => 3
    | .EXTCODECOPY => 4
  | .Block op =>
    match op with
    | .BLOCKHASH | .BLOBHASH => 1
    | _ => 0
  | .StackMemFlow op =>
    match op with
    | .POP | .MLOAD | .SLOAD | .JUMP | .TLOAD => 1
    | .MSTORE | .MSTORE8 | .SSTORE | .JUMPI | .TSTORE => 2
    | .PC | .JUMPDEST | .MSIZE | .GAS => 0
    | .MCOPY => 3
  | .Push _ => 0
  | .Dup d => d.idx.val + 1
  | .Swap e => e.idx.val + 2
  | .DupN d => d.n.val + 1
  | .SwapN s => s.n.val + 2
  | .Exchange e => Nat.max (e.n + 1) (e.m + 1) + 1
  | .Log l => l.topics.val + 2
  | .System op =>
    match op with
    | .CREATE => 3 | .CREATE2 => 4
    | .CALL | .CALLCODE => 7
    | .DELEGATECALL | .STATICCALL => 6
    | .RETURN | .REVERT => 2
    | .SELFDESTRUCT => 1
    | .INVALID => 0

/-- Operations whose execution mutates persistent or transient state and
    must therefore be rejected when `executionEnv.permitStateMutation = false` (static
    mode). Mirrors the reference's `W` predicate restricted to v1 ops. -/
def Operation.isStateMutating : Operation → Bool
  | .SSTORE     => true
  | .TSTORE     => true
  | .Log _      => true
  -- Out-of-scope for v1 but listed for forward compatibility:
  | .CREATE     => true
  | .CREATE2    => true
  | .SELFDESTRUCT => true
  | _           => false

/-- The Yellow Paper `α` — # of items pushed back. -/
def Operation.pushArity : Operation → Nat
  | .StopArith op => match op with | .STOP => 0 | _ => 1
  | .CompBit _ => 1
  | .Keccak _ => 1
  | .Env op =>
    match op with
    | .CALLDATACOPY | .CODECOPY | .EXTCODECOPY | .RETURNDATACOPY => 0
    | _ => 1
  | .Block _ => 1
  | .StackMemFlow op =>
    match op with
    | .POP | .MSTORE | .MSTORE8 | .SSTORE | .JUMP | .JUMPI | .JUMPDEST
    | .TSTORE | .MCOPY => 0
    | .MLOAD | .SLOAD | .PC | .MSIZE | .GAS | .TLOAD => 1
  | .Push _ => 1
  | .Dup d => d.idx.val + 2
  | .Swap e => e.idx.val + 2
  | .DupN d => d.n.val + 2
  | .SwapN s => s.n.val + 2
  | .Exchange e => Nat.max (e.n + 1) (e.m + 1) + 1
  | .Log _ => 0
  | .System op =>
    match op with
    | .CREATE | .CREATE2 | .CALL | .CALLCODE | .DELEGATECALL | .STATICCALL => 1
    | .RETURN | .REVERT | .INVALID | .SELFDESTRUCT => 0

end EvmSemantics
