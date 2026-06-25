import Batteries.Tactic.Lint.Misc
import Batteries.Tactic.Lint.Simp

/-!
`Operation` — the EVM instruction set, mirrored from `EvmYul.Operations`.

We use the same hierarchical grouping but drop the `OperationType` parameter
(`τ`) since v1 only handles `.EVM`. Group names are spelled out (`BlockOps`
rather than `BOp`) — only the standard mnemonic opcode names (`ADD`, `STOP`,
…) remain short.
-/

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
  /-- Number of immediate bytes pushed (0 for `PUSH0`, …, 32 for `PUSH32`). -/
  width : Fin 33
  deriving DecidableEq, Repr, Inhabited

/-- DUP1–DUP16. The constructor index `idx : Fin 16` plus one is the
    stack position to copy (DUP1 copies stack[0], DUP16 copies stack[15]). -/
structure DupOp where
  /-- Zero-indexed stack position to duplicate (0 for `DUP1`, …, 15 for `DUP16`). -/
  idx : Fin 16
  deriving DecidableEq, Repr, Inhabited

/-- SWAP1–SWAP16. -/
structure SwapOp where
  /-- Zero-indexed depth of the element to swap with the top (0 for `SWAP1`, …, 15 for `SWAP16`). -/
  idx : Fin 16
  deriving DecidableEq, Repr, Inhabited

/-- DUPN (EIP-8024, opcode `0xe6`) — duplicates the `n`-th stack item.
    The immediate byte `n` (`0 ≤ n ≤ 255`) is read from the bytecode at
    decode time. Per EIP-8024, immediate bytes `0x5b` and `0x60..0x7f`
    must be rejected to preserve jump-target analysis. -/
structure DupNOp where
  /-- Immediate byte: zero-indexed stack position to duplicate. -/
  n : Fin 256
  deriving DecidableEq, Repr, Inhabited

/-- SWAPN (EIP-8024, opcode `0xe7`) — swaps the top with the `(n+1)`-th
    stack item. Immediate byte `n` (`0 ≤ n ≤ 255`). -/
structure SwapNOp where
  /-- Immediate byte: swap top with `stack[n+1]`. -/
  n : Fin 256
  deriving DecidableEq, Repr, Inhabited

/-- EXCHANGE (EIP-8024, opcode `0xe8`) — swaps the `(n+1)`-th and
    `(m+1)`-th stack items. The single immediate byte packs `n` in the
    high nibble and `m` in the low nibble, so both range over `[0, 15]`. -/
structure ExchangeOp where
  /-- Packed immediate byte: high nibble = `n`, low nibble = `m`. -/
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
  /-- Number of indexed topics (0 for `LOG0`, …, 4 for `LOG4`). -/
  topics : Fin 5
  deriving DecidableEq, Repr, Inhabited

/-- System operations (calls, creates, halts, etc.). -/
inductive SystemOps where
  | CREATE | CALL | CALLCODE | RETURN | DELEGATECALL | CREATE2 | STATICCALL
  | REVERT | INVALID | SELFDESTRUCT
  deriving DecidableEq, Repr, Inhabited

end Operation

/-- The EVM instruction set as a tagged sum over per-category sub-inductives. -/
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

/-- Opcode `STOP`. -/
@[match_pattern] abbrev STOP       : Operation := .StopArith .STOP
/-- Opcode `ADD`. -/
@[match_pattern] abbrev ADD        : Operation := .StopArith .ADD
/-- Opcode `MUL`. -/
@[match_pattern] abbrev MUL        : Operation := .StopArith .MUL
/-- Opcode `SUB`. -/
@[match_pattern] abbrev SUB        : Operation := .StopArith .SUB
/-- Opcode `DIV`. -/
@[match_pattern] abbrev DIV        : Operation := .StopArith .DIV
/-- Opcode `SDIV`. -/
@[match_pattern] abbrev SDIV       : Operation := .StopArith .SDIV
/-- Opcode `MOD`. -/
@[match_pattern] abbrev MOD        : Operation := .StopArith .MOD
/-- Opcode `SMOD`. -/
@[match_pattern] abbrev SMOD       : Operation := .StopArith .SMOD
/-- Opcode `ADDMOD`. -/
@[match_pattern] abbrev ADDMOD     : Operation := .StopArith .ADDMOD
/-- Opcode `MULMOD`. -/
@[match_pattern] abbrev MULMOD     : Operation := .StopArith .MULMOD
/-- Opcode `EXP`. -/
@[match_pattern] abbrev EXP        : Operation := .StopArith .EXP
/-- Opcode `SIGNEXTEND`. -/
@[match_pattern] abbrev SIGNEXTEND : Operation := .StopArith .SIGNEXTEND

/-- Opcode `LT`. -/
@[match_pattern] abbrev LT     : Operation := .CompBit .LT
/-- Opcode `GT`. -/
@[match_pattern] abbrev GT     : Operation := .CompBit .GT
/-- Opcode `SLT`. -/
@[match_pattern] abbrev SLT    : Operation := .CompBit .SLT
/-- Opcode `SGT`. -/
@[match_pattern] abbrev SGT    : Operation := .CompBit .SGT
/-- Opcode `EQ`. -/
@[match_pattern] abbrev EQ     : Operation := .CompBit .EQ
/-- Opcode `ISZERO`. -/
@[match_pattern] abbrev ISZERO : Operation := .CompBit .ISZERO
/-- Opcode `AND`. -/
@[match_pattern] abbrev AND    : Operation := .CompBit .AND
/-- Opcode `OR`. -/
@[match_pattern] abbrev OR     : Operation := .CompBit .OR
/-- Opcode `XOR`. -/
@[match_pattern] abbrev XOR    : Operation := .CompBit .XOR
/-- Opcode `NOT`. -/
@[match_pattern] abbrev NOT    : Operation := .CompBit .NOT
/-- Opcode `BYTE`. -/
@[match_pattern] abbrev BYTE   : Operation := .CompBit .BYTE
/-- Opcode `SHL`. -/
@[match_pattern] abbrev SHL    : Operation := .CompBit .SHL
/-- Opcode `SHR`. -/
@[match_pattern] abbrev SHR    : Operation := .CompBit .SHR
/-- Opcode `SAR`. -/
@[match_pattern] abbrev SAR    : Operation := .CompBit .SAR

/-- Opcode `KECCAK256`. -/
@[match_pattern] abbrev KECCAK256 : Operation := .Keccak .KECCAK256

/-- Opcode `ADDRESS`. -/
@[match_pattern] abbrev ADDRESS        : Operation := .Env .ADDRESS
/-- Opcode `BALANCE`. -/
@[match_pattern] abbrev BALANCE        : Operation := .Env .BALANCE
/-- Opcode `ORIGIN`. -/
@[match_pattern] abbrev ORIGIN         : Operation := .Env .ORIGIN
/-- Opcode `CALLER`. -/
@[match_pattern] abbrev CALLER         : Operation := .Env .CALLER
/-- Opcode `CALLVALUE`. -/
@[match_pattern] abbrev CALLVALUE      : Operation := .Env .CALLVALUE
/-- Opcode `CALLDATALOAD`. -/
@[match_pattern] abbrev CALLDATALOAD   : Operation := .Env .CALLDATALOAD
/-- Opcode `CALLDATASIZE`. -/
@[match_pattern] abbrev CALLDATASIZE   : Operation := .Env .CALLDATASIZE
/-- Opcode `CALLDATACOPY`. -/
@[match_pattern] abbrev CALLDATACOPY   : Operation := .Env .CALLDATACOPY
/-- Opcode `CODESIZE`. -/
@[match_pattern] abbrev CODESIZE       : Operation := .Env .CODESIZE
/-- Opcode `CODECOPY`. -/
@[match_pattern] abbrev CODECOPY       : Operation := .Env .CODECOPY
/-- Opcode `GASPRICE`. -/
@[match_pattern] abbrev GASPRICE       : Operation := .Env .GASPRICE
/-- Opcode `EXTCODESIZE`. -/
@[match_pattern] abbrev EXTCODESIZE    : Operation := .Env .EXTCODESIZE
/-- Opcode `EXTCODECOPY`. -/
@[match_pattern] abbrev EXTCODECOPY    : Operation := .Env .EXTCODECOPY
/-- Opcode `RETURNDATASIZE`. -/
@[match_pattern] abbrev RETURNDATASIZE : Operation := .Env .RETURNDATASIZE
/-- Opcode `RETURNDATACOPY`. -/
@[match_pattern] abbrev RETURNDATACOPY : Operation := .Env .RETURNDATACOPY
/-- Opcode `EXTCODEHASH`. -/
@[match_pattern] abbrev EXTCODEHASH    : Operation := .Env .EXTCODEHASH

/-- Opcode `BLOCKHASH`. -/
@[match_pattern] abbrev BLOCKHASH   : Operation := .Block .BLOCKHASH
/-- Opcode `COINBASE`. -/
@[match_pattern] abbrev COINBASE    : Operation := .Block .COINBASE
/-- Opcode `TIMESTAMP`. -/
@[match_pattern] abbrev TIMESTAMP   : Operation := .Block .TIMESTAMP
/-- Opcode `NUMBER`. -/
@[match_pattern] abbrev NUMBER      : Operation := .Block .NUMBER
/-- Opcode `PREVRANDAO`. -/
@[match_pattern] abbrev PREVRANDAO  : Operation := .Block .PREVRANDAO
/-- Opcode `GASLIMIT`. -/
@[match_pattern] abbrev GASLIMIT    : Operation := .Block .GASLIMIT
/-- Opcode `CHAINID`. -/
@[match_pattern] abbrev CHAINID     : Operation := .Block .CHAINID
/-- Opcode `SELFBALANCE`. -/
@[match_pattern] abbrev SELFBALANCE : Operation := .Block .SELFBALANCE
/-- Opcode `BASEFEE`. -/
@[match_pattern] abbrev BASEFEE     : Operation := .Block .BASEFEE
/-- Opcode `BLOBHASH`. -/
@[match_pattern] abbrev BLOBHASH    : Operation := .Block .BLOBHASH
/-- Opcode `BLOBBASEFEE`. -/
@[match_pattern] abbrev BLOBBASEFEE : Operation := .Block .BLOBBASEFEE

/-- Opcode `POP`. -/
@[match_pattern] abbrev POP      : Operation := .StackMemFlow .POP
/-- Opcode `MLOAD`. -/
@[match_pattern] abbrev MLOAD    : Operation := .StackMemFlow .MLOAD
/-- Opcode `MSTORE`. -/
@[match_pattern] abbrev MSTORE   : Operation := .StackMemFlow .MSTORE
/-- Opcode `MSTORE8`. -/
@[match_pattern] abbrev MSTORE8  : Operation := .StackMemFlow .MSTORE8
/-- Opcode `SLOAD`. -/
@[match_pattern] abbrev SLOAD    : Operation := .StackMemFlow .SLOAD
/-- Opcode `SSTORE`. -/
@[match_pattern] abbrev SSTORE   : Operation := .StackMemFlow .SSTORE
/-- Opcode `JUMP`. -/
@[match_pattern] abbrev JUMP     : Operation := .StackMemFlow .JUMP
/-- Opcode `JUMPI`. -/
@[match_pattern] abbrev JUMPI    : Operation := .StackMemFlow .JUMPI
/-- Opcode `PC`. -/
@[match_pattern] abbrev PC       : Operation := .StackMemFlow .PC
/-- Opcode `JUMPDEST`. -/
@[match_pattern] abbrev JUMPDEST : Operation := .StackMemFlow .JUMPDEST
/-- Opcode `MSIZE`. -/
@[match_pattern] abbrev MSIZE    : Operation := .StackMemFlow .MSIZE
/-- Opcode `GAS`. -/
@[match_pattern] abbrev GAS      : Operation := .StackMemFlow .GAS
/-- Opcode `TLOAD`. -/
@[match_pattern] abbrev TLOAD    : Operation := .StackMemFlow .TLOAD
/-- Opcode `TSTORE`. -/
@[match_pattern] abbrev TSTORE   : Operation := .StackMemFlow .TSTORE
/-- Opcode `MCOPY`. -/
@[match_pattern] abbrev MCOPY    : Operation := .StackMemFlow .MCOPY

/-- EIP-8024 `DUPN` with immediate operand `n`. -/
@[match_pattern] abbrev DUPN (n : Fin 256) : Operation := .DupN ⟨n⟩
/-- EIP-8024 `SWAPN` with immediate operand `n`. -/
@[match_pattern] abbrev SWAPN (n : Fin 256) : Operation := .SwapN ⟨n⟩
/-- EIP-8024 `EXCHANGE` with packed immediate `b` (high nibble = `n`,
    low nibble = `m`). -/
@[match_pattern] abbrev EXCHANGE (b : Fin 256) : Operation := .Exchange ⟨b⟩

/-- Opcode `CREATE`. -/
@[match_pattern] abbrev CREATE       : Operation := .System .CREATE
/-- Opcode `CALL`. -/
@[match_pattern] abbrev CALL         : Operation := .System .CALL
/-- Opcode `CALLCODE`. -/
@[match_pattern] abbrev CALLCODE     : Operation := .System .CALLCODE
/-- Opcode `RETURN`. -/
@[match_pattern] abbrev RETURN       : Operation := .System .RETURN
/-- Opcode `DELEGATECALL`. -/
@[match_pattern] abbrev DELEGATECALL : Operation := .System .DELEGATECALL
/-- Opcode `CREATE2`. -/
@[match_pattern] abbrev CREATE2      : Operation := .System .CREATE2
/-- Opcode `STATICCALL`. -/
@[match_pattern] abbrev STATICCALL   : Operation := .System .STATICCALL
/-- Opcode `REVERT`. -/
@[match_pattern] abbrev REVERT       : Operation := .System .REVERT
/-- Opcode `INVALID`. -/
@[match_pattern] abbrev INVALID      : Operation := .System .INVALID
/-- Opcode `SELFDESTRUCT`. -/
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

-- The auto-derived `Repr` instances for the seven single-`Fin` op structs
-- all have an unused `prec : ℕ` argument inherited from `Repr.reprPrec`.
-- That's intrinsic to the `Repr` typeclass shape; we explicitly silence the
-- `unusedArguments` linter on each.
attribute [nolint unusedArguments]
  Operation.instReprPushOp.repr
  Operation.instReprDupOp.repr
  Operation.instReprSwapOp.repr
  Operation.instReprDupNOp.repr
  Operation.instReprSwapNOp.repr
  Operation.instReprExchangeOp.repr
  Operation.instReprLogOp.repr

-- `KeccakOps` has a single constructor (`KECCAK256`), so its auto-derived
-- `injEq` lemma is `KECCAK256 = KECCAK256 ↔ True`, which `simp` can already
-- prove. The lemma is harmless — silence `simpNF`.
attribute [nolint simpNF] Operation.Keccak.injEq

end EvmSemantics
