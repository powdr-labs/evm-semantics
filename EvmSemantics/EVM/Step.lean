module

public import EvmSemantics.EVM.State
public import EvmSemantics.EVM.Decode
public import EvmSemantics.EVM.Gas

/-!
`Step` — the small-step relation `Step : EVM.State → EVM.State → Prop`.

Each *success* rule has the same anatomy:

1. **Argument-polymorphism parameter** `arg : Option (UInt256 × Nat)` —
   the immediate-argument slot the decoder returns for PUSH-like ops
   (`none` for everything else). Quantifying it lets the soundness
   proof thread whatever the decoder produced without first proving
   an `argOpt = none` invariant.
2. **Decoding hypothesis** —
   `s.decoded = some (op, arg)` where `s.decoded = Decode.decodeAt s.executionEnv.code s.pc.toNat`.
3. **Running hypothesis** — `s.halt = .Running`.
4. **Static-mode hypothesis** (only for state-mutating ops) —
   `s.executionEnv.permitStateMutation = true`.
5. **Gas hypothesis** — `Gas.cost op ≤ s.gasAvailable.toNat`. Passed
   explicitly to `consumeGas` so the saturating `Nat` subtraction is
   provably safe — no truncation case-splits downstream.
6. **Stack-shape hypothesis** — `s.stack = a :: b :: rest` (or similar).
7. **Output-state computation** — the successor state given by record
   updaters / `s.consumeGas` / `s.replaceStackAndIncrPC`.

*Exception* rules (stack-underflow, out-of-gas, bad-jump, …) live in
the same inductive at the bottom of the file. They are parametric in
`op` where possible — one rule per failure mode rather than one per
(op, failure-mode) pair.
-/

@[expose] public section

namespace EvmSemantics

/-- Opaque Keccak-256 hash. The relational semantics never inspects the
    output value, only constrains it as the result of this abstract function.
    A concrete instantiation (e.g. for executable testing) can be supplied
    in a separate file. -/
opaque keccak256 : ByteArray → UInt256

/-- The hash of an account's bytecode (as used by EXTCODEHASH). -/
def Account.codeHash (acc : Account) : UInt256 := keccak256 acc.code

/-- The truthy interpretation of a UInt256 (zero is false, non-zero true). -/
def UInt256.isTrue (a : UInt256) : Prop := a.toNat ≠ 0

instance (a : UInt256) : Decidable (UInt256.isTrue a) :=
  inferInstanceAs (Decidable (a.toNat ≠ 0))

namespace EVM

namespace State

/-- Subtract `n` from the available gas. The proof `h` witnesses that the
    subtraction does not underflow; without it `consumeGas` would silently
    saturate at `0`, divorcing the function from its precondition. The
    proof is currently unused in the body (Nat subtraction is total) but
    keeps the call sites from accidentally subtracting too much. -/
@[nolint unusedArguments]
def consumeGas (s : State) (n : Nat) (_h : n ≤ s.gasAvailable.toNat) : State :=
  { s with gasAvailable := UInt256.ofNat (s.gasAvailable.toNat - n) }

/-- Convenience: the decoded operation (with its optional immediate) at
    the current `pc`. -/
def decoded (s : State) : Option (Operation × Option (UInt256 × Nat)) :=
  Decode.decodeAt s.executionEnv.code s.pc.toNat

end State

/-- The small-step relation. One constructor per opcode for the success
    path, plus generic exception constructors at the bottom. -/
inductive Step : State → State → Prop

  ----------------------------------------------------------------------------
  -- Stop, arithmetic.
  ----------------------------------------------------------------------------

  /-- ADD: pop `a`, `b`; push `a + b`. -/
  | add (s : State) (a b : UInt256) (rest : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.ADD, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .ADD ≤ s.gasAvailable.toNat)
        (h_stack   : s.stack = a :: b :: rest)
      : Step s ((s.consumeGas (Gas.cost .ADD) h_gas).replaceStackAndIncrPC ((a + b) :: rest))

  /-- MUL: pop `a`, `b`; push `a * b`. -/
  | mul (s : State) (a b : UInt256) (rest : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.MUL, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .MUL ≤ s.gasAvailable.toNat)
        (h_stack   : s.stack = a :: b :: rest)
      : Step s ((s.consumeGas (Gas.cost .MUL) h_gas).replaceStackAndIncrPC ((a * b) :: rest))

  /-- SUB: pop `a`, `b`; push `a - b`. -/
  | sub (s : State) (a b : UInt256) (rest : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.SUB, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .SUB ≤ s.gasAvailable.toNat)
        (h_stack   : s.stack = a :: b :: rest)
      : Step s ((s.consumeGas (Gas.cost .SUB) h_gas).replaceStackAndIncrPC ((a - b) :: rest))

  /-- DIV: pop `a`, `b`; push `a / b` (0 if `b = 0`). -/
  | div (s : State) (a b : UInt256) (rest : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.DIV, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .DIV ≤ s.gasAvailable.toNat)
        (h_stack   : s.stack = a :: b :: rest)
      : Step s ((s.consumeGas (Gas.cost .DIV) h_gas).replaceStackAndIncrPC ((a / b) :: rest))

  /-- SDIV: signed division. -/
  | sdiv (s : State) (a b : UInt256) (rest : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.SDIV, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .SDIV ≤ s.gasAvailable.toNat)
        (h_stack   : s.stack = a :: b :: rest)
      : Step s ((s.consumeGas (Gas.cost .SDIV) h_gas).replaceStackAndIncrPC
                  (UInt256.sdiv a b :: rest))

  /-- MOD: pop `a`, `b`; push `a % b` (0 if `b = 0`). -/
  | mod (s : State) (a b : UInt256) (rest : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.MOD, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .MOD ≤ s.gasAvailable.toNat)
        (h_stack   : s.stack = a :: b :: rest)
      : Step s ((s.consumeGas (Gas.cost .MOD) h_gas).replaceStackAndIncrPC ((a % b) :: rest))

  /-- SMOD: signed modulo. -/
  | smod (s : State) (a b : UInt256) (rest : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.SMOD, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .SMOD ≤ s.gasAvailable.toNat)
        (h_stack   : s.stack = a :: b :: rest)
      : Step s ((s.consumeGas (Gas.cost .SMOD) h_gas).replaceStackAndIncrPC
                  (UInt256.smod a b :: rest))

  /-- ADDMOD: pop `a`, `b`, `n`; push `(a + b) mod n`. -/
  | addmod (s : State) (a b n : UInt256) (rest : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.ADDMOD, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .ADDMOD ≤ s.gasAvailable.toNat)
        (h_stack   : s.stack = a :: b :: n :: rest)
      : Step s ((s.consumeGas (Gas.cost .ADDMOD) h_gas).replaceStackAndIncrPC
                  (UInt256.addMod a b n :: rest))

  /-- MULMOD: pop `a`, `b`, `n`; push `(a * b) mod n`. -/
  | mulmod (s : State) (a b n : UInt256) (rest : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.MULMOD, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .MULMOD ≤ s.gasAvailable.toNat)
        (h_stack   : s.stack = a :: b :: n :: rest)
      : Step s ((s.consumeGas (Gas.cost .MULMOD) h_gas).replaceStackAndIncrPC
                  (UInt256.mulMod a b n :: rest))

  /-- EXP: pop `a`, `b`; push `a ^ b mod 2^256`. -/
  | exp (s : State) (a b : UInt256) (rest : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.EXP, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .EXP ≤ s.gasAvailable.toNat)
        (h_stack   : s.stack = a :: b :: rest)
      : Step s ((s.consumeGas (Gas.cost .EXP) h_gas).replaceStackAndIncrPC
                  (UInt256.exp a b :: rest))

  /-- SIGNEXTEND: pop `b`, `x`; sign-extend `x` from byte index `b`. -/
  | signextend (s : State) (b x : UInt256) (rest : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.SIGNEXTEND, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .SIGNEXTEND ≤ s.gasAvailable.toNat)
        (h_stack   : s.stack = b :: x :: rest)
      : Step s ((s.consumeGas (Gas.cost .SIGNEXTEND) h_gas).replaceStackAndIncrPC
                  (UInt256.signExtend b x :: rest))

  ----------------------------------------------------------------------------
  -- Comparison & bitwise.
  ----------------------------------------------------------------------------

  | lt (s : State) (a b : UInt256) (rest : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.LT, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .LT ≤ s.gasAvailable.toNat)
        (h_stack   : s.stack = a :: b :: rest)
      : Step s ((s.consumeGas (Gas.cost .LT) h_gas).replaceStackAndIncrPC
                  (UInt256.lt a b :: rest))

  | gt (s : State) (a b : UInt256) (rest : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.GT, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .GT ≤ s.gasAvailable.toNat)
        (h_stack   : s.stack = a :: b :: rest)
      : Step s ((s.consumeGas (Gas.cost .GT) h_gas).replaceStackAndIncrPC
                  (UInt256.gt a b :: rest))

  | slt (s : State) (a b : UInt256) (rest : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.SLT, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .SLT ≤ s.gasAvailable.toNat)
        (h_stack   : s.stack = a :: b :: rest)
      : Step s ((s.consumeGas (Gas.cost .SLT) h_gas).replaceStackAndIncrPC
                  (UInt256.slt a b :: rest))

  | sgt (s : State) (a b : UInt256) (rest : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.SGT, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .SGT ≤ s.gasAvailable.toNat)
        (h_stack   : s.stack = a :: b :: rest)
      : Step s ((s.consumeGas (Gas.cost .SGT) h_gas).replaceStackAndIncrPC
                  (UInt256.sgt a b :: rest))

  | eq (s : State) (a b : UInt256) (rest : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.EQ, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .EQ ≤ s.gasAvailable.toNat)
        (h_stack   : s.stack = a :: b :: rest)
      : Step s ((s.consumeGas (Gas.cost .EQ) h_gas).replaceStackAndIncrPC
                  (UInt256.eq a b :: rest))

  | iszero (s : State) (a : UInt256) (rest : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.ISZERO, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .ISZERO ≤ s.gasAvailable.toNat)
        (h_stack   : s.stack = a :: rest)
      : Step s ((s.consumeGas (Gas.cost .ISZERO) h_gas).replaceStackAndIncrPC
                  (UInt256.isZero a :: rest))

  | and (s : State) (a b : UInt256) (rest : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.AND, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .AND ≤ s.gasAvailable.toNat)
        (h_stack   : s.stack = a :: b :: rest)
      : Step s ((s.consumeGas (Gas.cost .AND) h_gas).replaceStackAndIncrPC
                  (UInt256.land a b :: rest))

  | or (s : State) (a b : UInt256) (rest : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.OR, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .OR ≤ s.gasAvailable.toNat)
        (h_stack   : s.stack = a :: b :: rest)
      : Step s ((s.consumeGas (Gas.cost .OR) h_gas).replaceStackAndIncrPC
                  (UInt256.lor a b :: rest))

  | xor_ (s : State) (a b : UInt256) (rest : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.XOR, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .XOR ≤ s.gasAvailable.toNat)
        (h_stack   : s.stack = a :: b :: rest)
      : Step s ((s.consumeGas (Gas.cost .XOR) h_gas).replaceStackAndIncrPC
                  (UInt256.xor a b :: rest))

  | not (s : State) (a : UInt256) (rest : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.NOT, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .NOT ≤ s.gasAvailable.toNat)
        (h_stack   : s.stack = a :: rest)
      : Step s ((s.consumeGas (Gas.cost .NOT) h_gas).replaceStackAndIncrPC
                  (UInt256.lnot a :: rest))

  | byte_ (s : State) (i x : UInt256) (rest : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.BYTE, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .BYTE ≤ s.gasAvailable.toNat)
        (h_stack   : s.stack = i :: x :: rest)
      : Step s ((s.consumeGas (Gas.cost .BYTE) h_gas).replaceStackAndIncrPC
                  (UInt256.byteAt i x :: rest))

  | shl (s : State) (shift v : UInt256) (rest : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.SHL, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .SHL ≤ s.gasAvailable.toNat)
        (h_stack   : s.stack = shift :: v :: rest)
      : Step s ((s.consumeGas (Gas.cost .SHL) h_gas).replaceStackAndIncrPC
                  (UInt256.shiftLeft v shift :: rest))

  | shr (s : State) (shift v : UInt256) (rest : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.SHR, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .SHR ≤ s.gasAvailable.toNat)
        (h_stack   : s.stack = shift :: v :: rest)
      : Step s ((s.consumeGas (Gas.cost .SHR) h_gas).replaceStackAndIncrPC
                  (UInt256.shiftRight v shift :: rest))

  | sar (s : State) (shift v : UInt256) (rest : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.SAR, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .SAR ≤ s.gasAvailable.toNat)
        (h_stack   : s.stack = shift :: v :: rest)
      : Step s ((s.consumeGas (Gas.cost .SAR) h_gas).replaceStackAndIncrPC
                  (UInt256.sar v shift :: rest))

  ----------------------------------------------------------------------------
  -- KECCAK256.
  ----------------------------------------------------------------------------

  /-- KECCAK256: pop offset, size; push hash of memory[offset..offset+size]. -/
  | keccak256 (s : State) (offset size : UInt256) (rest : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.KECCAK256, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .KECCAK256 ≤ s.gasAvailable.toNat)
        (h_stack   : s.stack = offset :: size :: rest)
      : Step s
          (let bytes := MachineState.readPadded s.memory offset.toNat size.toNat
           (s.consumeGas (Gas.cost .KECCAK256) h_gas).replaceStackAndIncrPC
             (EvmSemantics.keccak256 bytes :: rest))

  ----------------------------------------------------------------------------
  -- Environment reads.
  ----------------------------------------------------------------------------

  | address (s : State)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.ADDRESS, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .ADDRESS ≤ s.gasAvailable.toNat)
      : Step s ((s.consumeGas (Gas.cost .ADDRESS) h_gas).replaceStackAndIncrPC
                  (s.executionEnv.codeOwner.toUInt256 :: s.stack))

  | balance (s : State) (addr : UInt256) (rest : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.BALANCE, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .BALANCE ≤ s.gasAvailable.toNat)
        (h_stack   : s.stack = addr :: rest)
      : Step s ((s.consumeGas (Gas.cost .BALANCE) h_gas).replaceStackAndIncrPC
                  ((s.accountMap (AccountAddress.ofUInt256 addr)).balance :: rest))

  | origin (s : State)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.ORIGIN, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .ORIGIN ≤ s.gasAvailable.toNat)
      : Step s ((s.consumeGas (Gas.cost .ORIGIN) h_gas).replaceStackAndIncrPC
                  (s.executionEnv.sender.toUInt256 :: s.stack))

  | caller (s : State)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.CALLER, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .CALLER ≤ s.gasAvailable.toNat)
      : Step s ((s.consumeGas (Gas.cost .CALLER) h_gas).replaceStackAndIncrPC
                  (s.executionEnv.source.toUInt256 :: s.stack))

  | callvalue (s : State)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.CALLVALUE, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .CALLVALUE ≤ s.gasAvailable.toNat)
      : Step s ((s.consumeGas (Gas.cost .CALLVALUE) h_gas).replaceStackAndIncrPC
                  (s.executionEnv.weiValue :: s.stack))

  /-- CALLDATALOAD: pop `i`; push 32 bytes of calldata starting at `i`,
      zero-padded if past the end. -/
  | calldataload (s : State) (i : UInt256) (rest : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.CALLDATALOAD, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .CALLDATALOAD ≤ s.gasAvailable.toNat)
        (h_stack   : s.stack = i :: rest)
      : Step s
          (let bs := MachineState.readPadded s.executionEnv.calldata i.toNat 32
           let word : Nat := bs.toList.foldl (fun acc b => acc * 256 + b.toNat) 0
           (s.consumeGas (Gas.cost .CALLDATALOAD) h_gas).replaceStackAndIncrPC
             (UInt256.ofNat word :: rest))

  | calldatasize (s : State)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.CALLDATASIZE, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .CALLDATASIZE ≤ s.gasAvailable.toNat)
      : Step s ((s.consumeGas (Gas.cost .CALLDATASIZE) h_gas).replaceStackAndIncrPC
                  (UInt256.ofNat s.executionEnv.calldata.size :: s.stack))

  /-- CALLDATACOPY: pop destOffset, srcOffset, size; copy calldata to memory. -/
  | calldatacopy (s : State) (destOff srcOff sz : UInt256) (rest : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.CALLDATACOPY, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .CALLDATACOPY ≤ s.gasAvailable.toNat)
        (h_stack   : s.stack = destOff :: srcOff :: sz :: rest)
      : Step s
          (let bytes := MachineState.readPadded s.executionEnv.calldata srcOff.toNat sz.toNat
           let μ' : MachineState :=
             { s.toMachineState with
                 memory := MachineState.writeBytes s.memory bytes destOff.toNat
                 activeWords := UInt256.ofNat
                                 (MachineState.activeWordsAfter
                                   s.activeWords.toNat destOff.toNat sz.toNat) }
           { (s.consumeGas (Gas.cost .CALLDATACOPY) h_gas) with toMachineState := μ' }
             |>.replaceStackAndIncrPC rest)

  | codesize (s : State)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.CODESIZE, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .CODESIZE ≤ s.gasAvailable.toNat)
      : Step s ((s.consumeGas (Gas.cost .CODESIZE) h_gas).replaceStackAndIncrPC
                  (UInt256.ofNat s.executionEnv.code.size :: s.stack))

  /-- CODECOPY: pop destOffset, srcOffset, size; copy current code to memory. -/
  | codecopy (s : State) (destOff srcOff sz : UInt256) (rest : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.CODECOPY, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .CODECOPY ≤ s.gasAvailable.toNat)
        (h_stack   : s.stack = destOff :: srcOff :: sz :: rest)
      : Step s
          (let bytes := MachineState.readPadded s.executionEnv.code srcOff.toNat sz.toNat
           let μ' : MachineState :=
             { s.toMachineState with
                 memory := MachineState.writeBytes s.memory bytes destOff.toNat
                 activeWords := UInt256.ofNat
                                 (MachineState.activeWordsAfter
                                   s.activeWords.toNat destOff.toNat sz.toNat) }
           { (s.consumeGas (Gas.cost .CODECOPY) h_gas) with toMachineState := μ' }
             |>.replaceStackAndIncrPC rest)

  | gasprice (s : State)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.GASPRICE, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .GASPRICE ≤ s.gasAvailable.toNat)
      : Step s ((s.consumeGas (Gas.cost .GASPRICE) h_gas).replaceStackAndIncrPC
                  (s.executionEnv.gasPrice :: s.stack))

  | extcodesize (s : State) (addr : UInt256) (rest : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.EXTCODESIZE, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .EXTCODESIZE ≤ s.gasAvailable.toNat)
        (h_stack   : s.stack = addr :: rest)
      : Step s ((s.consumeGas (Gas.cost .EXTCODESIZE) h_gas).replaceStackAndIncrPC
                  (UInt256.ofNat (s.accountMap (AccountAddress.ofUInt256 addr)).code.size :: rest))

  /-- EXTCODECOPY: pop addr, destOffset, srcOffset, size; copy external
      code bytes to memory. -/
  | extcodecopy (s : State) (addr destOff srcOff sz : UInt256) (rest : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.EXTCODECOPY, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .EXTCODECOPY ≤ s.gasAvailable.toNat)
        (h_stack   : s.stack = addr :: destOff :: srcOff :: sz :: rest)
      : Step s
          (let extCode := (s.accountMap (AccountAddress.ofUInt256 addr)).code
           let bytes := MachineState.readPadded extCode srcOff.toNat sz.toNat
           let μ' : MachineState :=
             { s.toMachineState with
                 memory := MachineState.writeBytes s.memory bytes destOff.toNat
                 activeWords := UInt256.ofNat
                                 (MachineState.activeWordsAfter
                                   s.activeWords.toNat destOff.toNat sz.toNat) }
           { (s.consumeGas (Gas.cost .EXTCODECOPY) h_gas) with toMachineState := μ' }
             |>.replaceStackAndIncrPC rest)

  | returndatasize (s : State)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.RETURNDATASIZE, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .RETURNDATASIZE ≤ s.gasAvailable.toNat)
      : Step s ((s.consumeGas (Gas.cost .RETURNDATASIZE) h_gas).replaceStackAndIncrPC
                  (UInt256.ofNat s.returnData.size :: s.stack))

  /-- RETURNDATACOPY: pop destOffset, srcOffset, size; copy returndata to memory.
      Out-of-bounds reads raise `InvalidMemoryAccess` (handled in Phase 5). -/
  | returndatacopy (s : State) (destOff srcOff sz : UInt256) (rest : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.RETURNDATACOPY, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .RETURNDATACOPY ≤ s.gasAvailable.toNat)
        (h_stack   : s.stack = destOff :: srcOff :: sz :: rest)
        (h_inbounds : srcOff.toNat + sz.toNat ≤ s.returnData.size)
      : Step s
          (let bytes := MachineState.readPadded s.returnData srcOff.toNat sz.toNat
           let μ' : MachineState :=
             { s.toMachineState with
                 memory := MachineState.writeBytes s.memory bytes destOff.toNat
                 activeWords := UInt256.ofNat
                                 (MachineState.activeWordsAfter
                                   s.activeWords.toNat destOff.toNat sz.toNat) }
           { (s.consumeGas (Gas.cost .RETURNDATACOPY) h_gas) with toMachineState := μ' }
             |>.replaceStackAndIncrPC rest)

  | extcodehash (s : State) (addr : UInt256) (rest : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.EXTCODEHASH, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .EXTCODEHASH ≤ s.gasAvailable.toNat)
        (h_stack   : s.stack = addr :: rest)
      : Step s ((s.consumeGas (Gas.cost .EXTCODEHASH) h_gas).replaceStackAndIncrPC
                  ((s.accountMap (AccountAddress.ofUInt256 addr)).codeHash :: rest))

  ----------------------------------------------------------------------------
  -- Block-context reads.
  ----------------------------------------------------------------------------

  | blockhash (s : State) (n : UInt256) (rest : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.BLOCKHASH, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .BLOCKHASH ≤ s.gasAvailable.toNat)
        (h_stack   : s.stack = n :: rest)
      : Step s ((s.consumeGas (Gas.cost .BLOCKHASH) h_gas).replaceStackAndIncrPC
                  (s.executionEnv.header.blockHash n :: rest))

  | coinbase (s : State)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.COINBASE, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .COINBASE ≤ s.gasAvailable.toNat)
      : Step s ((s.consumeGas (Gas.cost .COINBASE) h_gas).replaceStackAndIncrPC
                  (s.executionEnv.header.coinbase.toUInt256 :: s.stack))

  | timestamp (s : State)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.TIMESTAMP, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .TIMESTAMP ≤ s.gasAvailable.toNat)
      : Step s ((s.consumeGas (Gas.cost .TIMESTAMP) h_gas).replaceStackAndIncrPC
                  (s.executionEnv.header.timestamp :: s.stack))

  | number (s : State)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.NUMBER, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .NUMBER ≤ s.gasAvailable.toNat)
      : Step s ((s.consumeGas (Gas.cost .NUMBER) h_gas).replaceStackAndIncrPC
                  (s.executionEnv.header.number :: s.stack))

  | prevrandao (s : State)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.PREVRANDAO, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .PREVRANDAO ≤ s.gasAvailable.toNat)
      : Step s ((s.consumeGas (Gas.cost .PREVRANDAO) h_gas).replaceStackAndIncrPC
                  (s.executionEnv.header.prevRandao :: s.stack))

  | gaslimit (s : State)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.GASLIMIT, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .GASLIMIT ≤ s.gasAvailable.toNat)
      : Step s ((s.consumeGas (Gas.cost .GASLIMIT) h_gas).replaceStackAndIncrPC
                  (s.executionEnv.header.gasLimit :: s.stack))

  | chainid (s : State)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.CHAINID, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .CHAINID ≤ s.gasAvailable.toNat)
      : Step s ((s.consumeGas (Gas.cost .CHAINID) h_gas).replaceStackAndIncrPC
                  (s.executionEnv.header.chainId :: s.stack))

  | selfbalance (s : State)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.SELFBALANCE, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .SELFBALANCE ≤ s.gasAvailable.toNat)
      : Step s ((s.consumeGas (Gas.cost .SELFBALANCE) h_gas).replaceStackAndIncrPC
                  ((s.accountMap s.executionEnv.codeOwner).balance :: s.stack))

  | basefee (s : State)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.BASEFEE, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .BASEFEE ≤ s.gasAvailable.toNat)
      : Step s ((s.consumeGas (Gas.cost .BASEFEE) h_gas).replaceStackAndIncrPC
                  (s.executionEnv.header.baseFeePerGas :: s.stack))

  | blobhash (s : State) (i : UInt256) (rest : Stack UInt256) (h : UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.BLOBHASH, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .BLOBHASH ≤ s.gasAvailable.toNat)
        (h_stack   : s.stack = i :: rest)
        (h_get     : s.executionEnv.blobVersionedHashes[i.toNat]? = some h)
      : Step s ((s.consumeGas (Gas.cost .BLOBHASH) h_gas).replaceStackAndIncrPC
                  (h :: rest))

  /-- BLOBHASH when index is out of range — push 0. -/
  | blobhash_oob (s : State) (i : UInt256) (rest : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.BLOBHASH, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .BLOBHASH ≤ s.gasAvailable.toNat)
        (h_stack   : s.stack = i :: rest)
        (h_oob     : s.executionEnv.blobVersionedHashes[i.toNat]? = none)
      : Step s ((s.consumeGas (Gas.cost .BLOBHASH) h_gas).replaceStackAndIncrPC
                  (⟨0⟩ :: rest))

  | blobbasefee (s : State)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.BLOBBASEFEE, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .BLOBBASEFEE ≤ s.gasAvailable.toNat)
      : Step s ((s.consumeGas (Gas.cost .BLOBBASEFEE) h_gas).replaceStackAndIncrPC
                  (s.executionEnv.header.blobBaseFee :: s.stack))

  ----------------------------------------------------------------------------
  -- Stack manipulation: POP, PUSHk, DUPn, SWAPn.
  ----------------------------------------------------------------------------

  | pop (s : State) (a : UInt256) (rest : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.POP, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .POP ≤ s.gasAvailable.toNat)
        (h_stack   : s.stack = a :: rest)
      : Step s ((s.consumeGas (Gas.cost .POP) h_gas).replaceStackAndIncrPC rest)

  /-- PUSH0: push `0`. -/
  | push0 (s : State)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.Push ⟨0, by decide⟩, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost (.Push ⟨0, by decide⟩) ≤ s.gasAvailable.toNat)
      : Step s ((s.consumeGas (Gas.cost (.Push ⟨0, by decide⟩)) h_gas).replaceStackAndIncrPC
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
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost (.Push ⟨k, k.isLt⟩) ≤ s.gasAvailable.toNat)
      : Step s ((s.consumeGas (Gas.cost (.Push ⟨k, k.isLt⟩)) h_gas).replaceStackAndIncrPC
                  (data :: s.stack) (pcΔ := immWidth + 1))

  /-- DUPn: copy `stack[n]` (0-indexed from top) to the top. -/
  | dup (s : State) (n : Fin 16) (v : UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.Dup ⟨n⟩, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost (.Dup ⟨n⟩) ≤ s.gasAvailable.toNat)
        (h_get     : s.stack[n.val]? = some v)
      : Step s ((s.consumeGas (Gas.cost (.Dup ⟨n⟩)) h_gas).replaceStackAndIncrPC (v :: s.stack))

  /-- SWAPn: swap top with `stack[n+1]`. -/
  | swap (s : State) (n : Fin 16) (stk' : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.Swap ⟨n⟩, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost (.Swap ⟨n⟩) ≤ s.gasAvailable.toNat)
        (h_swap    : s.stack.exchange 0 (n.val + 1) = some stk')
      : Step s ((s.consumeGas (Gas.cost (.Swap ⟨n⟩)) h_gas).replaceStackAndIncrPC stk')

  ----------------------------------------------------------------------------
  -- Memory.
  ----------------------------------------------------------------------------

  /-- MLOAD: pop offset; push the 32-byte word at memory[offset]. -/
  | mload (s : State) (offset : UInt256) (rest : Stack UInt256)
        (v : UInt256) (μ' : MachineState)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.MLOAD, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .MLOAD ≤ s.gasAvailable.toNat)
        (h_stack   : s.stack = offset :: rest)
        (h_load    : MachineState.mload s.toMachineState offset = (v, μ'))
      : Step s ({ (s.consumeGas (Gas.cost .MLOAD) h_gas) with toMachineState := μ' }
                  |>.replaceStackAndIncrPC (v :: rest))

  /-- MSTORE: pop offset, value; write `value` as 32 bytes at memory[offset]. -/
  | mstore (s : State) (offset value : UInt256) (rest : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.MSTORE, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .MSTORE ≤ s.gasAvailable.toNat)
        (h_stack   : s.stack = offset :: value :: rest)
      : Step s
          (let μ' := MachineState.mstore s.toMachineState offset value
           { (s.consumeGas (Gas.cost .MSTORE) h_gas) with toMachineState := μ' }
             |>.replaceStackAndIncrPC rest)

  /-- MSTORE8: pop offset, value; write the low byte of `value` at memory[offset]. -/
  | mstore8 (s : State) (offset value : UInt256) (rest : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.MSTORE8, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .MSTORE8 ≤ s.gasAvailable.toNat)
        (h_stack   : s.stack = offset :: value :: rest)
      : Step s
          (let μ' := MachineState.mstore8 s.toMachineState offset value
           { (s.consumeGas (Gas.cost .MSTORE8) h_gas) with toMachineState := μ' }
             |>.replaceStackAndIncrPC rest)

  | msize (s : State)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.MSIZE, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .MSIZE ≤ s.gasAvailable.toNat)
      : Step s ((s.consumeGas (Gas.cost .MSIZE) h_gas).replaceStackAndIncrPC
                  (MachineState.msize s.toMachineState :: s.stack))

  /-- MCOPY: pop destOffset, srcOffset, size; copy memory[src..src+sz] to dest. -/
  | mcopy (s : State) (destOff srcOff sz : UInt256) (rest : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.MCOPY, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .MCOPY ≤ s.gasAvailable.toNat)
        (h_stack   : s.stack = destOff :: srcOff :: sz :: rest)
      : Step s
          (let μ' := MachineState.mcopy s.toMachineState destOff srcOff sz
           { (s.consumeGas (Gas.cost .MCOPY) h_gas) with toMachineState := μ' }
             |>.replaceStackAndIncrPC rest)

  ----------------------------------------------------------------------------
  -- Storage (persistent and transient).
  ----------------------------------------------------------------------------

  /-- SLOAD: pop key; push storage[key] from the executing contract. -/
  | sload (s : State) (key : UInt256) (rest : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.SLOAD, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .SLOAD ≤ s.gasAvailable.toNat)
        (h_stack   : s.stack = key :: rest)
      : Step s ((s.consumeGas (Gas.cost .SLOAD) h_gas).replaceStackAndIncrPC
                  (((s.accountMap s.executionEnv.codeOwner).storage key) :: rest))

  /-- SSTORE: pop key, value; write storage[key] := value. Requires
      static-mode permission. -/
  | sstore (s : State) (key value : UInt256) (rest : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.SSTORE, arg))
        (h_running : s.halt = .Running)
        (h_perm    : s.executionEnv.permitStateMutation = true)
        (h_gas     : Gas.cost .SSTORE ≤ s.gasAvailable.toNat)
        (h_stack   : s.stack = key :: value :: rest)
      : Step s
          (let addr := s.executionEnv.codeOwner
           let acc  := s.accountMap addr
           let acc' := { acc with storage := acc.storage.set key value }
           let σ'   := s.accountMap.set addr acc'
           { (s.consumeGas (Gas.cost .SSTORE) h_gas) with accountMap := σ' }
             |>.replaceStackAndIncrPC rest)

  /-- TLOAD: like SLOAD but reads from transient storage. -/
  | tload (s : State) (key : UInt256) (rest : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.TLOAD, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .TLOAD ≤ s.gasAvailable.toNat)
        (h_stack   : s.stack = key :: rest)
      : Step s ((s.consumeGas (Gas.cost .TLOAD) h_gas).replaceStackAndIncrPC
                  (((s.accountMap s.executionEnv.codeOwner).tstorage key) :: rest))

  /-- TSTORE: like SSTORE but writes to transient storage. -/
  | tstore (s : State) (key value : UInt256) (rest : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.TSTORE, arg))
        (h_running : s.halt = .Running)
        (h_perm    : s.executionEnv.permitStateMutation = true)
        (h_gas     : Gas.cost .TSTORE ≤ s.gasAvailable.toNat)
        (h_stack   : s.stack = key :: value :: rest)
      : Step s
          (let addr := s.executionEnv.codeOwner
           let acc  := s.accountMap addr
           let acc' := { acc with tstorage := acc.tstorage.set key value }
           let σ'   := s.accountMap.set addr acc'
           { (s.consumeGas (Gas.cost .TSTORE) h_gas) with accountMap := σ' }
             |>.replaceStackAndIncrPC rest)

  ----------------------------------------------------------------------------
  -- Control flow: JUMP, JUMPI, JUMPDEST, PC, GAS.
  ----------------------------------------------------------------------------

  /-- JUMP: pop destination; set `pc := dest` if the destination is a JUMPDEST. -/
  | jump (s : State) (dest : UInt256) (rest : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.JUMP, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .JUMP ≤ s.gasAvailable.toNat)
        (h_stack   : s.stack = dest :: rest)
        (h_valid   : Decode.decodeAt s.executionEnv.code dest.toNat
                       = some (.JUMPDEST, none))
      : Step s { (s.consumeGas (Gas.cost .JUMP) h_gas) with pc := dest, stack := rest }

  /-- JUMPI (taken): pop dest, cond; if `cond ≠ 0` and dest is a JUMPDEST,
      set `pc := dest`. -/
  | jumpi_taken (s : State) (dest cond : UInt256) (rest : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.JUMPI, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .JUMPI ≤ s.gasAvailable.toNat)
        (h_stack   : s.stack = dest :: cond :: rest)
        (h_cond    : UInt256.isTrue cond)
        (h_valid   : Decode.decodeAt s.executionEnv.code dest.toNat
                       = some (.JUMPDEST, none))
      : Step s { (s.consumeGas (Gas.cost .JUMPI) h_gas) with pc := dest, stack := rest }

  /-- JUMPI (not taken): pop dest, cond; if `cond = 0`, fall through to `pc + 1`. -/
  | jumpi_notTaken (s : State) (dest cond : UInt256) (rest : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.JUMPI, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .JUMPI ≤ s.gasAvailable.toNat)
        (h_stack   : s.stack = dest :: cond :: rest)
        (h_cond    : ¬ UInt256.isTrue cond)
      : Step s ((s.consumeGas (Gas.cost .JUMPI) h_gas).replaceStackAndIncrPC rest)

  | pc (s : State)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.PC, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .PC ≤ s.gasAvailable.toNat)
      : Step s ((s.consumeGas (Gas.cost .PC) h_gas).replaceStackAndIncrPC
                  (s.pc :: s.stack))

  | gas (s : State)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.GAS, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .GAS ≤ s.gasAvailable.toNat)
      : Step s ((s.consumeGas (Gas.cost .GAS) h_gas).replaceStackAndIncrPC
                  (s.gasAvailable :: s.stack))

  | jumpdest (s : State)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.JUMPDEST, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .JUMPDEST ≤ s.gasAvailable.toNat)
      : Step s ((s.consumeGas (Gas.cost .JUMPDEST) h_gas).incrPC)

  ----------------------------------------------------------------------------
  -- Halts: STOP, RETURN, REVERT.
  ----------------------------------------------------------------------------

  | stop (s : State)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.STOP, arg))
        (h_running : s.halt = .Running)
      : Step s { s with halt := .Success, hReturn := .empty }

  | return_ (s : State) (offset size : UInt256) (rest : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.RETURN, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .RETURN ≤ s.gasAvailable.toNat)
        (h_stack   : s.stack = offset :: size :: rest)
      : Step s
          (let bs := MachineState.readPadded s.memory offset.toNat size.toNat
           { (s.consumeGas (Gas.cost .RETURN) h_gas) with
              halt := .Returned, hReturn := bs, stack := rest })

  | revert (s : State) (offset size : UInt256) (rest : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.REVERT, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .REVERT ≤ s.gasAvailable.toNat)
        (h_stack   : s.stack = offset :: size :: rest)
      : Step s
          (let bs := MachineState.readPadded s.memory offset.toNat size.toNat
           { (s.consumeGas (Gas.cost .REVERT) h_gas) with
              halt := .Reverted, hReturn := bs, stack := rest })

  ----------------------------------------------------------------------------
  -- Logging: LOG0–LOG4 (parametric over topic count).
  ----------------------------------------------------------------------------

  /-- LOG `n`: pop offset, size, then `n` topics; append a log entry. -/
  | log (s : State) (n : Fin 5) (offset size : UInt256)
        (topics : List UInt256) (rest : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.Log ⟨n⟩, arg))
        (h_running  : s.halt = .Running)
        (h_perm     : s.executionEnv.permitStateMutation = true)
        (h_gas      : Gas.cost (.Log ⟨n⟩) ≤ s.gasAvailable.toNat)
        (h_topics_n : topics.length = n.val)
        (h_stack    : s.stack = offset :: size :: topics ++ rest)
      : Step s
          (let entry : LogEntry :=
             { address := s.executionEnv.codeOwner
               topics  := topics.toArray
               data    := MachineState.readPadded s.memory offset.toNat size.toNat }
           { (s.consumeGas (Gas.cost (.Log ⟨n⟩)) h_gas) with
              substate := s.substate.appendLog entry }
             |>.replaceStackAndIncrPC rest)

  ----------------------------------------------------------------------------
  -- EIP-8024: DUPN, SWAPN, EXCHANGE.
  ----------------------------------------------------------------------------

  /-- DUPN with immediate `n`: duplicate `stack[n]` to the top. PC += 2. -/
  | dupN (s : State) (n : Fin 256) (v : UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.DupN ⟨n⟩, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost (.DupN ⟨n⟩) ≤ s.gasAvailable.toNat)
        (h_get     : s.stack[n.val]? = some v)
      : Step s ((s.consumeGas (Gas.cost (.DupN ⟨n⟩)) h_gas).replaceStackAndIncrPC
                  (v :: s.stack) (pcΔ := 2))

  /-- SWAPN with immediate `n`: swap top with `stack[n+1]`. PC += 2. -/
  | swapN (s : State) (n : Fin 256) (stk' : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.SwapN ⟨n⟩, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost (.SwapN ⟨n⟩) ≤ s.gasAvailable.toNat)
        (h_swap    : s.stack.exchange 0 (n.val + 1) = some stk')
      : Step s ((s.consumeGas (Gas.cost (.SwapN ⟨n⟩)) h_gas).replaceStackAndIncrPC
                  stk' (pcΔ := 2))

  /-- EXCHANGE with packed immediate `b`: swap `stack[n+1]` and `stack[m+1]`
      where `n = b >>> 4` and `m = b &&& 0xf`. PC += 2. -/
  | exchange (s : State) (b : Fin 256) (stk' : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.Exchange ⟨b⟩, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost (.Exchange ⟨b⟩) ≤ s.gasAvailable.toNat)
        (h_swap    : s.stack.exchange
                      (b.val >>> 4 + 1)
                      ((b.val &&& 0xf) + 1) = some stk')
      : Step s ((s.consumeGas (Gas.cost (.Exchange ⟨b⟩)) h_gas).replaceStackAndIncrPC
                  stk' (pcΔ := 2))

  ----------------------------------------------------------------------------
  -- Exception rules.
  --
  -- These constructors halt the frame with `halt := .Exception e`. They are
  -- written *parametrically* over the operation where possible — one rule
  -- per failure mode rather than one per (op, failure-mode) pair. The
  -- non-overlap between success and exception rules comes from disjoint
  -- hypotheses (`Gas.cost op ≤ gas` vs. `gas < Gas.cost op`, etc.).
  --
  -- Several exception rules may fire simultaneously from the same state
  -- (e.g. underflow AND out-of-gas). The relational semantics is
  -- *non-deterministic* about which exception is reported. A deterministic
  -- check order can be layered on top later if desired.
  ----------------------------------------------------------------------------

  /-- Decode failure: the byte at the PC isn't a recognised opcode. -/
  | decodeFailure (s : State)
        (h_running : s.halt = .Running)
        (h_none    : s.decoded = none)
      : Step s (s.haltWith .InvalidInstruction)

  /-- The explicit `INVALID` opcode (`0xfe`). -/
  | invalidOpcode (s : State)
        (h_running : s.halt = .Running)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.INVALID, arg))
      : Step s (s.haltWith .InvalidInstruction)

  /-- Insufficient gas to pay for the decoded operation's cost. -/
  | outOfGas (s : State) (op : Operation) (arg : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (op, arg))
        (h_running : s.halt = .Running)
        (h_gas     : s.gasAvailable.toNat < Gas.cost op)
      : Step s (s.haltWith .OutOfGas)

  /-- Stack has fewer items than the operation requires to pop. -/
  | stackUnderflow (s : State) (op : Operation) (arg : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (op, arg))
        (h_running : s.halt = .Running)
        (h_under   : s.stack.length < op.popArity)
      : Step s (s.haltWith .StackUnderflow)

  /-- Executing this operation would grow the stack beyond the 1024-item
      EVM limit. Requires `popArity ≤ length` so the subtraction is well
      defined. -/
  | stackOverflow (s : State) (op : Operation) (arg : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (op, arg))
        (h_running : s.halt = .Running)
        (h_pop_ok  : op.popArity ≤ s.stack.length)
        (h_over    : s.stack.length - op.popArity + op.pushArity > 1024)
      : Step s (s.haltWith .StackOverflow)

  /-- State-mutating operation attempted while
      `executionEnv.permitStateMutation = false`. -/
  | staticModeViolation (s : State) (op : Operation) (arg : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (op, arg))
        (h_running : s.halt = .Running)
        (h_mut     : op.isStateMutating = true)
        (h_perm    : s.executionEnv.permitStateMutation = false)
      : Step s (s.haltWith .StaticModeViolation)

  /-- JUMP to a destination that is not a `JUMPDEST` (or off the code). -/
  | jumpBadDest (s : State) (dest : UInt256) (rest : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.JUMP, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .JUMP ≤ s.gasAvailable.toNat)
        (h_stack   : s.stack = dest :: rest)
        (h_bad     : Decode.decodeAt s.executionEnv.code dest.toNat ≠ some (.JUMPDEST, none))
      : Step s (s.haltWith .BadJumpDestination)

  /-- JUMPI with `cond ≠ 0` but destination is not a `JUMPDEST`. -/
  | jumpiBadDest (s : State) (dest cond : UInt256) (rest : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.JUMPI, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .JUMPI ≤ s.gasAvailable.toNat)
        (h_stack   : s.stack = dest :: cond :: rest)
        (h_cond    : UInt256.isTrue cond)
        (h_bad     : Decode.decodeAt s.executionEnv.code dest.toNat ≠ some (.JUMPDEST, none))
      : Step s (s.haltWith .BadJumpDestination)

  /-- RETURNDATACOPY with `srcOffset + size > returnData.size`. -/
  | returndatacopyOob (s : State) (destOff srcOff sz : UInt256) (rest : Stack UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.RETURNDATACOPY, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.cost .RETURNDATACOPY ≤ s.gasAvailable.toNat)
        (h_stack   : s.stack = destOff :: srcOff :: sz :: rest)
        (h_oob     : srcOff.toNat + sz.toNat > s.returnData.size)
      : Step s (s.haltWith .InvalidMemoryAccess)

end EVM
end EvmSemantics
