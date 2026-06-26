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
5. **Gas hypothesis** — `Gas.baseCost s.fork op ≤ s.gasAvailable`. Passed
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

namespace List

/-- Swap the elements at indices `i` and `j` (zero-indexed from the head
    of the list, i.e. the top of the stack). Returns `none` if either
    index is out of range. Used by the `SWAP` / `SWAPN` / `EXCHANGE` rules. -/
def exchange (s : List α) (i j : Nat) : Option (List α) := do
  let xi ← s[i]?
  let xj ← s[j]?
  return (s.set i xj).set j xi

end List

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
def consumeGas (s : State) (n : Nat) (_h : n ≤ s.gasAvailable) : State :=
  { s with gasAvailable := s.gasAvailable - n }

/-- Convenience shorthand for the active fork.
    `abbrev` so it unfolds transparently in proofs. -/
abbrev fork (s : State) : Fork := s.executionEnv.fork

/-- `s` has enough gas to pay the memory-expansion cost for touching
    `[offset, offset+sz)`. Used as the precondition of `consumeMemExp` and
    as the `h_mem` hypothesis on the memory-touching `Step` rules. -/
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
  | add (s : State) (a b : UInt256) (rest : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.ADD, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .ADD ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: b :: rest)
      : Step s ((s.consumeGas (Gas.baseCost s.fork .ADD) h_gas).replaceStackAndIncrPC
                  ((a + b) :: rest))

  /-- MUL: pop `a`, `b`; push `a * b`. -/
  | mul (s : State) (a b : UInt256) (rest : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.MUL, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .MUL ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: b :: rest)
      : Step s ((s.consumeGas (Gas.baseCost s.fork .MUL) h_gas).replaceStackAndIncrPC
                  ((a * b) :: rest))

  /-- SUB: pop `a`, `b`; push `a - b`. -/
  | sub (s : State) (a b : UInt256) (rest : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.SUB, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .SUB ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: b :: rest)
      : Step s ((s.consumeGas (Gas.baseCost s.fork .SUB) h_gas).replaceStackAndIncrPC
                  ((a - b) :: rest))

  /-- DIV: pop `a`, `b`; push `a / b` (0 if `b = 0`). -/
  | div (s : State) (a b : UInt256) (rest : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.DIV, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .DIV ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: b :: rest)
      : Step s ((s.consumeGas (Gas.baseCost s.fork .DIV) h_gas).replaceStackAndIncrPC
                  ((a / b) :: rest))

  /-- SDIV: signed division. -/
  | sdiv (s : State) (a b : UInt256) (rest : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.SDIV, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .SDIV ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: b :: rest)
      : Step s ((s.consumeGas (Gas.baseCost s.fork .SDIV) h_gas).replaceStackAndIncrPC
                  (UInt256.sdiv a b :: rest))

  /-- MOD: pop `a`, `b`; push `a % b` (0 if `b = 0`). -/
  | mod (s : State) (a b : UInt256) (rest : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.MOD, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .MOD ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: b :: rest)
      : Step s ((s.consumeGas (Gas.baseCost s.fork .MOD) h_gas).replaceStackAndIncrPC
                  ((a % b) :: rest))

  /-- SMOD: signed modulo. -/
  | smod (s : State) (a b : UInt256) (rest : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.SMOD, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .SMOD ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: b :: rest)
      : Step s ((s.consumeGas (Gas.baseCost s.fork .SMOD) h_gas).replaceStackAndIncrPC
                  (UInt256.smod a b :: rest))

  /-- ADDMOD: pop `a`, `b`, `n`; push `(a + b) mod n`. -/
  | addmod (s : State) (a b n : UInt256) (rest : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.ADDMOD, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .ADDMOD ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: b :: n :: rest)
      : Step s ((s.consumeGas (Gas.baseCost s.fork .ADDMOD) h_gas).replaceStackAndIncrPC
                  (UInt256.addMod a b n :: rest))

  /-- MULMOD: pop `a`, `b`, `n`; push `(a * b) mod n`. -/
  | mulmod (s : State) (a b n : UInt256) (rest : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.MULMOD, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .MULMOD ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: b :: n :: rest)
      : Step s ((s.consumeGas (Gas.baseCost s.fork .MULMOD) h_gas).replaceStackAndIncrPC
                  (UInt256.mulMod a b n :: rest))

  /-- EXP: pop `a`, `b`; push `a ^ b mod 2^256`. The static portion is the
      Yellow-Paper `G_exp = 10`; `h_dyn_gas` charges the per-byte exponent
      cost `Gas.expByteCost s.fork b` (= `50 · byteLen(b)` post-Spurious-Dragon). -/
  | exp (s : State) (a b : UInt256) (rest : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.EXP, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .EXP ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: b :: rest)
        (h_dyn_gas : Gas.expByteCost s.fork b
                      ≤ (s.consumeGas (Gas.baseCost s.fork .EXP) h_gas).gasAvailable)
      : Step s
          (let s' := s.consumeGas (Gas.baseCost s.fork .EXP) h_gas
           (s'.consumeGas (Gas.expByteCost s.fork b) h_dyn_gas).replaceStackAndIncrPC
             (UInt256.exp a b :: rest))

  /-- SIGNEXTEND: pop `b`, `x`; sign-extend `x` from byte index `b`. -/
  | signextend (s : State) (b x : UInt256) (rest : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.SIGNEXTEND, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .SIGNEXTEND ≤ s.gasAvailable)
        (h_stack   : s.stack = b :: x :: rest)
      : Step s ((s.consumeGas (Gas.baseCost s.fork .SIGNEXTEND) h_gas).replaceStackAndIncrPC
                  (UInt256.signExtend b x :: rest))

  ----------------------------------------------------------------------------
  -- Comparison & bitwise.
  ----------------------------------------------------------------------------

  | lt (s : State) (a b : UInt256) (rest : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.LT, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .LT ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: b :: rest)
      : Step s ((s.consumeGas (Gas.baseCost s.fork .LT) h_gas).replaceStackAndIncrPC
                  (UInt256.lt a b :: rest))

  | gt (s : State) (a b : UInt256) (rest : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.GT, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .GT ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: b :: rest)
      : Step s ((s.consumeGas (Gas.baseCost s.fork .GT) h_gas).replaceStackAndIncrPC
                  (UInt256.gt a b :: rest))

  | slt (s : State) (a b : UInt256) (rest : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.SLT, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .SLT ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: b :: rest)
      : Step s ((s.consumeGas (Gas.baseCost s.fork .SLT) h_gas).replaceStackAndIncrPC
                  (UInt256.slt a b :: rest))

  | sgt (s : State) (a b : UInt256) (rest : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.SGT, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .SGT ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: b :: rest)
      : Step s ((s.consumeGas (Gas.baseCost s.fork .SGT) h_gas).replaceStackAndIncrPC
                  (UInt256.sgt a b :: rest))

  | eq (s : State) (a b : UInt256) (rest : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.EQ, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .EQ ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: b :: rest)
      : Step s ((s.consumeGas (Gas.baseCost s.fork .EQ) h_gas).replaceStackAndIncrPC
                  (UInt256.eq a b :: rest))

  | iszero (s : State) (a : UInt256) (rest : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.ISZERO, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .ISZERO ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: rest)
      : Step s ((s.consumeGas (Gas.baseCost s.fork .ISZERO) h_gas).replaceStackAndIncrPC
                  (UInt256.isZero a :: rest))

  | and (s : State) (a b : UInt256) (rest : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.AND, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .AND ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: b :: rest)
      : Step s ((s.consumeGas (Gas.baseCost s.fork .AND) h_gas).replaceStackAndIncrPC
                  (UInt256.land a b :: rest))

  | or (s : State) (a b : UInt256) (rest : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.OR, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .OR ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: b :: rest)
      : Step s ((s.consumeGas (Gas.baseCost s.fork .OR) h_gas).replaceStackAndIncrPC
                  (UInt256.lor a b :: rest))

  | xor_ (s : State) (a b : UInt256) (rest : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.XOR, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .XOR ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: b :: rest)
      : Step s ((s.consumeGas (Gas.baseCost s.fork .XOR) h_gas).replaceStackAndIncrPC
                  (UInt256.xor a b :: rest))

  | not (s : State) (a : UInt256) (rest : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.NOT, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .NOT ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: rest)
      : Step s ((s.consumeGas (Gas.baseCost s.fork .NOT) h_gas).replaceStackAndIncrPC
                  (UInt256.lnot a :: rest))

  | byte_ (s : State) (i x : UInt256) (rest : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.BYTE, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .BYTE ≤ s.gasAvailable)
        (h_stack   : s.stack = i :: x :: rest)
      : Step s ((s.consumeGas (Gas.baseCost s.fork .BYTE) h_gas).replaceStackAndIncrPC
                  (UInt256.byteAt i x :: rest))

  | shl (s : State) (shift v : UInt256) (rest : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.SHL, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .SHL ≤ s.gasAvailable)
        (h_stack   : s.stack = shift :: v :: rest)
      : Step s ((s.consumeGas (Gas.baseCost s.fork .SHL) h_gas).replaceStackAndIncrPC
                  (UInt256.shiftLeft v shift :: rest))

  | shr (s : State) (shift v : UInt256) (rest : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.SHR, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .SHR ≤ s.gasAvailable)
        (h_stack   : s.stack = shift :: v :: rest)
      : Step s ((s.consumeGas (Gas.baseCost s.fork .SHR) h_gas).replaceStackAndIncrPC
                  (UInt256.shiftRight v shift :: rest))

  | sar (s : State) (shift v : UInt256) (rest : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.SAR, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .SAR ≤ s.gasAvailable)
        (h_stack   : s.stack = shift :: v :: rest)
      : Step s ((s.consumeGas (Gas.baseCost s.fork .SAR) h_gas).replaceStackAndIncrPC
                  (UInt256.sar v shift :: rest))

  ----------------------------------------------------------------------------
  -- KECCAK256.
  ----------------------------------------------------------------------------

  /-- KECCAK256: pop offset, size; push hash of memory[offset..offset+size].
      `h_mem` is the memory-expansion-gas precondition checked *after* the op
      cost has been deducted (mirroring `stepF.chargeMem`'s behaviour). -/
  | keccak256 (s : State) (offset size : UInt256) (rest : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.KECCAK256, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .KECCAK256 ≤ s.gasAvailable)
        (h_stack   : s.stack = offset :: size :: rest)
        (h_mem     : (s.consumeGas (Gas.baseCost s.fork .KECCAK256) h_gas).canExpandMemory
                       offset.toNat size.toNat)
      : Step s
          (let bytes := MachineState.readPadded s.memory offset.toNat size.toNat
           ((s.consumeGas (Gas.baseCost s.fork .KECCAK256) h_gas).consumeMemExp
              offset.toNat size.toNat h_mem).replaceStackAndIncrPC
             (EvmSemantics.keccak256 bytes :: rest))

  ----------------------------------------------------------------------------
  -- Environment reads.
  ----------------------------------------------------------------------------

  | address (s : State)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.ADDRESS, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .ADDRESS ≤ s.gasAvailable)
      : Step s ((s.consumeGas (Gas.baseCost s.fork .ADDRESS) h_gas).replaceStackAndIncrPC
                  (s.executionEnv.codeOwner.toUInt256 :: s.stack))

  | balance (s : State) (addr : UInt256) (rest : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.BALANCE, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .BALANCE ≤ s.gasAvailable)
        (h_stack   : s.stack = addr :: rest)
      : Step s ((s.consumeGas (Gas.baseCost s.fork .BALANCE) h_gas).replaceStackAndIncrPC
                  ((s.accountMap (AccountAddress.ofUInt256 addr)).balance :: rest))

  | origin (s : State)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.ORIGIN, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .ORIGIN ≤ s.gasAvailable)
      : Step s ((s.consumeGas (Gas.baseCost s.fork .ORIGIN) h_gas).replaceStackAndIncrPC
                  (s.executionEnv.sender.toUInt256 :: s.stack))

  | caller (s : State)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.CALLER, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .CALLER ≤ s.gasAvailable)
      : Step s ((s.consumeGas (Gas.baseCost s.fork .CALLER) h_gas).replaceStackAndIncrPC
                  (s.executionEnv.source.toUInt256 :: s.stack))

  | callvalue (s : State)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.CALLVALUE, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .CALLVALUE ≤ s.gasAvailable)
      : Step s ((s.consumeGas (Gas.baseCost s.fork .CALLVALUE) h_gas).replaceStackAndIncrPC
                  (s.executionEnv.weiValue :: s.stack))

  /-- CALLDATALOAD: pop `i`; push 32 bytes of calldata starting at `i`,
      zero-padded if past the end. -/
  | calldataload (s : State) (i : UInt256) (rest : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.CALLDATALOAD, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .CALLDATALOAD ≤ s.gasAvailable)
        (h_stack   : s.stack = i :: rest)
      : Step s
          (let bs := MachineState.readPadded s.executionEnv.calldata i.toNat 32
           let word : Nat := bs.toList.foldl (fun acc b => acc * 256 + b.toNat) 0
           (s.consumeGas (Gas.baseCost s.fork .CALLDATALOAD) h_gas).replaceStackAndIncrPC
             (UInt256.ofNat word :: rest))

  | calldatasize (s : State)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.CALLDATASIZE, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .CALLDATASIZE ≤ s.gasAvailable)
      : Step s ((s.consumeGas (Gas.baseCost s.fork .CALLDATASIZE) h_gas).replaceStackAndIncrPC
                  (UInt256.ofNat s.executionEnv.calldata.size :: s.stack))

  /-- CALLDATACOPY: pop destOffset, srcOffset, size; copy calldata to memory.
      `h_dyn_gas` charges the per-word copy cost `3 · ⌈sz/32⌉` on top of the
      static fee and the memory-expansion charge. -/
  | calldatacopy (s : State) (destOff srcOff sz : UInt256) (rest : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.CALLDATACOPY, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .CALLDATACOPY ≤ s.gasAvailable)
        (h_stack   : s.stack = destOff :: srcOff :: sz :: rest)
        (h_mem     : (s.consumeGas (Gas.baseCost s.fork .CALLDATACOPY) h_gas).canExpandMemory
                       destOff.toNat sz.toNat)
        (h_dyn_gas : Gas.copyWordCost sz ≤
                       ((s.consumeGas (Gas.baseCost s.fork .CALLDATACOPY) h_gas).consumeMemExp
                          destOff.toNat sz.toNat h_mem).gasAvailable)
      : Step s
          (let bytes := MachineState.readPadded s.executionEnv.calldata srcOff.toNat sz.toNat
           let s'' := (s.consumeGas (Gas.baseCost s.fork .CALLDATACOPY) h_gas).consumeMemExp
                        destOff.toNat sz.toNat h_mem
           let s''' := s''.consumeGas (Gas.copyWordCost sz) h_dyn_gas
           let μ' : MachineState :=
             { s'''.toMachineState with
                 memory := MachineState.writeBytes s.memory bytes destOff.toNat }
           { s''' with toMachineState := μ' }.replaceStackAndIncrPC rest)

  | codesize (s : State)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.CODESIZE, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .CODESIZE ≤ s.gasAvailable)
      : Step s ((s.consumeGas (Gas.baseCost s.fork .CODESIZE) h_gas).replaceStackAndIncrPC
                  (UInt256.ofNat s.executionEnv.code.size :: s.stack))

  /-- CODECOPY: pop destOffset, srcOffset, size; copy current code to memory. -/
  | codecopy (s : State) (destOff srcOff sz : UInt256) (rest : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.CODECOPY, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .CODECOPY ≤ s.gasAvailable)
        (h_stack   : s.stack = destOff :: srcOff :: sz :: rest)
        (h_mem     : (s.consumeGas (Gas.baseCost s.fork .CODECOPY) h_gas).canExpandMemory
                       destOff.toNat sz.toNat)
        (h_dyn_gas : Gas.copyWordCost sz ≤
                       ((s.consumeGas (Gas.baseCost s.fork .CODECOPY) h_gas).consumeMemExp
                          destOff.toNat sz.toNat h_mem).gasAvailable)
      : Step s
          (let bytes := MachineState.readPadded s.executionEnv.code srcOff.toNat sz.toNat
           let s'' := (s.consumeGas (Gas.baseCost s.fork .CODECOPY) h_gas).consumeMemExp
                        destOff.toNat sz.toNat h_mem
           let s''' := s''.consumeGas (Gas.copyWordCost sz) h_dyn_gas
           let μ' : MachineState :=
             { s'''.toMachineState with
                 memory := MachineState.writeBytes s.memory bytes destOff.toNat }
           { s''' with toMachineState := μ' }.replaceStackAndIncrPC rest)

  | gasprice (s : State)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.GASPRICE, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .GASPRICE ≤ s.gasAvailable)
      : Step s ((s.consumeGas (Gas.baseCost s.fork .GASPRICE) h_gas).replaceStackAndIncrPC
                  (s.executionEnv.gasPrice :: s.stack))

  | extcodesize (s : State) (addr : UInt256) (rest : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.EXTCODESIZE, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .EXTCODESIZE ≤ s.gasAvailable)
        (h_stack   : s.stack = addr :: rest)
      : Step s ((s.consumeGas (Gas.baseCost s.fork .EXTCODESIZE) h_gas).replaceStackAndIncrPC
                  (UInt256.ofNat (s.accountMap (AccountAddress.ofUInt256 addr)).code.size :: rest))

  /-- EXTCODECOPY: pop addr, destOffset, srcOffset, size; copy external
      code bytes to memory. -/
  | extcodecopy (s : State) (addr destOff srcOff sz : UInt256) (rest : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.EXTCODECOPY, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .EXTCODECOPY ≤ s.gasAvailable)
        (h_stack   : s.stack = addr :: destOff :: srcOff :: sz :: rest)
        (h_mem     : (s.consumeGas (Gas.baseCost s.fork .EXTCODECOPY) h_gas).canExpandMemory
                       destOff.toNat sz.toNat)
        (h_dyn_gas : Gas.copyWordCost sz ≤
                       ((s.consumeGas (Gas.baseCost s.fork .EXTCODECOPY) h_gas).consumeMemExp
                          destOff.toNat sz.toNat h_mem).gasAvailable)
      : Step s
          (let extCode := (s.accountMap (AccountAddress.ofUInt256 addr)).code
           let bytes := MachineState.readPadded extCode srcOff.toNat sz.toNat
           let s'' := (s.consumeGas (Gas.baseCost s.fork .EXTCODECOPY) h_gas).consumeMemExp
                        destOff.toNat sz.toNat h_mem
           let s''' := s''.consumeGas (Gas.copyWordCost sz) h_dyn_gas
           let μ' : MachineState :=
             { s'''.toMachineState with
                 memory := MachineState.writeBytes s.memory bytes destOff.toNat }
           { s''' with toMachineState := μ' }.replaceStackAndIncrPC rest)

  | returndatasize (s : State)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.RETURNDATASIZE, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .RETURNDATASIZE ≤ s.gasAvailable)
      : Step s ((s.consumeGas (Gas.baseCost s.fork .RETURNDATASIZE) h_gas).replaceStackAndIncrPC
                  (UInt256.ofNat s.returnData.size :: s.stack))

  /-- RETURNDATACOPY: pop destOffset, srcOffset, size; copy returndata to memory.
      Out-of-bounds reads raise `InvalidMemoryAccess` (handled in Phase 5). -/
  | returndatacopy (s : State) (destOff srcOff sz : UInt256) (rest : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.RETURNDATACOPY, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .RETURNDATACOPY ≤ s.gasAvailable)
        (h_stack   : s.stack = destOff :: srcOff :: sz :: rest)
        (h_inbounds : srcOff.toNat + sz.toNat ≤ s.returnData.size)
        (h_mem     : (s.consumeGas (Gas.baseCost s.fork .RETURNDATACOPY) h_gas).canExpandMemory
                       destOff.toNat sz.toNat)
        (h_dyn_gas : Gas.copyWordCost sz ≤
                       ((s.consumeGas (Gas.baseCost s.fork .RETURNDATACOPY) h_gas).consumeMemExp
                          destOff.toNat sz.toNat h_mem).gasAvailable)
      : Step s
          (let bytes := MachineState.readPadded s.returnData srcOff.toNat sz.toNat
           let s'' := (s.consumeGas (Gas.baseCost s.fork .RETURNDATACOPY) h_gas).consumeMemExp
                        destOff.toNat sz.toNat h_mem
           let s''' := s''.consumeGas (Gas.copyWordCost sz) h_dyn_gas
           let μ' : MachineState :=
             { s'''.toMachineState with
                 memory := MachineState.writeBytes s.memory bytes destOff.toNat }
           { s''' with toMachineState := μ' }.replaceStackAndIncrPC rest)

  | extcodehash (s : State) (addr : UInt256) (rest : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.EXTCODEHASH, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .EXTCODEHASH ≤ s.gasAvailable)
        (h_stack   : s.stack = addr :: rest)
      : Step s ((s.consumeGas (Gas.baseCost s.fork .EXTCODEHASH) h_gas).replaceStackAndIncrPC
                  ((s.accountMap (AccountAddress.ofUInt256 addr)).codeHash :: rest))

  ----------------------------------------------------------------------------
  -- Block-context reads.
  ----------------------------------------------------------------------------

  | blockhash (s : State) (n : UInt256) (rest : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.BLOCKHASH, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .BLOCKHASH ≤ s.gasAvailable)
        (h_stack   : s.stack = n :: rest)
      : Step s ((s.consumeGas (Gas.baseCost s.fork .BLOCKHASH) h_gas).replaceStackAndIncrPC
                  (s.executionEnv.header.blockHash n :: rest))

  | coinbase (s : State)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.COINBASE, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .COINBASE ≤ s.gasAvailable)
      : Step s ((s.consumeGas (Gas.baseCost s.fork .COINBASE) h_gas).replaceStackAndIncrPC
                  (s.executionEnv.header.coinbase.toUInt256 :: s.stack))

  | timestamp (s : State)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.TIMESTAMP, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .TIMESTAMP ≤ s.gasAvailable)
      : Step s ((s.consumeGas (Gas.baseCost s.fork .TIMESTAMP) h_gas).replaceStackAndIncrPC
                  (s.executionEnv.header.timestamp :: s.stack))

  | number (s : State)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.NUMBER, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .NUMBER ≤ s.gasAvailable)
      : Step s ((s.consumeGas (Gas.baseCost s.fork .NUMBER) h_gas).replaceStackAndIncrPC
                  (s.executionEnv.header.number :: s.stack))

  | prevrandao (s : State)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.PREVRANDAO, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .PREVRANDAO ≤ s.gasAvailable)
      : Step s ((s.consumeGas (Gas.baseCost s.fork .PREVRANDAO) h_gas).replaceStackAndIncrPC
                  (s.executionEnv.header.prevRandao :: s.stack))

  | gaslimit (s : State)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.GASLIMIT, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .GASLIMIT ≤ s.gasAvailable)
      : Step s ((s.consumeGas (Gas.baseCost s.fork .GASLIMIT) h_gas).replaceStackAndIncrPC
                  (s.executionEnv.header.gasLimit :: s.stack))

  | chainid (s : State)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.CHAINID, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .CHAINID ≤ s.gasAvailable)
      : Step s ((s.consumeGas (Gas.baseCost s.fork .CHAINID) h_gas).replaceStackAndIncrPC
                  (s.executionEnv.header.chainId :: s.stack))

  | selfbalance (s : State)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.SELFBALANCE, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .SELFBALANCE ≤ s.gasAvailable)
      : Step s ((s.consumeGas (Gas.baseCost s.fork .SELFBALANCE) h_gas).replaceStackAndIncrPC
                  ((s.accountMap s.executionEnv.codeOwner).balance :: s.stack))

  | basefee (s : State)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.BASEFEE, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .BASEFEE ≤ s.gasAvailable)
      : Step s ((s.consumeGas (Gas.baseCost s.fork .BASEFEE) h_gas).replaceStackAndIncrPC
                  (s.executionEnv.header.baseFeePerGas :: s.stack))

  | blobhash (s : State) (i : UInt256) (rest : List UInt256) (h : UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.BLOBHASH, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .BLOBHASH ≤ s.gasAvailable)
        (h_stack   : s.stack = i :: rest)
        (h_get     : s.executionEnv.blobVersionedHashes[i.toNat]? = some h)
      : Step s ((s.consumeGas (Gas.baseCost s.fork .BLOBHASH) h_gas).replaceStackAndIncrPC
                  (h :: rest))

  /-- BLOBHASH when index is out of range — push 0. -/
  | blobhash_oob (s : State) (i : UInt256) (rest : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.BLOBHASH, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .BLOBHASH ≤ s.gasAvailable)
        (h_stack   : s.stack = i :: rest)
        (h_oob     : s.executionEnv.blobVersionedHashes[i.toNat]? = none)
      : Step s ((s.consumeGas (Gas.baseCost s.fork .BLOBHASH) h_gas).replaceStackAndIncrPC
                  (⟨0⟩ :: rest))

  | blobbasefee (s : State)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.BLOBBASEFEE, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .BLOBBASEFEE ≤ s.gasAvailable)
      : Step s ((s.consumeGas (Gas.baseCost s.fork .BLOBBASEFEE) h_gas).replaceStackAndIncrPC
                  (s.executionEnv.header.blobBaseFee :: s.stack))

  ----------------------------------------------------------------------------
  -- Stack manipulation: POP, PUSHk, DUPn, SWAPn.
  ----------------------------------------------------------------------------

  | pop (s : State) (a : UInt256) (rest : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.POP, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .POP ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: rest)
      : Step s ((s.consumeGas (Gas.baseCost s.fork .POP) h_gas).replaceStackAndIncrPC
                  rest)

  /-- PUSH0: push `0`. -/
  | push0 (s : State)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.Push ⟨0, by decide⟩, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork (.Push ⟨0, by decide⟩) ≤ s.gasAvailable)
      : Step s
          ((s.consumeGas (Gas.baseCost s.fork (.Push ⟨0, by decide⟩)) h_gas).replaceStackAndIncrPC
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
        (h_gas     : Gas.baseCost s.fork (.Push ⟨k, k.isLt⟩) ≤ s.gasAvailable)
      : Step s ((s.consumeGas (Gas.baseCost s.fork (.Push ⟨k, k.isLt⟩)) h_gas).replaceStackAndIncrPC
                  (data :: s.stack) (pcΔ := immWidth + 1))

  /-- DUPn: copy `stack[n]` (0-indexed from top) to the top. -/
  | dup (s : State) (n : Fin 16) (v : UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.Dup ⟨n⟩, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork (.Dup ⟨n⟩) ≤ s.gasAvailable)
        (h_get     : s.stack[n.val]? = some v)
      : Step s
          ((s.consumeGas (Gas.baseCost s.fork (.Dup ⟨n⟩)) h_gas).replaceStackAndIncrPC
              (v :: s.stack))

  /-- SWAPn: swap top with `stack[n+1]`. -/
  | swap (s : State) (n : Fin 16) (stk' : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.Swap ⟨n⟩, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork (.Swap ⟨n⟩) ≤ s.gasAvailable)
        (h_swap    : s.stack.exchange 0 (n.val + 1) = some stk')
      : Step s ((s.consumeGas (Gas.baseCost s.fork (.Swap ⟨n⟩)) h_gas).replaceStackAndIncrPC stk')

  ----------------------------------------------------------------------------
  -- Memory.
  ----------------------------------------------------------------------------

  /-- MLOAD: pop offset; push the 32-byte word at memory[offset]. -/
  | mload (s : State) (offset : UInt256) (rest : List UInt256)
        (v : UInt256) (μ' : MachineState)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.MLOAD, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .MLOAD ≤ s.gasAvailable)
        (h_stack   : s.stack = offset :: rest)
        (h_mem     : (s.consumeGas (Gas.baseCost s.fork .MLOAD) h_gas).canExpandMemory
                       offset.toNat 32)
        (h_load    : MachineState.mload
                       ((s.consumeGas (Gas.baseCost s.fork .MLOAD) h_gas).consumeMemExp
                          offset.toNat 32 h_mem).toMachineState offset = (v, μ'))
      : Step s ({ ((s.consumeGas (Gas.baseCost s.fork .MLOAD) h_gas).consumeMemExp
                     offset.toNat 32 h_mem) with toMachineState := μ' }
                  |>.replaceStackAndIncrPC (v :: rest))

  /-- MSTORE: pop offset, value; write `value` as 32 bytes at memory[offset]. -/
  | mstore (s : State) (offset value : UInt256) (rest : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.MSTORE, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .MSTORE ≤ s.gasAvailable)
        (h_stack   : s.stack = offset :: value :: rest)
        (h_mem     : (s.consumeGas (Gas.baseCost s.fork .MSTORE) h_gas).canExpandMemory
                       offset.toNat 32)
      : Step s
          (let s'' := (s.consumeGas (Gas.baseCost s.fork .MSTORE) h_gas).consumeMemExp
                        offset.toNat 32 h_mem
           let μ' := MachineState.mstore s''.toMachineState offset value
           { s'' with toMachineState := μ' }.replaceStackAndIncrPC rest)

  /-- MSTORE8: pop offset, value; write the low byte of `value` at memory[offset]. -/
  | mstore8 (s : State) (offset value : UInt256) (rest : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.MSTORE8, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .MSTORE8 ≤ s.gasAvailable)
        (h_stack   : s.stack = offset :: value :: rest)
        (h_mem     : (s.consumeGas (Gas.baseCost s.fork .MSTORE8) h_gas).canExpandMemory
                       offset.toNat 1)
      : Step s
          (let s'' := (s.consumeGas (Gas.baseCost s.fork .MSTORE8) h_gas).consumeMemExp
                        offset.toNat 1 h_mem
           let μ' := MachineState.mstore8 s''.toMachineState offset value
           { s'' with toMachineState := μ' }.replaceStackAndIncrPC rest)

  | msize (s : State)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.MSIZE, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .MSIZE ≤ s.gasAvailable)
      : Step s ((s.consumeGas (Gas.baseCost s.fork .MSIZE) h_gas).replaceStackAndIncrPC
                  (MachineState.msize s.toMachineState :: s.stack))

  /-- MCOPY: pop destOffset, srcOffset, size; copy memory[src..src+sz] to dest.
      Touches *both* the read range `[srcOff, srcOff+sz)` and the write range
      `[destOff, destOff+sz)`; expansion gas is charged for their union. -/
  | mcopy (s : State) (destOff srcOff sz : UInt256) (rest : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.MCOPY, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .MCOPY ≤ s.gasAvailable)
        (h_stack   : s.stack = destOff :: srcOff :: sz :: rest)
        (h_mem     : (s.consumeGas (Gas.baseCost s.fork .MCOPY) h_gas).canExpandMemory2
                       destOff.toNat sz.toNat srcOff.toNat sz.toNat)
        (h_dyn_gas : Gas.copyWordCost sz ≤
                       ((s.consumeGas (Gas.baseCost s.fork .MCOPY)
                                       h_gas).consumeMemExp2 destOff.toNat sz.toNat
                                       srcOff.toNat sz.toNat h_mem).gasAvailable)
      : Step s
          (let s'' := (s.consumeGas (Gas.baseCost s.fork .MCOPY) h_gas).consumeMemExp2
                        destOff.toNat sz.toNat srcOff.toNat sz.toNat h_mem
           let s''' := s''.consumeGas (Gas.copyWordCost sz) h_dyn_gas
           let μ' := MachineState.mcopy s'''.toMachineState destOff srcOff sz
           { s''' with toMachineState := μ' }.replaceStackAndIncrPC rest)

  ----------------------------------------------------------------------------
  -- Storage (persistent and transient).
  ----------------------------------------------------------------------------

  /-- SLOAD: pop key; push storage[key] from the executing contract. -/
  | sload (s : State) (key : UInt256) (rest : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.SLOAD, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .SLOAD ≤ s.gasAvailable)
        (h_stack   : s.stack = key :: rest)
      : Step s ((s.consumeGas (Gas.baseCost s.fork .SLOAD) h_gas).replaceStackAndIncrPC
                  (((s.accountMap s.executionEnv.codeOwner).storage key) :: rest))

  /-- SSTORE: pop key, value; write storage[key] := value. Requires
      static-mode permission. `h_dyn_gas` charges the EIP-1283 net-metered
      `Gas.sstoreCost s.fork original current value` on top of the (zero) static
      fee, so the actual gas deducted matches the dynamic schedule. -/
  | sstore (s : State) (key value : UInt256) (rest : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.SSTORE, arg))
        (h_running : s.halt = .Running)
        (h_perm    : s.executionEnv.permitStateMutation = true)
        (h_gas     : Gas.baseCost s.fork .SSTORE ≤ s.gasAvailable)
        (h_stack   : s.stack = key :: value :: rest)
        -- EIP-2200 stipend sentry must not be triggered (Cancun only).
        (h_sentry  : Gas.sstoreSentry s.fork
                       (s.consumeGas (Gas.baseCost s.fork .SSTORE) h_gas).gasAvailable
                     = false)
        (h_dyn_gas : Gas.sstoreCost s.fork
                       (s.substate.originalStorage s.executionEnv.codeOwner key)
                       ((s.accountMap s.executionEnv.codeOwner).storage key) value
                       ≤ (s.consumeGas (Gas.baseCost s.fork .SSTORE) h_gas).gasAvailable)
      : Step s
          (let addr     := s.executionEnv.codeOwner
           let acc      := s.accountMap addr
           let current  := acc.storage key
           let original := s.substate.originalStorage addr key
           let cost     := Gas.sstoreCost s.fork original current value
           let acc' := { acc with storage := acc.storage.set key value }
           let σ'   := s.accountMap.set addr acc'
           { ((s.consumeGas (Gas.baseCost s.fork .SSTORE) h_gas).consumeGas cost h_dyn_gas)
               with accountMap := σ' }
             |>.replaceStackAndIncrPC rest)

  /-- TLOAD: like SLOAD but reads from transient storage. -/
  | tload (s : State) (key : UInt256) (rest : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.TLOAD, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .TLOAD ≤ s.gasAvailable)
        (h_stack   : s.stack = key :: rest)
      : Step s ((s.consumeGas (Gas.baseCost s.fork .TLOAD) h_gas).replaceStackAndIncrPC
                  (((s.accountMap s.executionEnv.codeOwner).tstorage key) :: rest))

  /-- TSTORE: like SSTORE but writes to transient storage. -/
  | tstore (s : State) (key value : UInt256) (rest : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.TSTORE, arg))
        (h_running : s.halt = .Running)
        (h_perm    : s.executionEnv.permitStateMutation = true)
        (h_gas     : Gas.baseCost s.fork .TSTORE ≤ s.gasAvailable)
        (h_stack   : s.stack = key :: value :: rest)
      : Step s
          (let addr := s.executionEnv.codeOwner
           let acc  := s.accountMap addr
           let acc' := { acc with tstorage := acc.tstorage.set key value }
           let σ'   := s.accountMap.set addr acc'
           { (s.consumeGas (Gas.baseCost s.fork .TSTORE) h_gas) with accountMap := σ' }
             |>.replaceStackAndIncrPC rest)

  ----------------------------------------------------------------------------
  -- Control flow: JUMP, JUMPI, JUMPDEST, PC, GAS.
  ----------------------------------------------------------------------------

  /-- JUMP: pop destination; set `pc := dest` if the destination is a JUMPDEST. -/
  | jump (s : State) (dest : UInt256) (rest : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.JUMP, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .JUMP ≤ s.gasAvailable)
        (h_stack   : s.stack = dest :: rest)
        (h_valid   : Decode.decodeAt s.executionEnv.code dest.toNat
                       = some (.JUMPDEST, none))
      : Step s { (s.consumeGas (Gas.baseCost s.fork .JUMP) h_gas) with pc := dest, stack := rest }

  /-- JUMPI (taken): pop dest, cond; if `cond ≠ 0` and dest is a JUMPDEST,
      set `pc := dest`. -/
  | jumpi_taken (s : State) (dest cond : UInt256) (rest : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.JUMPI, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .JUMPI ≤ s.gasAvailable)
        (h_stack   : s.stack = dest :: cond :: rest)
        (h_cond    : UInt256.isTrue cond)
        (h_valid   : Decode.decodeAt s.executionEnv.code dest.toNat
                       = some (.JUMPDEST, none))
      : Step s { (s.consumeGas (Gas.baseCost s.fork .JUMPI) h_gas) with pc := dest, stack := rest }

  /-- JUMPI (not taken): pop dest, cond; if `cond = 0`, fall through to `pc + 1`. -/
  | jumpi_notTaken (s : State) (dest cond : UInt256) (rest : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.JUMPI, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .JUMPI ≤ s.gasAvailable)
        (h_stack   : s.stack = dest :: cond :: rest)
        (h_cond    : ¬ UInt256.isTrue cond)
      : Step s ((s.consumeGas (Gas.baseCost s.fork .JUMPI) h_gas).replaceStackAndIncrPC
                  rest)

  | pc (s : State)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.PC, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .PC ≤ s.gasAvailable)
      : Step s ((s.consumeGas (Gas.baseCost s.fork .PC) h_gas).replaceStackAndIncrPC
                  (s.pc :: s.stack))

  /-- GAS pushes the remaining gas *after* the opcode's own 2-gas cost is
      deducted (Yellow Paper §9.4.7 / EIP-150), so we read the post-charge
      `s'.gasAvailable` rather than the original `s.gasAvailable`. -/
  | gas (s : State)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.GAS, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .GAS ≤ s.gasAvailable)
      : Step s
          (let s' := s.consumeGas (Gas.baseCost s.fork .GAS) h_gas
           s'.replaceStackAndIncrPC (UInt256.ofNat s'.gasAvailable :: s.stack))

  | jumpdest (s : State)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.JUMPDEST, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .JUMPDEST ≤ s.gasAvailable)
      : Step s ((s.consumeGas (Gas.baseCost s.fork .JUMPDEST) h_gas).incrPC)

  ----------------------------------------------------------------------------
  -- Halts: STOP, RETURN, REVERT.
  ----------------------------------------------------------------------------

  | stop (s : State)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.STOP, arg))
        (h_running : s.halt = .Running)
      : Step s { s with halt := .Success, hReturn := .empty }

  | return_ (s : State) (offset size : UInt256) (rest : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.RETURN, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .RETURN ≤ s.gasAvailable)
        (h_stack   : s.stack = offset :: size :: rest)
        (h_mem     : (s.consumeGas (Gas.baseCost s.fork .RETURN) h_gas).canExpandMemory
                       offset.toNat size.toNat)
      : Step s
          (let bs := MachineState.readPadded s.memory offset.toNat size.toNat
           let s'' := (s.consumeGas (Gas.baseCost s.fork .RETURN) h_gas).consumeMemExp
                        offset.toNat size.toNat h_mem
           { s'' with halt := .Returned, hReturn := bs, stack := rest })

  | revert (s : State) (offset size : UInt256) (rest : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.REVERT, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .REVERT ≤ s.gasAvailable)
        (h_stack   : s.stack = offset :: size :: rest)
        (h_mem     : (s.consumeGas (Gas.baseCost s.fork .REVERT) h_gas).canExpandMemory
                       offset.toNat size.toNat)
      : Step s
          (let bs := MachineState.readPadded s.memory offset.toNat size.toNat
           let s'' := (s.consumeGas (Gas.baseCost s.fork .REVERT) h_gas).consumeMemExp
                        offset.toNat size.toNat h_mem
           { s'' with halt := .Reverted, hReturn := bs, stack := rest })

  ----------------------------------------------------------------------------
  -- CALL. The intermediate gas-charged states `s' s2 s3 s4` are introduced as
  -- explicit parameters tied down by equation hypotheses (rather than inlined),
  -- so each later hypothesis can refer to the previous state by name. This
  -- mirrors `stepF.system`'s `.CALL` arm step-for-step.
  ----------------------------------------------------------------------------

  /-- CALL (taken): pop the 7 args; charge base (`G_call`), memory expansion for
      the args+return ranges, and the value/new-account surcharge; check the
      depth limit and caller balance; forward 63/64 of the remaining gas plus
      the value stipend; transfer `value`; and enter the callee frame. -/
  | call (s : State)
        (gasArg toArg value argsOff argsLen retOff retLen : UInt256)
        (rest : List UInt256) (arg : Option (UInt256 × Nat))
        (s' s2 s3 s4 : State) (forwarded : Nat)
        (h_op      : s.decoded = some (.CALL, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .CALL ≤ s.gasAvailable)
        (h_stack   : s.stack =
                       gasArg :: toArg :: value :: argsOff :: argsLen :: retOff :: retLen :: rest)
        (h_s'      : s' = s.consumeGas (Gas.baseCost s.fork .CALL) h_gas)
        (h_mem     : s'.canExpandMemory2 argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat)
        (h_s2      : s2 = s'.consumeMemExp2 argsOff.toNat argsLen.toNat
                            retOff.toNat retLen.toNat h_mem)
        (h_sc      : Gas.callSurcharge (value.toNat != 0)
                       (s2.accountMap (AccountAddress.ofUInt256 toArg)).isEmpty
                       ≤ s2.gasAvailable)
        (h_s3      : s3 = s2.consumeGas (Gas.callSurcharge (value.toNat != 0)
                       (s2.accountMap (AccountAddress.ofUInt256 toArg)).isEmpty) h_sc)
        (h_take    : ¬ (s3.executionEnv.depth ≥ 1024 ∨
                        (s3.accountMap s3.executionEnv.codeOwner).balance < value))
        (h_fwd     : forwarded =
                       min gasArg.toNat (Gas.allButOneSixtyFourth s3.gasAvailable))
        (h_fw      : forwarded ≤ s3.gasAvailable)
        (h_s4      : s4 = s3.consumeGas forwarded h_fw)
      : Step s
          (s4.enterCall rest (AccountAddress.ofUInt256 toArg) value
             (MachineState.readPadded s4.memory argsOff.toNat argsLen.toNat)
             (s2.accountMap (AccountAddress.ofUInt256 toArg)).code
             (forwarded + (bif (value.toNat != 0) then Gas.callStipend else 0))
             retOff.toNat retLen.toNat)

  /-- CALL (not taken): the depth limit is hit or the caller cannot afford the
      value. Base+memory+surcharge gas is still charged; `0` is pushed and the
      forwarded gas is *not* spent. -/
  | callFail (s : State)
        (gasArg toArg value argsOff argsLen retOff retLen : UInt256)
        (rest : List UInt256) (arg : Option (UInt256 × Nat))
        (s' s2 s3 : State)
        (h_op      : s.decoded = some (.CALL, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .CALL ≤ s.gasAvailable)
        (h_stack   : s.stack =
                       gasArg :: toArg :: value :: argsOff :: argsLen :: retOff :: retLen :: rest)
        (h_s'      : s' = s.consumeGas (Gas.baseCost s.fork .CALL) h_gas)
        (h_mem     : s'.canExpandMemory2 argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat)
        (h_s2      : s2 = s'.consumeMemExp2 argsOff.toNat argsLen.toNat
                            retOff.toNat retLen.toNat h_mem)
        (h_sc      : Gas.callSurcharge (value.toNat != 0)
                       (s2.accountMap (AccountAddress.ofUInt256 toArg)).isEmpty
                       ≤ s2.gasAvailable)
        (h_s3      : s3 = s2.consumeGas (Gas.callSurcharge (value.toNat != 0)
                       (s2.accountMap (AccountAddress.ofUInt256 toArg)).isEmpty) h_sc)
        (h_fail    : s3.executionEnv.depth ≥ 1024 ∨
                       (s3.accountMap s3.executionEnv.codeOwner).balance < value)
      : Step s (s3.replaceStackAndIncrPC (UInt256.ofNat 0 :: rest))

  ----------------------------------------------------------------------------
  -- Logging: LOG0–LOG4 (parametric over topic count).
  ----------------------------------------------------------------------------

  /-- LOG `n`: pop offset, size, then `n` topics; append a log entry. -/
  | log (s : State) (n : Fin 5) (offset size : UInt256)
        (topics : List UInt256) (rest : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.Log ⟨n⟩, arg))
        (h_running  : s.halt = .Running)
        (h_perm     : s.executionEnv.permitStateMutation = true)
        (h_gas      : Gas.baseCost s.fork (.Log ⟨n⟩) ≤ s.gasAvailable)
        (h_topics_n : topics.length = n.val)
        (h_stack    : s.stack = offset :: size :: topics ++ rest)
        (h_mem      : (s.consumeGas (Gas.baseCost s.fork (.Log ⟨n⟩)) h_gas).canExpandMemory
                        offset.toNat size.toNat)
        (h_dyn_gas  : Gas.logDataCost size ≤
                        ((s.consumeGas (Gas.baseCost s.fork (.Log ⟨n⟩)) h_gas).consumeMemExp
                            offset.toNat size.toNat h_mem).gasAvailable)
      : Step s
          (let entry : LogEntry :=
             { address := s.executionEnv.codeOwner
               topics  := topics.toArray
               data    := MachineState.readPadded s.memory offset.toNat size.toNat }
           let s'' := (s.consumeGas (Gas.baseCost s.fork (.Log ⟨n⟩)) h_gas).consumeMemExp
                        offset.toNat size.toNat h_mem
           let s''' := s''.consumeGas (Gas.logDataCost size) h_dyn_gas
           { s''' with substate := s.substate.appendLog entry }
             |>.replaceStackAndIncrPC rest)

  ----------------------------------------------------------------------------
  -- EIP-8024: DUPN, SWAPN, EXCHANGE.
  ----------------------------------------------------------------------------

  /-- DUPN with immediate `n`: duplicate `stack[n]` to the top. PC += 2. -/
  | dupN (s : State) (n : Fin 256) (v : UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.DupN ⟨n⟩, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork (.DupN ⟨n⟩) ≤ s.gasAvailable)
        (h_get     : s.stack[n.val]? = some v)
      : Step s ((s.consumeGas (Gas.baseCost s.fork (.DupN ⟨n⟩)) h_gas).replaceStackAndIncrPC
                  (v :: s.stack) (pcΔ := 2))

  /-- SWAPN with immediate `n`: swap top with `stack[n+1]`. PC += 2. -/
  | swapN (s : State) (n : Fin 256) (stk' : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.SwapN ⟨n⟩, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork (.SwapN ⟨n⟩) ≤ s.gasAvailable)
        (h_swap    : s.stack.exchange 0 (n.val + 1) = some stk')
      : Step s ((s.consumeGas (Gas.baseCost s.fork (.SwapN ⟨n⟩)) h_gas).replaceStackAndIncrPC
                  stk' (pcΔ := 2))

  /-- EXCHANGE with packed immediate `b`: swap `stack[n+1]` and `stack[m+1]`
      where `n = b >>> 4` and `m = b &&& 0xf`. PC += 2. -/
  | exchange (s : State) (b : Fin 256) (stk' : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.Exchange ⟨b⟩, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork (.Exchange ⟨b⟩) ≤ s.gasAvailable)
        (h_swap    : s.stack.exchange
                      (b.val >>> 4 + 1)
                      ((b.val &&& 0xf) + 1) = some stk')
      : Step s ((s.consumeGas (Gas.baseCost s.fork (.Exchange ⟨b⟩)) h_gas).replaceStackAndIncrPC
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
        (h_running : s.halt = .Running)
        (h_none    : s.decoded = none)
      : Step s (s.haltWith .InvalidInstruction)

  /-- The explicit `INVALID` opcode (`0xfe`). -/
  | invalidOpcode (s : State)
        (h_running : s.halt = .Running)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.INVALID, arg))
      : Step s (s.haltWith .InvalidInstruction)

  /-- Insufficient gas to pay for the decoded operation's *total* cost.
      `cost` is any witness gas amount at least `baseCost` — this lets the
      rule fire not only when the static fee alone exceeds the budget but
      also when a dynamic surcharge does: memory expansion, per-word copy,
      per-byte LOG/EXP, `Gas.sstoreCost`, or the EIP-2200 stipend. The
      `h_cost_lb` constraint prevents bogus OOGs (a `cost < baseCost`
      witness could not actually halt the op). -/
  | outOfGas (s : State) (op : Operation) (arg : Option (UInt256 × Nat)) (cost : Nat)
        (h_op       : s.decoded = some (op, arg))
        (h_running  : s.halt = .Running)
        (h_cost_lb  : Gas.baseCost s.fork op ≤ cost)
        (h_gas      : s.gasAvailable < cost)
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
  | jumpBadDest (s : State) (dest : UInt256) (rest : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.JUMP, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .JUMP ≤ s.gasAvailable)
        (h_stack   : s.stack = dest :: rest)
        (h_bad     : Decode.decodeAt s.executionEnv.code dest.toNat ≠ some (.JUMPDEST, none))
      : Step s (s.haltWith .BadJumpDestination)

  /-- JUMPI with `cond ≠ 0` but destination is not a `JUMPDEST`. -/
  | jumpiBadDest (s : State) (dest cond : UInt256) (rest : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.JUMPI, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .JUMPI ≤ s.gasAvailable)
        (h_stack   : s.stack = dest :: cond :: rest)
        (h_cond    : UInt256.isTrue cond)
        (h_bad     : Decode.decodeAt s.executionEnv.code dest.toNat ≠ some (.JUMPDEST, none))
      : Step s (s.haltWith .BadJumpDestination)

  /-- RETURNDATACOPY with `srcOffset + size > returnData.size`. -/
  | returndatacopyOob (s : State) (destOff srcOff sz : UInt256) (rest : List UInt256)
        (arg       : Option (UInt256 × Nat))
        (h_op      : s.decoded = some (.RETURNDATACOPY, arg))
        (h_running : s.halt = .Running)
        (h_gas     : Gas.baseCost s.fork .RETURNDATACOPY ≤ s.gasAvailable)
        (h_stack   : s.stack = destOff :: srcOff :: sz :: rest)
        (h_oob     : srcOff.toNat + sz.toNat > s.returnData.size)
      : Step s (s.haltWith .InvalidMemoryAccess)

  ----------------------------------------------------------------------------
  -- Call return / resume rules.
  --
  -- Unlike every rule above, these fire on a *halted* active frame whose
  -- `callStack` is non-empty: the child has finished, so we pop the caller
  -- frame `f` and resume it (writing the child's return data into the
  -- caller's memory and pushing the success flag). They carry NO `h_running`
  -- — instead a `h_halt` on the concrete halt kind plus a non-empty-stack
  -- hypothesis. This is the only place a non-Running state has a successor.
  ----------------------------------------------------------------------------

  /-- Child STOP/RETURN: resume the caller with success flag `1`, keeping the
      child's world mutations and refunding its unspent gas. -/
  | callReturnSuccess (s : State) (f : Frame) (rest : List Frame)
        (h_halt  : s.halt = .Success ∨ s.halt = .Returned)
        (h_stack : s.callStack = f :: rest)
      : Step s (s.resumeSuccess f rest)

  /-- Child REVERT: resume the caller with failure flag `0`, roll the world
      back to the call-time snapshot, return the revert data, refund unspent gas. -/
  | callReturnRevert (s : State) (f : Frame) (rest : List Frame)
        (h_halt  : s.halt = .Reverted)
        (h_stack : s.callStack = f :: rest)
      : Step s (s.resumeRevert f rest)

  /-- Child exceptional halt: resume the caller with failure flag `0`, roll the
      world back, return no data, and refund nothing. -/
  | callReturnException (s : State) (f : Frame) (rest : List Frame)
        (e : ExecutionException)
        (h_halt  : s.halt = .Exception e)
        (h_stack : s.callStack = f :: rest)
      : Step s (s.resumeException f rest)

end EVM
end EvmSemantics
