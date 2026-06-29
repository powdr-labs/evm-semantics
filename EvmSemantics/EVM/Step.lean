module

public import EvmSemantics.EVM.State
public import EvmSemantics.EVM.Decode
public import EvmSemantics.EVM.Gas
public import EvmSemantics.Crypto.Keccak256
public import EvmSemantics.Data.Rlp

/-!
`Step` — the small-step relation, split across three inductives.

* **`StepRunning : State → State → Prop`** holds the per-opcode logic:
  one success constructor per opcode (81) plus generic exception
  constructors parametric over `op` (9). Its constructors do **not**
  carry a `s.halt = .Running` premise — they are meant to be invoked
  only when the caller has separately established that the frame is
  running. The running guard lives on the wrapper `Step.running`
  (below) and on `Eval.stepThen`.
* **`StepReturn : State → State → Prop`** holds the three `callReturn*`
  resume rules. Unlike `StepRunning`, these fire on a *halted* active
  frame whose call stack is non-empty: the child has finished and we
  pop the caller. Each constructor pins the concrete halt kind via
  `h_halt` and `s.callStack = f :: rest` via `h_stack`, so a
  `StepReturn s s'` derivation already implies
  `s.halt ≠ .Running ∧ s.callStack ≠ []`.
* **`Step : State → State → Prop`** is the combined relation used by
  `Eval` / `Steps`. It has two constructors: `running` (which guards a
  `StepRunning` with `s.halt = .Running`) and `returning` (which just
  wraps a `StepReturn`). The 1-of-2 wrapper means the running
  precondition appears *once* in the source, on `Step.running`, rather
  than ninety times.

Each `StepRunning` success rule has the same anatomy:

1. **Decoding hypothesis** — `s.decodedOp = some op`, where
   `s.decodedOp` is the operation-only projection of
   `Decode.decodeAt s.executionEnv.code s.pc.toNat`. Only `pushN` uses
   the full `s.decoded` (it consumes the immediate); everything else
   gets a one-field hypothesis because the immediate-argument slot is
   irrelevant to the rule.
2. **Static-mode hypothesis** (only for state-mutating ops) —
   `s.executionEnv.permitStateMutation = true`.
3. **Gas hypothesis** — `Gas.<op>Total s ... ≤ s.gasAvailable` (or just
   `Gas.baseCost s.fork op ≤ s.gasAvailable` for ops with no dynamic
   piece). Bundles the static base, any memory-expansion delta, and any
   per-byte/per-word dynamic cost into a single `Nat`-valued total, so
   the same identifier appears in the pre-condition and again in the
   post-state's `gasAvailable := s.gasAvailable - <total>`.
4. **Stack-shape hypothesis** — `s.stack = a :: b :: rest` (or similar).
5. **Output-state computation** — a flat record update `{ s with ... }`
   over the fields the opcode touches (stack/pc/gasAvailable and
   whatever else).

*Exception* rules (stack-underflow, out-of-gas, bad-jump, …) sit in the
same `StepRunning` inductive at the bottom. They are parametric in `op`
where possible — one rule per failure mode rather than one per
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

/-- The hash of an account's bytecode (as used by EXTCODEHASH). -/
def Account.codeHash (acc : Account) : UInt256 := keccak256 acc.code

/-- The truthy interpretation of a UInt256 (zero is false, non-zero true). -/
def UInt256.isTrue (a : UInt256) : Prop := a.toNat ≠ 0

instance (a : UInt256) : Decidable (UInt256.isTrue a) :=
  inferInstanceAs (Decidable (a.toNat ≠ 0))

----------------------------------------------------------------------------
-- Contract-address derivation (CREATE / CREATE2).
--
-- Both opcodes derive the new contract's `AccountAddress` by hashing
-- a structured preimage with keccak256 and taking the low 20 bytes
-- (via `AccountAddress.ofUInt256`, which discards the top 12 bytes
-- via `% 2^160`). CREATE's preimage is RLP-encoded so the derivation
-- can fail at the `encodeAddrNonce` step (returning `none` only when
-- the encoded payload would exceed 2^64 bytes — unreachable from
-- gas-bounded EVM execution). CREATE2's preimage is a raw byte
-- concatenation, so its derivation is total.
----------------------------------------------------------------------------

/-- The address of a contract created by `CREATE` from `sender` whose
    pre-bump nonce is `nonce`:
    `AccountAddress.ofUInt256 (keccak256 (rlp [sender, nonce]))`.
    Returns `none` only if `Rlp.encodeAddrNonce` does — in practice
    never, since the encoded payload is `≤ 30` bytes (20-byte address
    + ≤8-byte nonce + RLP overhead). -/
def createAddress (sender : AccountAddress) (nonce : Nat) :
    Option AccountAddress :=
  (Rlp.encodeAddrNonce sender nonce).map (fun rlpBytes =>
    AccountAddress.ofUInt256 (keccak256 rlpBytes))

/-- The address of a contract created by `CREATE2` from `sender`,
    `salt`, and the *pre-hashed* init-code hash (the keccak256 of the
    init bytes the EVM read from memory):
    `AccountAddress.ofUInt256 (keccak256 (0xff || sender || salt || initCodeHash))`. -/
def create2AddressFromHash (sender : AccountAddress) (salt : UInt256)
    (initCodeHash : UInt256) : AccountAddress :=
  AccountAddress.ofUInt256 (keccak256
    (ByteArray.mk #[0xff]
      ++ Rlp.addressBytes sender
      ++ Rlp.uint256ToBytes32 salt
      ++ Rlp.uint256ToBytes32 initCodeHash))

/-- The address of a contract created by `CREATE2` from `sender`,
    `salt`, and the raw `initCode` bytes — hashes `initCode` and
    forwards to `create2AddressFromHash`. -/
def create2Address (sender : AccountAddress) (salt : UInt256)
    (initCode : ByteArray) : AccountAddress :=
  create2AddressFromHash sender salt (keccak256 initCode)

namespace EVM

namespace State

/-- `UInt256`-wrapped `activeWords` value after touching `[off, off+sz)`.
    Bundles the YP's `μ_i` update into a single name for use in
    record-update post-states. -/
@[inline] def activeWordsAfterUInt256 (s : State) (off sz : Nat) : UInt256 :=
  UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat off sz)

/-- Two-range version of `activeWordsAfterUInt256`, used by MCOPY which
    touches both `[off1, off1+sz1)` and `[off2, off2+sz2)`. -/
@[inline] def activeWordsAfterUInt256_2 (s : State) (off1 sz1 off2 sz2 : Nat) : UInt256 :=
  UInt256.ofNat
    (MachineState.activeWordsAfter
      (MachineState.activeWordsAfter s.activeWords.toNat off1 sz1) off2 sz2)

/-- Convenience shorthand for the active fork.
    `abbrev` so it unfolds transparently in proofs. -/
abbrev fork (s : State) : Fork := s.executionEnv.fork

/-- Convenience: the decoded operation (with its optional immediate) at
    the current `pc`. -/
def decoded (s : State) : Option (Operation × Option (UInt256 × Nat)) :=
  Decode.decodeAt s.executionEnv.code s.pc.toNat

/-- Just the decoded operation at the current `pc`, dropping the immediate.
    Used as the `h_op` hypothesis on every `Step` success rule that doesn't
    consume PUSH-style immediate data — most of them — so the constructor
    doesn't have to existentially quantify the unused `arg` slot. -/
@[reducible] def decodedOp (s : State) : Option Operation := s.decoded.map (·.1)

/-- Bridge between `decoded` and `decodedOp`: if the full decode produced
    `(op, imm)` then the op-only projection produces `op`. Used in
    `Equiv.lean` to thread `decodedOp`-shaped premises onto `Step`
    constructors after `stepF` has obtained the `(op, imm)` pair from
    `decoded`. -/
theorem decoded_to_op {s : State} {op : Operation} {imm : Option (UInt256 × Nat)}
    (h : s.decoded = some (op, imm)) : s.decodedOp = some op := by
  simp [decodedOp, h]

end State

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
        (h_gas     : Gas.baseCost s.fork .ADD ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: b :: rest)
      : StepRunning s
          { s with
              stack        := (a + b) :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .ADD }

  /-- MUL: pop `a`, `b`; push `a * b`. -/
  | mul (s : State) (a b : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .MUL)
        (h_gas     : Gas.baseCost s.fork .MUL ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: b :: rest)
      : StepRunning s
          { s with
              stack        := (a * b) :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .MUL }

  /-- SUB: pop `a`, `b`; push `a - b`. -/
  | sub (s : State) (a b : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .SUB)
        (h_gas     : Gas.baseCost s.fork .SUB ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: b :: rest)
      : StepRunning s
          { s with
              stack        := (a - b) :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .SUB }

  /-- DIV: pop `a`, `b`; push `a / b` (0 if `b = 0`). -/
  | div (s : State) (a b : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .DIV)
        (h_gas     : Gas.baseCost s.fork .DIV ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: b :: rest)
      : StepRunning s
          { s with
              stack        := (a / b) :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .DIV }

  /-- SDIV: signed division. -/
  | sdiv (s : State) (a b : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .SDIV)
        (h_gas     : Gas.baseCost s.fork .SDIV ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: b :: rest)
      : StepRunning s
          { s with
              stack        := UInt256.sdiv a b :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .SDIV }

  /-- MOD: pop `a`, `b`; push `a % b` (0 if `b = 0`). -/
  | mod (s : State) (a b : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .MOD)
        (h_gas     : Gas.baseCost s.fork .MOD ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: b :: rest)
      : StepRunning s
          { s with
              stack        := (a % b) :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .MOD }

  /-- SMOD: signed modulo. -/
  | smod (s : State) (a b : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .SMOD)
        (h_gas     : Gas.baseCost s.fork .SMOD ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: b :: rest)
      : StepRunning s
          { s with
              stack        := UInt256.smod a b :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .SMOD }

  /-- ADDMOD: pop `a`, `b`, `n`; push `(a + b) mod n`. -/
  | addmod (s : State) (a b n : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .ADDMOD)
        (h_gas     : Gas.baseCost s.fork .ADDMOD ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: b :: n :: rest)
      : StepRunning s
          { s with
              stack        := UInt256.addMod a b n :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .ADDMOD }

  /-- MULMOD: pop `a`, `b`, `n`; push `(a * b) mod n`. -/
  | mulmod (s : State) (a b n : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .MULMOD)
        (h_gas     : Gas.baseCost s.fork .MULMOD ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: b :: n :: rest)
      : StepRunning s
          { s with
              stack        := UInt256.mulMod a b n :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .MULMOD }

  /-- EXP: pop `a`, `b`; push `a ^ b mod 2^256`. The static portion is the
      Yellow-Paper `G_exp = 10`; `h_dyn_gas` charges the per-byte exponent
      cost `Gas.expByteCost s.fork b` (= `50 · byteLen(b)` post-Spurious-Dragon). -/
  | exp (s : State) (a b : UInt256) (rest : List UInt256)
        (h_op    : s.decodedOp = some .EXP)
        (h_gas   : Gas.baseCost s.fork .EXP + Gas.expByteCost s.fork b ≤ s.gasAvailable)
        (h_stack : s.stack = a :: b :: rest)
      : StepRunning s
          { s with
              stack        := UInt256.exp a b :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .EXP
                              - Gas.expByteCost s.fork b }

  /-- SIGNEXTEND: pop `b`, `x`; sign-extend `x` from byte index `b`. -/
  | signextend (s : State) (b x : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .SIGNEXTEND)
        (h_gas     : Gas.baseCost s.fork .SIGNEXTEND ≤ s.gasAvailable)
        (h_stack   : s.stack = b :: x :: rest)
      : StepRunning s
          { s with
              stack        := UInt256.signExtend b x :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .SIGNEXTEND }

  ----------------------------------------------------------------------------
  -- Comparison & bitwise.
  ----------------------------------------------------------------------------

  | lt (s : State) (a b : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .LT)
        (h_gas     : Gas.baseCost s.fork .LT ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: b :: rest)
      : StepRunning s
          { s with
              stack        := UInt256.lt a b :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .LT }

  | gt (s : State) (a b : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .GT)
        (h_gas     : Gas.baseCost s.fork .GT ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: b :: rest)
      : StepRunning s
          { s with
              stack        := UInt256.gt a b :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .GT }

  | slt (s : State) (a b : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .SLT)
        (h_gas     : Gas.baseCost s.fork .SLT ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: b :: rest)
      : StepRunning s
          { s with
              stack        := UInt256.slt a b :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .SLT }

  | sgt (s : State) (a b : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .SGT)
        (h_gas     : Gas.baseCost s.fork .SGT ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: b :: rest)
      : StepRunning s
          { s with
              stack        := UInt256.sgt a b :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .SGT }

  | eq (s : State) (a b : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .EQ)
        (h_gas     : Gas.baseCost s.fork .EQ ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: b :: rest)
      : StepRunning s
          { s with
              stack        := UInt256.eq a b :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .EQ }

  | iszero (s : State) (a : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .ISZERO)
        (h_gas     : Gas.baseCost s.fork .ISZERO ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: rest)
      : StepRunning s
          { s with
              stack        := UInt256.isZero a :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .ISZERO }

  | and (s : State) (a b : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .AND)
        (h_gas     : Gas.baseCost s.fork .AND ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: b :: rest)
      : StepRunning s
          { s with
              stack        := UInt256.land a b :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .AND }

  | or (s : State) (a b : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .OR)
        (h_gas     : Gas.baseCost s.fork .OR ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: b :: rest)
      : StepRunning s
          { s with
              stack        := UInt256.lor a b :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .OR }

  | xor_ (s : State) (a b : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .XOR)
        (h_gas     : Gas.baseCost s.fork .XOR ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: b :: rest)
      : StepRunning s
          { s with
              stack        := UInt256.xor a b :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .XOR }

  | not (s : State) (a : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .NOT)
        (h_gas     : Gas.baseCost s.fork .NOT ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: rest)
      : StepRunning s
          { s with
              stack        := UInt256.lnot a :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .NOT }

  | byte_ (s : State) (i x : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .BYTE)
        (h_gas     : Gas.baseCost s.fork .BYTE ≤ s.gasAvailable)
        (h_stack   : s.stack = i :: x :: rest)
      : StepRunning s
          { s with
              stack        := UInt256.byteAt i x :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .BYTE }

  | shl (s : State) (shift v : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .SHL)
        (h_gas     : Gas.baseCost s.fork .SHL ≤ s.gasAvailable)
        (h_stack   : s.stack = shift :: v :: rest)
      : StepRunning s
          { s with
              stack        := UInt256.shiftLeft v shift :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .SHL }

  | shr (s : State) (shift v : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .SHR)
        (h_gas     : Gas.baseCost s.fork .SHR ≤ s.gasAvailable)
        (h_stack   : s.stack = shift :: v :: rest)
      : StepRunning s
          { s with
              stack        := UInt256.shiftRight v shift :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .SHR }

  | sar (s : State) (shift v : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .SAR)
        (h_gas     : Gas.baseCost s.fork .SAR ≤ s.gasAvailable)
        (h_stack   : s.stack = shift :: v :: rest)
      : StepRunning s
          { s with
              stack        := UInt256.sar v shift :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .SAR }

  ----------------------------------------------------------------------------
  -- KECCAK256.
  ----------------------------------------------------------------------------

  /-- KECCAK256: pop offset, size; push hash of memory[offset..offset+size].
      `Gas.keccakTotal s offset size` bundles the static `G_keccak256 = 30`,
      the quadratic memory-expansion delta for `[offset, offset+size)`,
      and the per-word cost `6 · ⌈size/32⌉`. Both the pre-condition and the
      post-state's `gasAvailable` use the same identifier, which keeps the
      rule Hoare-triple friendly. -/
  | keccak256 (s : State) (offset size : UInt256) (rest : List UInt256)
        (h_op    : s.decodedOp = some .KECCAK256)
        (h_stack : s.stack = offset :: size :: rest)
        (h_gas   : Gas.keccakTotal s offset size ≤ s.gasAvailable)
      : StepRunning s
          { s with
              stack        := EvmSemantics.keccak256
                                (MachineState.readPadded s.memory
                                  offset.toNat size.toNat) :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.keccakTotal s offset size
              activeWords  := s.activeWordsAfterUInt256 offset.toNat size.toNat }

  ----------------------------------------------------------------------------
  -- Environment reads.
  ----------------------------------------------------------------------------

  | address (s : State)
        (h_op      : s.decodedOp = some .ADDRESS)
        (h_gas     : Gas.baseCost s.fork .ADDRESS ≤ s.gasAvailable)
      : StepRunning s
          { s with
              stack        := s.executionEnv.address.toUInt256 :: s.stack
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .ADDRESS }

  | balance (s : State) (addr : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .BALANCE)
        (h_gas     : Gas.baseCost s.fork .BALANCE ≤ s.gasAvailable)
        (h_stack   : s.stack = addr :: rest)
      : StepRunning s
          { s with
              stack        := (s.accountMap (AccountAddress.ofUInt256 addr)).balance :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .BALANCE }

  | origin (s : State)
        (h_op      : s.decodedOp = some .ORIGIN)
        (h_gas     : Gas.baseCost s.fork .ORIGIN ≤ s.gasAvailable)
      : StepRunning s
          { s with
              stack        := s.executionEnv.origin.toUInt256 :: s.stack
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .ORIGIN }

  | caller (s : State)
        (h_op      : s.decodedOp = some .CALLER)
        (h_gas     : Gas.baseCost s.fork .CALLER ≤ s.gasAvailable)
      : StepRunning s
          { s with
              stack        := s.executionEnv.caller.toUInt256 :: s.stack
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .CALLER }

  | callvalue (s : State)
        (h_op      : s.decodedOp = some .CALLVALUE)
        (h_gas     : Gas.baseCost s.fork .CALLVALUE ≤ s.gasAvailable)
      : StepRunning s
          { s with
              stack        := s.executionEnv.weiValue :: s.stack
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .CALLVALUE }

  /-- CALLDATALOAD: pop `i`; push 32 bytes of calldata starting at `i`,
      zero-padded if past the end. -/
  | calldataload (s : State) (i : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .CALLDATALOAD)
        (h_gas     : Gas.baseCost s.fork .CALLDATALOAD ≤ s.gasAvailable)
        (h_stack   : s.stack = i :: rest)
      : StepRunning s
          { s with
              stack        := MachineState.readWord s.executionEnv.calldata i.toNat :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .CALLDATALOAD }

  | calldatasize (s : State)
        (h_op      : s.decodedOp = some .CALLDATASIZE)
        (h_gas     : Gas.baseCost s.fork .CALLDATASIZE ≤ s.gasAvailable)
      : StepRunning s
          { s with
              stack        := UInt256.ofNat s.executionEnv.calldata.size :: s.stack
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .CALLDATASIZE }

  /-- CALLDATACOPY: pop destOffset, srcOffset, size; copy calldata to memory.
      `Gas.calldatacopyTotal s destOff sz` bundles the static base, the
      memory-expansion delta, and the per-word copy cost `3 · ⌈sz/32⌉`. -/
  | calldatacopy (s : State) (destOff srcOff sz : UInt256) (rest : List UInt256)
        (h_op    : s.decodedOp = some .CALLDATACOPY)
        (h_stack : s.stack = destOff :: srcOff :: sz :: rest)
        (h_gas   : Gas.calldatacopyTotal s destOff sz ≤ s.gasAvailable)
      : StepRunning s
          { s with
              stack        := rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.calldatacopyTotal s destOff sz
              activeWords  := s.activeWordsAfterUInt256 destOff.toNat sz.toNat
              memory       := MachineState.writeBytes s.memory
                                (MachineState.readPadded s.executionEnv.calldata
                                  srcOff.toNat sz.toNat)
                                destOff.toNat }

  | codesize (s : State)
        (h_op      : s.decodedOp = some .CODESIZE)
        (h_gas     : Gas.baseCost s.fork .CODESIZE ≤ s.gasAvailable)
      : StepRunning s
          { s with
              stack        := UInt256.ofNat s.executionEnv.code.size :: s.stack
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .CODESIZE }

  /-- CODECOPY: pop destOffset, srcOffset, size; copy current code to memory.
      `Gas.codecopyTotal s destOff sz` bundles the static base, the
      memory-expansion delta, and the per-word copy cost `3 · ⌈sz/32⌉`. -/
  | codecopy (s : State) (destOff srcOff sz : UInt256) (rest : List UInt256)
        (h_op    : s.decodedOp = some .CODECOPY)
        (h_stack : s.stack = destOff :: srcOff :: sz :: rest)
        (h_gas   : Gas.codecopyTotal s destOff sz ≤ s.gasAvailable)
      : StepRunning s
          { s with
              stack        := rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.codecopyTotal s destOff sz
              activeWords  := s.activeWordsAfterUInt256 destOff.toNat sz.toNat
              memory       := MachineState.writeBytes s.memory
                                (MachineState.readPadded s.executionEnv.code
                                  srcOff.toNat sz.toNat)
                                destOff.toNat }

  | gasprice (s : State)
        (h_op      : s.decodedOp = some .GASPRICE)
        (h_gas     : Gas.baseCost s.fork .GASPRICE ≤ s.gasAvailable)
      : StepRunning s
          { s with
              stack        := s.executionEnv.gasPrice :: s.stack
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .GASPRICE }

  | extcodesize (s : State) (addr : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .EXTCODESIZE)
        (h_gas     : Gas.baseCost s.fork .EXTCODESIZE ≤ s.gasAvailable)
        (h_stack   : s.stack = addr :: rest)
      : StepRunning s
          { s with
              stack        := UInt256.ofNat
                                (s.accountMap (AccountAddress.ofUInt256 addr)).code.size
                              :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .EXTCODESIZE }

  /-- EXTCODECOPY: pop addr, destOffset, srcOffset, size; copy external
      code bytes to memory. `Gas.extcodecopyTotal s destOff sz` bundles
      the static base, the memory-expansion delta, and the per-word copy
      cost `3 · ⌈sz/32⌉`. -/
  | extcodecopy (s : State) (addr destOff srcOff sz : UInt256) (rest : List UInt256)
        (h_op    : s.decodedOp = some .EXTCODECOPY)
        (h_stack : s.stack = addr :: destOff :: srcOff :: sz :: rest)
        (h_gas   : Gas.extcodecopyTotal s destOff sz ≤ s.gasAvailable)
      : StepRunning s
          { s with
              stack        := rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.extcodecopyTotal s destOff sz
              activeWords  := s.activeWordsAfterUInt256 destOff.toNat sz.toNat
              memory       := MachineState.writeBytes s.memory
                                (MachineState.readPadded
                                  (s.accountMap (AccountAddress.ofUInt256 addr)).code
                                  srcOff.toNat sz.toNat)
                                destOff.toNat }

  | returndatasize (s : State)
        (h_op      : s.decodedOp = some .RETURNDATASIZE)
        (h_gas     : Gas.baseCost s.fork .RETURNDATASIZE ≤ s.gasAvailable)
      : StepRunning s
          { s with
              stack        := UInt256.ofNat s.returnData.size :: s.stack
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .RETURNDATASIZE }

  /-- RETURNDATACOPY: pop destOffset, srcOffset, size; copy returndata to memory.
      Out-of-bounds reads raise `InvalidMemoryAccess` (handled in Phase 5).
      `Gas.returndatacopyTotal s destOff sz` bundles the static base, the
      memory-expansion delta, and the per-word copy cost `3 · ⌈sz/32⌉`. -/
  | returndatacopy (s : State) (destOff srcOff sz : UInt256) (rest : List UInt256)
        (h_op       : s.decodedOp = some .RETURNDATACOPY)
        (h_stack    : s.stack = destOff :: srcOff :: sz :: rest)
        (h_inbounds : srcOff.toNat + sz.toNat ≤ s.returnData.size)
        (h_gas      : Gas.returndatacopyTotal s destOff sz ≤ s.gasAvailable)
      : StepRunning s
          { s with
              stack        := rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.returndatacopyTotal s destOff sz
              activeWords  := s.activeWordsAfterUInt256 destOff.toNat sz.toNat
              memory       := MachineState.writeBytes s.memory
                                (MachineState.readPadded s.returnData
                                  srcOff.toNat sz.toNat)
                                destOff.toNat }

  | extcodehash (s : State) (addr : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .EXTCODEHASH)
        (h_gas     : Gas.baseCost s.fork .EXTCODEHASH ≤ s.gasAvailable)
        (h_stack   : s.stack = addr :: rest)
      : StepRunning s
          { s with
              stack        := (s.accountMap (AccountAddress.ofUInt256 addr)).codeHash :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .EXTCODEHASH }

  ----------------------------------------------------------------------------
  -- Block-context reads.
  ----------------------------------------------------------------------------

  | blockhash (s : State) (n : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .BLOCKHASH)
        (h_gas     : Gas.baseCost s.fork .BLOCKHASH ≤ s.gasAvailable)
        (h_stack   : s.stack = n :: rest)
      : StepRunning s
          { s with
              stack        := s.executionEnv.header.blockHash n :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .BLOCKHASH }

  | coinbase (s : State)
        (h_op      : s.decodedOp = some .COINBASE)
        (h_gas     : Gas.baseCost s.fork .COINBASE ≤ s.gasAvailable)
      : StepRunning s
          { s with
              stack        := s.executionEnv.header.coinbase.toUInt256 :: s.stack
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .COINBASE }

  | timestamp (s : State)
        (h_op      : s.decodedOp = some .TIMESTAMP)
        (h_gas     : Gas.baseCost s.fork .TIMESTAMP ≤ s.gasAvailable)
      : StepRunning s
          { s with
              stack        := s.executionEnv.header.timestamp :: s.stack
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .TIMESTAMP }

  | number (s : State)
        (h_op      : s.decodedOp = some .NUMBER)
        (h_gas     : Gas.baseCost s.fork .NUMBER ≤ s.gasAvailable)
      : StepRunning s
          { s with
              stack        := s.executionEnv.header.number :: s.stack
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .NUMBER }

  | prevrandao (s : State)
        (h_op      : s.decodedOp = some .PREVRANDAO)
        (h_gas     : Gas.baseCost s.fork .PREVRANDAO ≤ s.gasAvailable)
      : StepRunning s
          { s with
              stack        := s.executionEnv.header.prevRandao :: s.stack
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .PREVRANDAO }

  | gaslimit (s : State)
        (h_op      : s.decodedOp = some .GASLIMIT)
        (h_gas     : Gas.baseCost s.fork .GASLIMIT ≤ s.gasAvailable)
      : StepRunning s
          { s with
              stack        := s.executionEnv.header.gasLimit :: s.stack
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .GASLIMIT }

  | chainid (s : State)
        (h_op      : s.decodedOp = some .CHAINID)
        (h_gas     : Gas.baseCost s.fork .CHAINID ≤ s.gasAvailable)
      : StepRunning s
          { s with
              stack        := s.executionEnv.header.chainId :: s.stack
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .CHAINID }

  | selfbalance (s : State)
        (h_op      : s.decodedOp = some .SELFBALANCE)
        (h_gas     : Gas.baseCost s.fork .SELFBALANCE ≤ s.gasAvailable)
      : StepRunning s
          { s with
              stack        := (s.accountMap s.executionEnv.address).balance :: s.stack
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .SELFBALANCE }

  | basefee (s : State)
        (h_op      : s.decodedOp = some .BASEFEE)
        (h_gas     : Gas.baseCost s.fork .BASEFEE ≤ s.gasAvailable)
      : StepRunning s
          { s with
              stack        := s.executionEnv.header.baseFeePerGas :: s.stack
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .BASEFEE }

  | blobhash (s : State) (i : UInt256) (rest : List UInt256) (h : UInt256)
        (h_op      : s.decodedOp = some .BLOBHASH)
        (h_gas     : Gas.baseCost s.fork .BLOBHASH ≤ s.gasAvailable)
        (h_stack   : s.stack = i :: rest)
        (h_get     : s.executionEnv.blobVersionedHashes[i.toNat]? = some h)
      : StepRunning s
          { s with
              stack        := h :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .BLOBHASH }

  /-- BLOBHASH when index is out of range — push 0. -/
  | blobhash_oob (s : State) (i : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .BLOBHASH)
        (h_gas     : Gas.baseCost s.fork .BLOBHASH ≤ s.gasAvailable)
        (h_stack   : s.stack = i :: rest)
        (h_oob     : s.executionEnv.blobVersionedHashes[i.toNat]? = none)
      : StepRunning s
          { s with
              stack        := ⟨0⟩ :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .BLOBHASH }

  | blobbasefee (s : State)
        (h_op      : s.decodedOp = some .BLOBBASEFEE)
        (h_gas     : Gas.baseCost s.fork .BLOBBASEFEE ≤ s.gasAvailable)
      : StepRunning s
          { s with
              stack        := s.executionEnv.header.blobBaseFee :: s.stack
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .BLOBBASEFEE }

  ----------------------------------------------------------------------------
  -- Stack manipulation: POP, PUSHk, DUPn, SWAPn.
  ----------------------------------------------------------------------------

  | pop (s : State) (a : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .POP)
        (h_gas     : Gas.baseCost s.fork .POP ≤ s.gasAvailable)
        (h_stack   : s.stack = a :: rest)
      : StepRunning s
          { s with
              stack        := rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .POP }

  /-- PUSH0: push `0`. -/
  | push0 (s : State)
        (h_op      : s.decodedOp = some (.Push ⟨0, by decide⟩))
        (h_gas     : Gas.baseCost s.fork (.Push ⟨0, by decide⟩) ≤ s.gasAvailable)
      : StepRunning s
          { s with
              stack        := ⟨0⟩ :: s.stack
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork (.Push ⟨0, by decide⟩) }

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
        (h_gas     : Gas.baseCost s.fork (.Push ⟨k, k.isLt⟩) ≤ s.gasAvailable)
      : StepRunning s
          { s with
              stack        := data :: s.stack
              pc           := s.pc + UInt256.ofNat (immWidth + 1)
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork (.Push ⟨k, k.isLt⟩) }

  /-- DUPn: copy `stack[n]` (0-indexed from top) to the top. -/
  | dup (s : State) (n : Fin 16) (v : UInt256)
        (h_op      : s.decodedOp = some (.Dup ⟨n⟩))
        (h_gas     : Gas.baseCost s.fork (.Dup ⟨n⟩) ≤ s.gasAvailable)
        (h_get     : s.stack[n.val]? = some v)
      : StepRunning s
          { s with
              stack        := v :: s.stack
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork (.Dup ⟨n⟩) }

  /-- SWAPn: swap top with `stack[n+1]`. -/
  | swap (s : State) (n : Fin 16) (stk' : List UInt256)
        (h_op      : s.decodedOp = some (.Swap ⟨n⟩))
        (h_gas     : Gas.baseCost s.fork (.Swap ⟨n⟩) ≤ s.gasAvailable)
        (h_swap    : s.stack.exchange 0 (n.val + 1) = some stk')
      : StepRunning s
          { s with
              stack        := stk'
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork (.Swap ⟨n⟩) }

  ----------------------------------------------------------------------------
  -- Memory.
  ----------------------------------------------------------------------------

  /-- MLOAD: pop offset; push the 32-byte word at memory[offset].
      `Gas.mloadTotal s offset` bundles the static base and the
      memory-expansion delta for the fixed 32-byte read window. -/
  | mload (s : State) (offset : UInt256) (rest : List UInt256)
        (h_op    : s.decodedOp = some .MLOAD)
        (h_stack : s.stack = offset :: rest)
        (h_gas   : Gas.mloadTotal s offset ≤ s.gasAvailable)
      : StepRunning s
          { s with
              stack        := MachineState.readWord s.memory offset.toNat :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.mloadTotal s offset
              activeWords  := s.activeWordsAfterUInt256 offset.toNat 32 }

  /-- MSTORE: pop offset, value; write `value` as 32 bytes at memory[offset].
      `Gas.mstoreTotal s offset` bundles the static base and the
      memory-expansion delta for the fixed 32-byte write window. -/
  | mstore (s : State) (offset value : UInt256) (rest : List UInt256)
        (h_op    : s.decodedOp = some .MSTORE)
        (h_stack : s.stack = offset :: value :: rest)
        (h_gas   : Gas.mstoreTotal s offset ≤ s.gasAvailable)
      : StepRunning s
          { s with
              stack        := rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.mstoreTotal s offset
              memory       := MachineState.writeBytes s.memory
                                (MachineState.wordBytes value) offset.toNat
              activeWords  := s.activeWordsAfterUInt256 offset.toNat 32 }

  /-- MSTORE8: pop offset, value; write the low byte of `value` at memory[offset].
      `Gas.mstore8Total s offset` bundles the static base and the
      memory-expansion delta for the 1-byte write. -/
  | mstore8 (s : State) (offset value : UInt256) (rest : List UInt256)
        (h_op    : s.decodedOp = some .MSTORE8)
        (h_stack : s.stack = offset :: value :: rest)
        (h_gas   : Gas.mstore8Total s offset ≤ s.gasAvailable)
      : StepRunning s
          { s with
              stack        := rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.mstore8Total s offset
              memory       := MachineState.writeBytes s.memory
                                (ByteArray.mk #[UInt8.ofNat (value.toNat % 256)])
                                offset.toNat
              activeWords  := s.activeWordsAfterUInt256 offset.toNat 1 }

  | msize (s : State)
        (h_op      : s.decodedOp = some .MSIZE)
        (h_gas     : Gas.baseCost s.fork .MSIZE ≤ s.gasAvailable)
      : StepRunning s
          { s with
              stack        := MachineState.msize s.toMachineState :: s.stack
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .MSIZE }

  /-- MCOPY: pop destOffset, srcOffset, size; copy memory[src..src+sz] to dest.
      Touches *both* the read range `[srcOff, srcOff+sz)` and the write range
      `[destOff, destOff+sz)`; `Gas.mcopyTotal s destOff srcOff sz` bundles
      the static base, the expansion delta for their union, and the
      per-word copy cost `3 · ⌈sz/32⌉`. -/
  | mcopy (s : State) (destOff srcOff sz : UInt256) (rest : List UInt256)
        (h_op    : s.decodedOp = some .MCOPY)
        (h_stack : s.stack = destOff :: srcOff :: sz :: rest)
        (h_gas   : Gas.mcopyTotal s destOff srcOff sz ≤ s.gasAvailable)
      : StepRunning s
          { s with
              stack        := rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.mcopyTotal s destOff srcOff sz
              memory       := MachineState.writeBytes s.memory
                                (MachineState.readPadded s.memory
                                  srcOff.toNat sz.toNat)
                                destOff.toNat
              activeWords  := s.activeWordsAfterUInt256_2
                                destOff.toNat sz.toNat srcOff.toNat sz.toNat }

  ----------------------------------------------------------------------------
  -- Storage (persistent and transient).
  ----------------------------------------------------------------------------

  /-- SLOAD: pop key; push storage[key] from the executing contract. -/
  | sload (s : State) (key : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .SLOAD)
        (h_gas     : Gas.baseCost s.fork .SLOAD ≤ s.gasAvailable)
        (h_stack   : s.stack = key :: rest)
      : StepRunning s
          { s with
              stack        := ((s.accountMap s.executionEnv.address).storage key) :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .SLOAD }

  /-- SSTORE: pop key, value; write storage[key] := value. Requires
      static-mode permission. `Gas.sstoreTotal s key value` bundles the
      (zero) static base and the EIP-2200 net-metered dynamic cost.
      `h_sentry` enforces the EIP-2200 stipend sentry (Cancun only). -/
  | sstore (s : State) (key value : UInt256) (rest : List UInt256)
        (h_op     : s.decodedOp = some .SSTORE)
        (h_perm   : s.executionEnv.permitStateMutation = true)
        (h_stack  : s.stack = key :: value :: rest)
        (h_sentry : Gas.sstoreSentry s.fork
                      (s.gasAvailable - Gas.baseCost s.fork .SSTORE) = false)
        (h_gas    : Gas.sstoreTotal s key value ≤ s.gasAvailable)
      : StepRunning s
          { s with
              stack        := rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.sstoreTotal s key value
              accountMap   := s.accountMap.set s.executionEnv.address
                                { s.accountMap s.executionEnv.address with
                                    storage := (s.accountMap s.executionEnv.address).storage.set
                                                 key value } }

  /-- TLOAD: like SLOAD but reads from transient storage. -/
  | tload (s : State) (key : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .TLOAD)
        (h_gas     : Gas.baseCost s.fork .TLOAD ≤ s.gasAvailable)
        (h_stack   : s.stack = key :: rest)
      : StepRunning s
          { s with
              stack        := ((s.accountMap s.executionEnv.address).tstorage key) :: rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .TLOAD }

  /-- TSTORE: like SSTORE but writes to transient storage. -/
  | tstore (s : State) (key value : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .TSTORE)
        (h_perm    : s.executionEnv.permitStateMutation = true)
        (h_gas     : Gas.baseCost s.fork .TSTORE ≤ s.gasAvailable)
        (h_stack   : s.stack = key :: value :: rest)
      : StepRunning s
          { s with
              stack        := rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .TSTORE
              accountMap   := s.accountMap.set s.executionEnv.address
                                { s.accountMap s.executionEnv.address with
                                    tstorage :=
                                      (s.accountMap s.executionEnv.address).tstorage.set
                                        key value } }

  ----------------------------------------------------------------------------
  -- Control flow: JUMP, JUMPI, JUMPDEST, PC, GAS.
  ----------------------------------------------------------------------------

  /-- JUMP: pop destination; set `pc := dest` if the destination is a
      `JUMPDEST` *as an instruction boundary* — a `0x5b` byte sitting inside
      a PUSH immediate is rejected by the jumpdest analysis. -/
  | jump (s : State) (dest : UInt256) (rest : List UInt256)
        (h_op    : s.decodedOp = some .JUMP)
        (h_gas   : Gas.baseCost s.fork .JUMP ≤ s.gasAvailable)
        (h_stack : s.stack = dest :: rest)
        (h_valid : Decode.isValidJumpDest s.executionEnv.code dest.toNat = true)
      : StepRunning s
          { s with
              stack        := rest
              pc           := dest
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .JUMP }

  /-- JUMPI (taken): pop dest, cond; if `cond ≠ 0` and dest is a valid
      `JUMPDEST` (instruction boundary, not push-data), set `pc := dest`. -/
  | jumpi_taken (s : State) (dest cond : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .JUMPI)
        (h_gas     : Gas.baseCost s.fork .JUMPI ≤ s.gasAvailable)
        (h_stack   : s.stack = dest :: cond :: rest)
        (h_cond    : UInt256.isTrue cond)
        (h_valid   : Decode.isValidJumpDest s.executionEnv.code dest.toNat = true)
      : StepRunning s
          { s with
              stack        := rest
              pc           := dest
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .JUMPI }

  /-- JUMPI (not taken): pop dest, cond; if `cond = 0`, fall through to `pc + 1`. -/
  | jumpi_notTaken (s : State) (dest cond : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .JUMPI)
        (h_gas     : Gas.baseCost s.fork .JUMPI ≤ s.gasAvailable)
        (h_stack   : s.stack = dest :: cond :: rest)
        (h_cond    : ¬ UInt256.isTrue cond)
      : StepRunning s
          { s with
              stack        := rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .JUMPI }

  | pc (s : State)
        (h_op      : s.decodedOp = some .PC)
        (h_gas     : Gas.baseCost s.fork .PC ≤ s.gasAvailable)
      : StepRunning s
          { s with
              stack        := s.pc :: s.stack
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .PC }

  /-- GAS pushes the remaining gas *after* the opcode's own 2-gas cost is
      deducted (Yellow Paper §9.4.7 / EIP-150), so we read the post-charge
      `s'.gasAvailable` rather than the original `s.gasAvailable`. -/
  | gas (s : State)
        (h_op      : s.decodedOp = some .GAS)
        (h_gas     : Gas.baseCost s.fork .GAS ≤ s.gasAvailable)
      : StepRunning s
          { s with
              stack        := UInt256.ofNat (s.gasAvailable - Gas.baseCost s.fork .GAS)
                                :: s.stack
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .GAS }

  | jumpdest (s : State)
        (h_op      : s.decodedOp = some .JUMPDEST)
        (h_gas     : Gas.baseCost s.fork .JUMPDEST ≤ s.gasAvailable)
      : StepRunning s
          { s with
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork .JUMPDEST }

  ----------------------------------------------------------------------------
  -- Halts: STOP, RETURN, REVERT.
  ----------------------------------------------------------------------------

  | stop (s : State)
        (h_op      : s.decodedOp = some .STOP)
      : StepRunning s { s with halt := .Success, hReturn := .empty }

  | return_ (s : State) (offset size : UInt256) (rest : List UInt256)
        (h_op    : s.decodedOp = some .RETURN)
        (h_stack : s.stack = offset :: size :: rest)
        (h_gas   : Gas.returnTotal s offset size ≤ s.gasAvailable)
      : StepRunning s
          { s with
              halt         := .Returned
              hReturn      := MachineState.readPadded s.memory offset.toNat size.toNat
              stack        := rest
              gasAvailable := s.gasAvailable - Gas.returnTotal s offset size
              activeWords  := s.activeWordsAfterUInt256 offset.toNat size.toNat }

  | revert (s : State) (offset size : UInt256) (rest : List UInt256)
        (h_op    : s.decodedOp = some .REVERT)
        (h_stack : s.stack = offset :: size :: rest)
        (h_gas   : Gas.revertTotal s offset size ≤ s.gasAvailable)
      : StepRunning s
          { s with
              halt         := .Reverted
              hReturn      := MachineState.readPadded s.memory offset.toNat size.toNat
              stack        := rest
              gasAvailable := s.gasAvailable - Gas.revertTotal s offset size
              activeWords  := s.activeWordsAfterUInt256 offset.toNat size.toNat }

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
      : StepRunning s ({ s with halt := .Exception .StaticModeViolation })

  /-- CALL (taken): pop the 7 args; charge base (`G_call`), memory expansion for
      the args+return ranges, and the value/new-account surcharge; check the
      depth limit and caller balance; forward 63/64 of the remaining gas plus
      the value stipend; transfer `value`; and enter the callee frame.
      `Gas.callCommitted s value argsOff argsLen retOff retLen toArg` bundles
      the unconditional pre-forwarding charge (base + memory + surcharge). -/
  | call (s : State)
        (gasArg toArg value argsOff argsLen retOff retLen : UInt256)
        (rest : List UInt256) (forwarded : Nat)
        (h_op       : s.decodedOp = some .CALL)
        (h_stack    : s.stack =
                        gasArg :: toArg :: value :: argsOff :: argsLen :: retOff :: retLen :: rest)
        (h_gas      : Gas.callCommitted s value argsOff argsLen retOff retLen toArg
                        ≤ s.gasAvailable)
        (h_take     : ¬ (s.executionEnv.depth ≥ 1024 ∨
                         (s.accountMap s.executionEnv.address).balance < value))
        (h_fwd      : forwarded = min gasArg.toNat (Gas.allButOneSixtyFourth
                        s.executionEnv.fork
                        (s.gasAvailable
                          - Gas.callCommitted s value argsOff argsLen retOff retLen toArg)))
      : StepRunning s
          (({ s with
                gasAvailable := s.gasAvailable
                                - Gas.callCommitted s value argsOff argsLen retOff retLen toArg
                                - forwarded
                activeWords  := s.activeWordsAfterUInt256_2
                                  argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat }
           ).enterCall rest (AccountAddress.ofUInt256 toArg) value
             (MachineState.readPadded s.memory argsOff.toNat argsLen.toNat)
             (s.accountMap (AccountAddress.ofUInt256 toArg)).code
             (forwarded + (bif (value.toNat != 0) then Gas.callStipend else 0))
             retOff.toNat retLen.toNat)

  /-- CALL (not taken): the depth limit is hit or the caller cannot afford the
      value. Base+memory+surcharge gas is still charged; `0` is pushed and the
      forwarded gas is *not* spent. -/
  | callFail (s : State)
        (gasArg toArg value argsOff argsLen retOff retLen : UInt256)
        (rest : List UInt256)
        (h_op    : s.decodedOp = some .CALL)
        (h_stack : s.stack =
                     gasArg :: toArg :: value :: argsOff :: argsLen :: retOff :: retLen :: rest)
        (h_gas   : Gas.callCommitted s value argsOff argsLen retOff retLen toArg
                     ≤ s.gasAvailable)
        (h_fail  : s.executionEnv.depth ≥ 1024 ∨
                     (s.accountMap s.executionEnv.address).balance < value)
      : StepRunning s
          ({ s with
              gasAvailable := s.gasAvailable
                              - Gas.callCommitted s value argsOff argsLen retOff retLen toArg
              activeWords  := s.activeWordsAfterUInt256_2
                                argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat
              returnData   := .empty
              stack        := UInt256.ofNat 0 :: rest
              pc           := s.pc.succ })

  /-- CALLCODE (taken): like `call`, but the callee runs in the *caller's*
      storage/address context (its `address` is unchanged) using the target
      account's code. Value is "transferred" caller→caller, i.e. a no-op on
      balances. CALLCODE never creates a new account, so the surcharge uses
      `targetEmpty = false`. Note the **absence** of a `callcodeStatic`
      sibling (compare `call` / `callStatic`): a value-transferring CALLCODE
      in a static frame is *not* rejected because the self-transfer is a
      no-op on world state — no real state mutation occurs at this opcode,
      and the static flag still propagates into the callee frame via
      `permitStateMutation`. -/
  | callcode (s : State)
        (gasArg toArg value argsOff argsLen retOff retLen : UInt256)
        (rest : List UInt256) (forwarded : Nat)
        (h_op    : s.decodedOp = some .CALLCODE)
        (h_stack : s.stack =
                     gasArg :: toArg :: value :: argsOff :: argsLen :: retOff :: retLen :: rest)
        (h_gas   : Gas.callcodeCommitted s value argsOff argsLen retOff retLen
                     ≤ s.gasAvailable)
        (h_take  : ¬ (s.executionEnv.depth ≥ 1024 ∨
                      (s.accountMap s.executionEnv.address).balance < value))
        (h_fwd   : forwarded = min gasArg.toNat (Gas.allButOneSixtyFourth
                     s.executionEnv.fork
                     (s.gasAvailable
                       - Gas.callcodeCommitted s value argsOff argsLen retOff retLen)))
      : StepRunning s
          (({ s with
                gasAvailable := s.gasAvailable
                                - Gas.callcodeCommitted s value argsOff argsLen retOff retLen
                                - forwarded
                activeWords  := s.activeWordsAfterUInt256_2
                                  argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat }
           ).enterCall rest s.executionEnv.address value
             (MachineState.readPadded s.memory argsOff.toNat argsLen.toNat)
             (s.accountMap (AccountAddress.ofUInt256 toArg)).code
             (forwarded + (bif (value.toNat != 0) then Gas.callStipend else 0))
             retOff.toNat retLen.toNat)

  /-- CALLCODE (not taken): depth limit hit or caller cannot afford the value.
      Base+memory+surcharge gas is still charged; `0` is pushed; the forwarded
      gas is *not* spent. -/
  | callcodeFail (s : State)
        (gasArg toArg value argsOff argsLen retOff retLen : UInt256)
        (rest : List UInt256)
        (h_op    : s.decodedOp = some .CALLCODE)
        (h_stack : s.stack =
                     gasArg :: toArg :: value :: argsOff :: argsLen :: retOff :: retLen :: rest)
        (h_gas   : Gas.callcodeCommitted s value argsOff argsLen retOff retLen
                     ≤ s.gasAvailable)
        (h_fail  : s.executionEnv.depth ≥ 1024 ∨
                     (s.accountMap s.executionEnv.address).balance < value)
      : StepRunning s
          ({ s with
              gasAvailable := s.gasAvailable
                              - Gas.callcodeCommitted s value argsOff argsLen retOff retLen
              activeWords  := s.activeWordsAfterUInt256_2
                                argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat
              returnData   := .empty
              stack        := UInt256.ofNat 0 :: rest
              pc           := s.pc.succ })

  ----------------------------------------------------------------------------
  -- DELEGATECALL / STATICCALL. Both pop *six* stack items (no `value`).
  -- The differences from `call` / `callcode` live in the per-kind
  -- `CallKind.*` helpers in `State.lean`; both arms use `enterCallFor`
  -- to install the callee frame.
  --
  -- Neither opcode transfers value, so there's no balance check and no
  -- new-account surcharge — `Gas.callSurcharge false false = 0` for both.
  -- We still gate on the depth limit (≥ 1024 pushes 0 instead of entering).
  ----------------------------------------------------------------------------

  /-- DELEGATECALL (taken): runs the target's code in the *caller's*
      context (address unchanged), inheriting the caller's `source` and
      `weiValue` — i.e. the callee sees the same `msg.sender` and
      `CALLVALUE` as the caller did. No value parameter; no transfer;
      no stipend. -/
  | delegatecall (s : State)
        (gasArg toArg argsOff argsLen retOff retLen : UInt256)
        (rest : List UInt256) (forwarded : Nat)
        (h_op    : s.decodedOp = some .DELEGATECALL)
        (h_stack : s.stack =
                     gasArg :: toArg :: argsOff :: argsLen :: retOff :: retLen :: rest)
        (h_gas   : Gas.delegatecallCommitted s argsOff argsLen retOff retLen
                     ≤ s.gasAvailable)
        (h_take  : ¬ s.executionEnv.depth ≥ 1024)
        (h_fwd   : forwarded = min gasArg.toNat (Gas.allButOneSixtyFourth
                     s.executionEnv.fork
                     (s.gasAvailable
                       - Gas.delegatecallCommitted s argsOff argsLen retOff retLen)))
      : StepRunning s
          (({ s with
                gasAvailable := s.gasAvailable
                                - Gas.delegatecallCommitted s argsOff argsLen retOff retLen
                                - forwarded
                activeWords  := s.activeWordsAfterUInt256_2
                                  argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat }
           ).enterCallFor .DelegateCall rest (AccountAddress.ofUInt256 toArg)
             ⟨0⟩  -- value is irrelevant: weiValue is inherited
             (MachineState.readPadded s.memory argsOff.toNat argsLen.toNat)
             (s.accountMap (AccountAddress.ofUInt256 toArg)).code
             forwarded retOff.toNat retLen.toNat)

  /-- DELEGATECALL (not taken): depth limit hit. Base + memory gas is still
      spent; `0` is pushed and `returnData` cleared. -/
  | delegatecallFail (s : State)
        (gasArg toArg argsOff argsLen retOff retLen : UInt256)
        (rest : List UInt256)
        (h_op    : s.decodedOp = some .DELEGATECALL)
        (h_stack : s.stack =
                     gasArg :: toArg :: argsOff :: argsLen :: retOff :: retLen :: rest)
        (h_gas   : Gas.delegatecallCommitted s argsOff argsLen retOff retLen
                     ≤ s.gasAvailable)
        (h_fail  : s.executionEnv.depth ≥ 1024)
      : StepRunning s
          ({ s with
              gasAvailable := s.gasAvailable
                              - Gas.delegatecallCommitted s argsOff argsLen retOff retLen
              activeWords  := s.activeWordsAfterUInt256_2
                                argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat
              returnData   := .empty
              stack        := UInt256.ofNat 0 :: rest
              pc           := s.pc.succ })

  /-- STATICCALL (taken): runs the target's code in the target's context
      (address = target), but forces `permitStateMutation = false` in
      the callee frame so any state-mutating opcode raises
      `StaticModeViolation`. No value parameter; the callee sees
      `CALLVALUE = 0`. -/
  | staticcall (s : State)
        (gasArg toArg argsOff argsLen retOff retLen : UInt256)
        (rest : List UInt256) (forwarded : Nat)
        (h_op    : s.decodedOp = some .STATICCALL)
        (h_stack : s.stack =
                     gasArg :: toArg :: argsOff :: argsLen :: retOff :: retLen :: rest)
        (h_gas   : Gas.staticcallCommitted s argsOff argsLen retOff retLen
                     ≤ s.gasAvailable)
        (h_take  : ¬ s.executionEnv.depth ≥ 1024)
        (h_fwd   : forwarded = min gasArg.toNat (Gas.allButOneSixtyFourth
                     s.executionEnv.fork
                     (s.gasAvailable
                       - Gas.staticcallCommitted s argsOff argsLen retOff retLen)))
      : StepRunning s
          (({ s with
                gasAvailable := s.gasAvailable
                                - Gas.staticcallCommitted s argsOff argsLen retOff retLen
                                - forwarded
                activeWords  := s.activeWordsAfterUInt256_2
                                  argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat }
           ).enterCallFor .StaticCall rest (AccountAddress.ofUInt256 toArg)
             ⟨0⟩
             (MachineState.readPadded s.memory argsOff.toNat argsLen.toNat)
             (s.accountMap (AccountAddress.ofUInt256 toArg)).code
             forwarded retOff.toNat retLen.toNat)

  /-- STATICCALL (not taken): depth limit hit. -/
  | staticcallFail (s : State)
        (gasArg toArg argsOff argsLen retOff retLen : UInt256)
        (rest : List UInt256)
        (h_op    : s.decodedOp = some .STATICCALL)
        (h_stack : s.stack =
                     gasArg :: toArg :: argsOff :: argsLen :: retOff :: retLen :: rest)
        (h_gas   : Gas.staticcallCommitted s argsOff argsLen retOff retLen
                     ≤ s.gasAvailable)
        (h_fail  : s.executionEnv.depth ≥ 1024)
      : StepRunning s
          ({ s with
              gasAvailable := s.gasAvailable
                              - Gas.staticcallCommitted s argsOff argsLen retOff retLen
              activeWords  := s.activeWordsAfterUInt256_2
                                argsOff.toNat argsLen.toNat retOff.toNat retLen.toNat
              returnData   := .empty
              stack        := UInt256.ofNat 0 :: rest
              pc           := s.pc.succ })

  ----------------------------------------------------------------------------
  -- CREATE / CREATE2: install a new contract.
  --
  -- Both opcodes share a five-branch shape: static-mode rejection, OOG
  -- on memory expansion (caught by the generic `outOfGas` rule on the
  -- surrounding `chargeMem`), pre-execution failure (depth ≥ 1024 or
  -- caller balance < value), address-collision failure, and the taken
  -- path. CREATE2 also rejects when its initcode-hash cost can't be
  -- paid (also a generic `outOfGas`).
  --
  -- Address derivation differs:
  --   * CREATE  : keccak256(rlp([sender, sender.nonce]))[12:]
  --   * CREATE2 : keccak256(0xff || sender || salt || keccak256(init))[12:]
  -- Otherwise the bookkeeping (nonce bump on collision, transfer +
  -- enterCreate on take) is identical.
  ----------------------------------------------------------------------------

  /-- CREATE attempted in a static frame. Halts with `StaticModeViolation`
      *before* paying gas. -/
  | createStatic (s : State)
        (value offset size : UInt256) (rest : List UInt256)
        (h_op    : s.decodedOp = some .CREATE)
        (h_stack : s.stack = value :: offset :: size :: rest)
        (h_perm  : s.executionEnv.permitStateMutation = false)
      : StepRunning s ({ s with halt := .Exception .StaticModeViolation })

  /-- CREATE (not taken — depth limit or insufficient balance): base gas
      and memory-expansion gas are still paid, sender nonce is **not**
      bumped, no transfer, no frame entry. `0` is pushed. -/
  | createFail (s : State)
        (value offset size : UInt256) (rest : List UInt256)
        (h_op    : s.decodedOp = some .CREATE)
        (h_stack : s.stack = value :: offset :: size :: rest)
        (h_perm  : s.executionEnv.permitStateMutation = true)
        (h_gas   : Gas.createCommitted s offset size ≤ s.gasAvailable)
        (h_fail  : s.executionEnv.depth ≥ 1024 ∨
                     (s.accountMap s.executionEnv.address).balance < value)
      : StepRunning s
          { s with
              gasAvailable := s.gasAvailable - Gas.createCommitted s offset size
              activeWords  := s.activeWordsAfterUInt256 offset.toNat size.toNat
              returnData   := .empty
              stack        := UInt256.ofNat 0 :: rest
              pc           := s.pc.succ }

  /-- CREATE (address collision): the derived `newAddr` already hosts a
      contract (code or nonce > 0). The caller's nonce is bumped, `0` is
      pushed, and no transfer or frame entry happens.

      EIP-150 still takes the forwarded amount on collision (the child
      "returns zero gas"), so this rule consumes `forwarded` from `s2`
      into `s3` before bumping the nonce — mirroring the no-collision
      `create` rule.

      `EvmSemantics.createAddress` returns `Option` only because of its
      general signature (the underlying RLP encoder is `Option`-typed);
      the `none` case is unreachable for EVM-bounded nonces. The
      explicit `newAddr` / `h_addr` pair binds the derived address. -/
  | createCollision (s : State)
        (value offset size : UInt256) (rest : List UInt256)
        (forwarded : Nat) (newAddr : AccountAddress)
        (h_op    : s.decodedOp = some .CREATE)
        (h_stack : s.stack = value :: offset :: size :: rest)
        (h_perm  : s.executionEnv.permitStateMutation = true)
        (h_gas   : Gas.createCommitted s offset size ≤ s.gasAvailable)
        (h_take  : ¬ (s.executionEnv.depth ≥ 1024 ∨
                        (s.accountMap s.executionEnv.address).balance < value))
        (h_addr  : EvmSemantics.createAddress s.executionEnv.address
                     (s.accountMap s.executionEnv.address).nonce.toNat
                     = some newAddr)
        (h_fwd   : forwarded = Gas.allButOneSixtyFourth s.executionEnv.fork
                     (s.gasAvailable - Gas.createCommitted s offset size))
        (h_coll  : (s.accountMap newAddr).isContract = true)
      : StepRunning s
          { s with
              gasAvailable := s.gasAvailable - Gas.createCommitted s offset size - forwarded
              activeWords  := s.activeWordsAfterUInt256 offset.toNat size.toNat
              accountMap   := s.accountMap.set s.executionEnv.address
                                { s.accountMap s.executionEnv.address with
                                    nonce := (s.accountMap s.executionEnv.address).nonce + ⟨1⟩ }
              returnData   := .empty
              stack        := UInt256.ofNat 0 :: rest
              pc           := s.pc.succ }

  /-- CREATE (taken): depth + balance check passes *and* the derived
      address is free. The remaining gas (after base + memory) has
      63/64 forwarded to the init-code frame. See `createCollision`
      for the `newAddr` / `h_addr` convention. -/
  | create (s : State)
        (value offset size : UInt256) (rest : List UInt256)
        (forwarded : Nat) (newAddr : AccountAddress)
        (h_op     : s.decodedOp = some .CREATE)
        (h_stack  : s.stack = value :: offset :: size :: rest)
        (h_perm   : s.executionEnv.permitStateMutation = true)
        (h_gas    : Gas.createCommitted s offset size ≤ s.gasAvailable)
        (h_take   : ¬ (s.executionEnv.depth ≥ 1024 ∨
                         (s.accountMap s.executionEnv.address).balance < value))
        (h_addr   : EvmSemantics.createAddress s.executionEnv.address
                      (s.accountMap s.executionEnv.address).nonce.toNat
                      = some newAddr)
        (h_fwd    : forwarded = Gas.allButOneSixtyFourth s.executionEnv.fork
                      (s.gasAvailable - Gas.createCommitted s offset size))
        (h_nocoll : (s.accountMap newAddr).isContract = false)
      : StepRunning s
          (({ s with
                gasAvailable := s.gasAvailable - Gas.createCommitted s offset size - forwarded
                activeWords  := s.activeWordsAfterUInt256 offset.toNat size.toNat }
           ).enterCreate rest newAddr value
             (MachineState.readPadded s.memory offset.toNat size.toNat)
             forwarded)

  /-- CREATE2 attempted in a static frame. -/
  | create2Static (s : State)
        (value offset size salt : UInt256) (rest : List UInt256)
        (h_op    : s.decodedOp = some .CREATE2)
        (h_stack : s.stack = value :: offset :: size :: salt :: rest)
        (h_perm  : s.executionEnv.permitStateMutation = false)
      : StepRunning s ({ s with halt := .Exception .StaticModeViolation })

  /-- CREATE2 (not taken — depth or balance). -/
  | create2Fail (s : State)
        (value offset size salt : UInt256) (rest : List UInt256)
        (h_op    : s.decodedOp = some .CREATE2)
        (h_stack : s.stack = value :: offset :: size :: salt :: rest)
        (h_perm  : s.executionEnv.permitStateMutation = true)
        (h_gas   : Gas.create2Committed s offset size ≤ s.gasAvailable)
        (h_fail  : s.executionEnv.depth ≥ 1024 ∨
                     (s.accountMap s.executionEnv.address).balance < value)
      : StepRunning s
          { s with
              gasAvailable := s.gasAvailable - Gas.create2Committed s offset size
              activeWords  := s.activeWordsAfterUInt256 offset.toNat size.toNat
              returnData   := .empty
              stack        := UInt256.ofNat 0 :: rest
              pc           := s.pc.succ }

  /-- CREATE2 (address collision). Mirrors `createCollision`: EIP-150
      takes the forwarded amount even though no child runs. -/
  | create2Collision (s : State)
        (value offset size salt : UInt256) (rest : List UInt256) (forwarded : Nat)
        (h_op    : s.decodedOp = some .CREATE2)
        (h_stack : s.stack = value :: offset :: size :: salt :: rest)
        (h_perm  : s.executionEnv.permitStateMutation = true)
        (h_gas   : Gas.create2Committed s offset size ≤ s.gasAvailable)
        (h_take  : ¬ (s.executionEnv.depth ≥ 1024 ∨
                        (s.accountMap s.executionEnv.address).balance < value))
        (h_fwd   : forwarded = Gas.allButOneSixtyFourth s.executionEnv.fork
                     (s.gasAvailable - Gas.create2Committed s offset size))
        (h_coll  : (s.accountMap
                     (EvmSemantics.create2Address s.executionEnv.address salt
                       (MachineState.readPadded s.memory
                          offset.toNat size.toNat))).isContract = true)
      : StepRunning s
          { s with
              gasAvailable := s.gasAvailable - Gas.create2Committed s offset size - forwarded
              activeWords  := s.activeWordsAfterUInt256 offset.toNat size.toNat
              accountMap   := s.accountMap.set s.executionEnv.address
                                { s.accountMap s.executionEnv.address with
                                    nonce := (s.accountMap s.executionEnv.address).nonce + ⟨1⟩ }
              returnData   := .empty
              stack        := UInt256.ofNat 0 :: rest
              pc           := s.pc.succ }

  /-- CREATE2 (taken): no collision, depth + balance pass. -/
  | create2 (s : State)
        (value offset size salt : UInt256) (rest : List UInt256) (forwarded : Nat)
        (h_op     : s.decodedOp = some .CREATE2)
        (h_stack  : s.stack = value :: offset :: size :: salt :: rest)
        (h_perm   : s.executionEnv.permitStateMutation = true)
        (h_gas    : Gas.create2Committed s offset size ≤ s.gasAvailable)
        (h_take   : ¬ (s.executionEnv.depth ≥ 1024 ∨
                         (s.accountMap s.executionEnv.address).balance < value))
        (h_fwd    : forwarded = Gas.allButOneSixtyFourth s.executionEnv.fork
                      (s.gasAvailable - Gas.create2Committed s offset size))
        (h_nocoll : (s.accountMap
                      (EvmSemantics.create2Address s.executionEnv.address salt
                        (MachineState.readPadded s.memory
                           offset.toNat size.toNat))).isContract = false)
      : StepRunning s
          (({ s with
                gasAvailable := s.gasAvailable - Gas.create2Committed s offset size - forwarded
                activeWords  := s.activeWordsAfterUInt256 offset.toNat size.toNat }
           ).enterCreate rest
             (EvmSemantics.create2Address s.executionEnv.address salt
               (MachineState.readPadded s.memory offset.toNat size.toNat))
             value
             (MachineState.readPadded s.memory offset.toNat size.toNat)
             forwarded)

  ----------------------------------------------------------------------------
  -- SELFDESTRUCT: pop the beneficiary, transfer all of self's balance to
  -- it (credit-then-debit so self-beneficiary burns the balance), mark
  -- self in `substate.selfDestructSet`, and halt with `.Success`. The
  -- account isn't actually deleted at this site — deletion happens at end
  -- of transaction; for our single-tx test corpora the runner projects
  -- through `selfDestructSet` when comparing post-state.
  ----------------------------------------------------------------------------

  /-- SELFDESTRUCT attempted while the frame disallows state mutation
      (static mode). Halts with `StaticModeViolation` before paying any
      gas, mirroring `stepF.system`'s early static check (cf. `callStatic`). -/
  | selfDestructStatic (s : State)
        (beneficiary : UInt256) (rest : List UInt256)
        (h_op    : s.decodedOp = some .SELFDESTRUCT)
        (h_stack : s.stack = beneficiary :: rest)
        (h_perm  : s.executionEnv.permitStateMutation = false)
      : StepRunning s ({ s with halt := .Exception .StaticModeViolation })

  /-- SELFDESTRUCT: pop `beneficiary`, charge base (`G_selfdestruct = 5000`)
      and the new-account surcharge (`25000` iff the beneficiary is empty
      *and* self has a non-zero balance), then credit beneficiary,
      zero-out self, mark self in `selfDestructSet`, and halt with
      `.Success`. The order of explicit parameters mirrors the
      `stepF.system .SELFDESTRUCT` arm step-for-step. -/
  | selfDestruct (s : State)
        (beneficiary : UInt256) (rest : List UInt256)
        (h_op    : s.decodedOp = some .SELFDESTRUCT)
        (h_stack : s.stack = beneficiary :: rest)
        (h_perm  : s.executionEnv.permitStateMutation = true)
        (h_gas   : Gas.selfDestructTotal s beneficiary ≤ s.gasAvailable)
      : StepRunning s
          (({ s with gasAvailable := s.gasAvailable - Gas.selfDestructTotal s beneficiary
            }).selfDestructTo (AccountAddress.ofUInt256 beneficiary))

  ----------------------------------------------------------------------------
  -- Logging: LOG0–LOG4 (parametric over topic count).
  ----------------------------------------------------------------------------

  /-- LOG `n`: pop offset, size, then `n` topics; append a log entry.
      `Gas.logTotal s n offset size` bundles the static base, the memory-
      expansion delta for the read range, and the per-byte log-data cost. -/
  | log (s : State) (n : Fin 5) (offset size : UInt256)
        (topics : List UInt256) (rest : List UInt256)
        (h_op       : s.decodedOp = some (.Log ⟨n⟩))
        (h_perm     : s.executionEnv.permitStateMutation = true)
        (h_topics_n : topics.length = n.val)
        (h_stack    : s.stack = offset :: size :: topics ++ rest)
        (h_gas      : Gas.logTotal s n offset size ≤ s.gasAvailable)
      : StepRunning s
          { s with
              stack        := rest
              pc           := s.pc.succ
              gasAvailable := s.gasAvailable - Gas.logTotal s n offset size
              activeWords  := s.activeWordsAfterUInt256 offset.toNat size.toNat
              substate     := s.substate.appendLog
                                { address := s.executionEnv.address
                                  topics  := topics.toArray
                                  data    := MachineState.readPadded s.memory
                                               offset.toNat size.toNat } }

  ----------------------------------------------------------------------------
  -- EIP-8024: DUPN, SWAPN, EXCHANGE.
  ----------------------------------------------------------------------------

  /-- DUPN with immediate `n`: duplicate `stack[n]` to the top. PC += 2. -/
  | dupN (s : State) (n : Fin 256) (v : UInt256)
        (h_op      : s.decodedOp = some (.DupN ⟨n⟩))
        (h_gas     : Gas.baseCost s.fork (.DupN ⟨n⟩) ≤ s.gasAvailable)
        (h_get     : s.stack[n.val]? = some v)
      : StepRunning s
          { s with
              stack        := v :: s.stack
              pc           := s.pc + UInt256.ofNat 2
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork (.DupN ⟨n⟩) }

  /-- SWAPN with immediate `n`: swap top with `stack[n+1]`. PC += 2. -/
  | swapN (s : State) (n : Fin 256) (stk' : List UInt256)
        (h_op      : s.decodedOp = some (.SwapN ⟨n⟩))
        (h_gas     : Gas.baseCost s.fork (.SwapN ⟨n⟩) ≤ s.gasAvailable)
        (h_swap    : s.stack.exchange 0 (n.val + 1) = some stk')
      : StepRunning s
          { s with
              stack        := stk'
              pc           := s.pc + UInt256.ofNat 2
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork (.SwapN ⟨n⟩) }

  /-- EXCHANGE with packed immediate `b`: swap `stack[n+1]` and `stack[m+1]`
      where `n = b >>> 4` and `m = b &&& 0xf`. PC += 2. -/
  | exchange (s : State) (b : Fin 256) (stk' : List UInt256)
        (h_op      : s.decodedOp = some (.Exchange ⟨b⟩))
        (h_gas     : Gas.baseCost s.fork (.Exchange ⟨b⟩) ≤ s.gasAvailable)
        (h_swap    : s.stack.exchange
                      (b.val >>> 4 + 1)
                      ((b.val &&& 0xf) + 1) = some stk')
      : StepRunning s
          { s with
              stack        := stk'
              pc           := s.pc + UInt256.ofNat 2
              gasAvailable := s.gasAvailable - Gas.baseCost s.fork (.Exchange ⟨b⟩) }

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
      : StepRunning s ({ s with halt := .Exception .InvalidInstruction })

  /-- The explicit `INVALID` opcode (`0xfe`). -/
  | invalidOpcode (s : State)
        (h_op      : s.decodedOp = some .INVALID)
      : StepRunning s ({ s with halt := .Exception .InvalidInstruction })

  /-- Insufficient gas to pay for the decoded operation's *total* cost.
      `cost` is any witness gas amount at least `baseCost` — this lets the
      rule fire not only when the static fee alone exceeds the budget but
      also when a dynamic surcharge does: memory expansion, per-word copy,
      per-byte LOG/EXP, `Gas.sstoreCost`, or the EIP-2200 stipend. The
      `h_cost_lb` constraint prevents bogus OOGs (a `cost < baseCost`
      witness could not actually halt the op). -/
  | outOfGas (s : State) (op : Operation) (cost : Nat)
        (h_op       : s.decodedOp = some op)
        (h_cost_lb  : Gas.baseCost s.fork op ≤ cost)
        (h_gas      : s.gasAvailable < cost)
      : StepRunning s ({ s with halt := .Exception .OutOfGas })

  /-- Stack has fewer items than the operation requires to pop. -/
  | stackUnderflow (s : State) (op : Operation)
        (h_op      : s.decodedOp = some op)
        (h_under   : s.stack.length < op.popArity)
      : StepRunning s ({ s with halt := .Exception .StackUnderflow })

  /-- Executing this operation would grow the stack beyond the 1024-item
      EVM limit. Requires `popArity ≤ length` so the subtraction is well
      defined. -/
  | stackOverflow (s : State) (op : Operation)
        (h_op      : s.decodedOp = some op)
        (h_pop_ok  : op.popArity ≤ s.stack.length)
        (h_over    : s.stack.length - op.popArity + op.pushArity > 1024)
      : StepRunning s ({ s with halt := .Exception .StackOverflow })

  /-- State-mutating operation attempted while
      `executionEnv.permitStateMutation = false`. -/
  | staticModeViolation (s : State) (op : Operation)
        (h_op      : s.decodedOp = some op)
        (h_mut     : op.isStateMutating = true)
        (h_perm    : s.executionEnv.permitStateMutation = false)
      : StepRunning s ({ s with halt := .Exception .StaticModeViolation })

  /-- JUMP to a destination that is not a valid `JUMPDEST`: either the byte
      there is not `0x5b`, or it sits inside PUSH immediate data and so is
      not reachable as an instruction boundary. -/
  | jumpBadDest (s : State) (dest : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .JUMP)
        (h_gas     : Gas.baseCost s.fork .JUMP ≤ s.gasAvailable)
        (h_stack   : s.stack = dest :: rest)
        (h_bad     : Decode.isValidJumpDest s.executionEnv.code dest.toNat = false)
      : StepRunning s ({ s with halt := .Exception .BadJumpDestination })

  /-- JUMPI with `cond ≠ 0` but the destination is not a valid `JUMPDEST`
      (same rule as `jumpBadDest` — push-data byte or non-`0x5b`). -/
  | jumpiBadDest (s : State) (dest cond : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .JUMPI)
        (h_gas     : Gas.baseCost s.fork .JUMPI ≤ s.gasAvailable)
        (h_stack   : s.stack = dest :: cond :: rest)
        (h_cond    : UInt256.isTrue cond)
        (h_bad     : Decode.isValidJumpDest s.executionEnv.code dest.toNat = false)
      : StepRunning s ({ s with halt := .Exception .BadJumpDestination })

  /-- RETURNDATACOPY with `srcOffset + size > returnData.size`. -/
  | returndatacopyOob (s : State) (destOff srcOff sz : UInt256) (rest : List UInt256)
        (h_op      : s.decodedOp = some .RETURNDATACOPY)
        (h_gas     : Gas.baseCost s.fork .RETURNDATACOPY ≤ s.gasAvailable)
        (h_stack   : s.stack = destOff :: srcOff :: sz :: rest)
        (h_oob     : srcOff.toNat + sz.toNat > s.returnData.size)
      : StepRunning s ({ s with halt := .Exception .InvalidMemoryAccess })

/-- Call-return resume relation. Fires on a *halted* active frame whose
    `callStack` is non-empty: the child has finished, so we pop the caller
    frame `f` and resume it (writing the child's return data into the
    caller's memory and pushing the success flag). Each constructor pins
    the concrete halt kind via `h_halt` and the non-empty stack via
    `h_stack`, so a `StepReturn s s'` derivation by itself implies
    `s.halt ≠ .Running ∧ s.callStack ≠ []`. -/
inductive StepReturn : State → State → Prop

  /-- Child STOP/RETURN: resume the caller with success flag `1`, keeping the
      child's world mutations and refunding its unspent gas.

      The `h_kind : f.createAddr = none` premise discriminates this from
      `createReturnSuccess`: with `f.createAddr = some _` the frame is a
      CREATE child and must resume through the CREATE-family rule, not
      this one (which pushes `1` and ignores `hReturn`). -/
  | callReturnSuccess (s : State) (f : Frame) (rest : List Frame)
        (h_halt  : s.halt = .Success ∨ s.halt = .Returned)
        (h_stack : s.callStack = f :: rest)
        (h_kind  : f.createAddr = none)
      : StepReturn s (s.resumeSuccess f rest)

  /-- Child REVERT: resume the caller with failure flag `0`, roll the world
      back to the call-time snapshot, return the revert data, refund unspent gas. -/
  | callReturnRevert (s : State) (f : Frame) (rest : List Frame)
        (h_halt  : s.halt = .Reverted)
        (h_stack : s.callStack = f :: rest)
        (h_kind  : f.createAddr = none)
      : StepReturn s (s.resumeRevert f rest)

  /-- Child exceptional halt: resume the caller with failure flag `0`, roll the
      world back, return no data, and refund nothing. -/
  | callReturnException (s : State) (f : Frame) (rest : List Frame)
        (e : ExecutionException)
        (h_halt  : s.halt = .Exception e)
        (h_stack : s.callStack = f :: rest)
        (h_kind  : f.createAddr = none)
      : StepReturn s (s.resumeException f rest)

  /-- CREATE child STOP/RETURN: install the child's `hReturn` as the new
      account's code (charging `G_codedeposit · |code|` from the child's
      remaining gas), push `newAddr` to the caller, and refund the rest. -/
  | createReturnSuccess (s : State) (f : Frame) (rest : List Frame)
        (newAddr : AccountAddress)
        (h_halt  : s.halt = .Success ∨ s.halt = .Returned)
        (h_stack : s.callStack = f :: rest)
        (h_kind  : f.createAddr = some newAddr)
      : StepReturn s (s.resumeCreateSuccess f rest newAddr)

  /-- CREATE child REVERT: roll the world back, push `0`, keep `hReturn`
      as `returnData`, refund unspent gas. -/
  | createReturnRevert (s : State) (f : Frame) (rest : List Frame)
        (newAddr : AccountAddress)
        (h_halt  : s.halt = .Reverted)
        (h_stack : s.callStack = f :: rest)
        (h_kind  : f.createAddr = some newAddr)
      : StepReturn s (s.resumeCreateRevert f rest)

  /-- CREATE child exceptional halt: roll back, push `0`, refund nothing. -/
  | createReturnException (s : State) (f : Frame) (rest : List Frame)
        (newAddr : AccountAddress)
        (e : ExecutionException)
        (h_halt  : s.halt = .Exception e)
        (h_stack : s.callStack = f :: rest)
        (h_kind  : f.createAddr = some newAddr)
      : StepReturn s (s.resumeCreateException f rest)

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

end EVM
end EvmSemantics
