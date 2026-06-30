module

public import EvmSemantics
public import EvmSemantics.Hoare.Triple
public meta import EvmSemantics.Data.UInt256
public meta import EvmSemantics.EVM.Operation
public meta import EvmSemantics.EVM.Decode

/-!
`FibDemo` — a worked example: iterative Fibonacci, hand-written in EVM
bytecode and executed against the verified evaluator.

The program reads the index `n` from `calldata[4..36]` (skipping the
4-byte selector that a Solidity-style ABI would put up front),
iteratively computes `fib(n)`, stores the 32-byte result in memory at
offset 0, and `RETURN`s it.

```
0:  PUSH1 0x04        ; selector skip offset
2:  CALLDATALOAD      ; stack: [n]
3:  PUSH1 0x00        ; a := 0; stack: [a, n]
5:  PUSH1 0x01        ; b := 1; stack: [b, a, n]   (treat top arg as i = n)
7:  JUMPDEST          ; loop_start
8:  DUP3              ; stack: [i, b, a, i]
9:  ISZERO            ; stack: [i==0, b, a, i]
10: PUSH1 0x19        ; end = 25
12: JUMPI             ; if i = 0 goto end
13: SWAP1             ; [a, b, i]
14: DUP2              ; [b, a, b, i]
15: ADD               ; [a+b, b, i]            -- new b on top
16: SWAP2             ; [i, b, a+b]
17: PUSH1 0x01
19: SWAP1             ; [i, 1, b, a+b]
20: SUB               ; [i-1, b, a+b]
21: SWAP2             ; [a+b, b, i-1]
22: PUSH1 0x07        ; loop_start
24: JUMP
25: JUMPDEST          ; end ; stack here: [b, a, 0]
26: POP               ; [a, 0]
27: PUSH1 0x00        ; mem offset
29: MSTORE            ; memory[0..32] := a (big-endian); stack: [0]
30: PUSH1 0x20        ; len = 32
32: PUSH1 0x00        ; offset = 0
34: RETURN            ; halt with `hReturn = bytes(a)`
```

The relational soundness theorem `stepF_sound` already certifies every
step the runner takes against the inductive `Step` relation, so each
execution of this demo is implicitly a proof that *that specific trace*
is well-typed under the small-step semantics. We do not try to write
out a closed-form `Steps s₀ sf ∧ sf.stack = [fib n]` here for the same
whnf-budget reason discussed in the previous demo: the JUMP arm pulls
in `Decode.isValidJumpDest` and the cumulative reduction exhausts the
budget several steps later. -/

@[expose] public section

open EvmSemantics EvmSemantics.EVM

namespace FibDemo

/-- The Fibonacci bytecode (35 bytes). -/
def code : ByteArray :=
  ⟨#[0x60, 0x04,       -- PUSH1 4              (offset 0)
     0x35,             -- CALLDATALOAD         (offset 2)
     0x60, 0x00,       -- PUSH1 0  (a)         (offset 3)
     0x60, 0x01,       -- PUSH1 1  (b)         (offset 5)
     0x5b,             -- JUMPDEST loop_start  (offset 7)
     0x82,             -- DUP3                 (offset 8)
     0x15,             -- ISZERO               (offset 9)
     0x60, 0x19,       -- PUSH1 0x19 (= 25)    (offset 10)
     0x57,             -- JUMPI                (offset 12)
     0x90,             -- SWAP1                (offset 13)
     0x81,             -- DUP2                 (offset 14)
     0x01,             -- ADD                  (offset 15)
     0x91,             -- SWAP2                (offset 16)
     0x60, 0x01,       -- PUSH1 1              (offset 17)
     0x90,             -- SWAP1                (offset 19)
     0x03,             -- SUB                  (offset 20)
     0x91,             -- SWAP2                (offset 21)
     0x60, 0x07,       -- PUSH1 7              (offset 22)
     0x56,             -- JUMP                 (offset 24)
     0x5b,             -- JUMPDEST end         (offset 25)
     0x50,             -- POP                  (offset 26)
     0x60, 0x00,       -- PUSH1 0              (offset 27)
     0x52,             -- MSTORE               (offset 29)
     0x60, 0x20,       -- PUSH1 0x20           (offset 30)
     0x60, 0x00,       -- PUSH1 0              (offset 32)
     0xf3]⟩           -- RETURN               (offset 34)

/-- Build the 36-byte calldata: 4 selector bytes (zeros — the program ignores
    them) followed by `n` as a 256-bit big-endian word. -/
def calldataFor (n : Nat) : ByteArray := Id.run do
  let mut bs : ByteArray := ByteArray.empty
  for i in [0:36] do
    let byte : UInt8 :=
      if i < 4 then 0
      else
        let shift := (35 - i) * 8
        UInt8.ofNat ((n >>> shift) &&& 0xff)
    bs := bs.push byte
  return bs

/-- Initial state with `calldataFor n` as calldata. 100 000 gas is plenty for
    Fibonacci indices up to a few hundred — each loop iteration is ~50 gas. -/
def initState (n : Nat) : State :=
  let env : ExecutionEnv :=
    { address := 0, origin := 0, caller := 0, weiValue := ⟨0⟩
      calldata := calldataFor n, code := code
      gasPrice := ⟨0⟩, header := default, depth := 0
      permitStateMutation := true, blobVersionedHashes := #[]
      fork := .Cancun }
  { toMachineState :=
      { gasAvailable := 100000, activeWords := ⟨0⟩
        memory := .empty, returnData := .empty, hReturn := .empty }
    accountMap   := AccountMap.empty
    substate     := Substate.empty
    executionEnv := env
    pc := ⟨0⟩, stack := [], execLength := 0, halt := .Running }

/-- Run `stepF` to a halt (with empty call stack) or until `fuel` runs out. -/
partial def run (s : State) (fuel : Nat) : Except ExecutionException State :=
  if fuel = 0 then .error .OutOfFuel else
    if s.isDone then .ok s else
      match stepF s with
      | .ok s'   => run s' (fuel - 1)
      | .error e => .error e

/-- Reference Fibonacci, used to check the bytecode's output. -/
def fib : Nat → Nat
  | 0     => 0
  | 1     => 1
  | n + 2 => fib (n + 1) + fib n

/-- `fib n ≤ fib (n + 1)` — used to propagate "no overflow" through the loop. -/
theorem fib_le_succ (n : Nat) : fib n ≤ fib (n + 1) := by
  match n with
  | 0     => decide
  | 1     => decide
  | m + 2 => show fib (m + 2) ≤ fib (m + 2) + fib (m + 1); omega

/-- `fib m ≤ fib (m + k)` — fib is monotone in its argument. -/
theorem fib_le_add (m k : Nat) : fib m ≤ fib (m + k) := by
  induction k with
  | zero => exact Nat.le_refl _
  | succ k' ih =>
    have : m + k' + 1 = m + (k' + 1) := by omega
    exact this ▸ Nat.le_trans ih (fib_le_succ (m + k'))

/-- Decode a 32-byte big-endian `ByteArray` to a `Nat`. -/
def bytesToNat (bs : ByteArray) : Nat :=
  bs.toList.foldl (fun acc b => acc * 256 + b.toNat) 0

----------------------------------------------------------------------------
-- Relational basic-block proofs
--
-- Each block is a contiguous piece of the bytecode bracketed by JUMP / JUMPI
-- targets. We prove its semantic effect with the relational `Step` /
-- `Steps` rules directly — no `stepF`, no soundness lift. Each step
-- carries an `h_op : s.decodedOp = some <op>` premise, discharged via the
-- pre-decoded `decodeFib` table (see below) plus the bridge lemma
-- `decodeFib_eq`.
----------------------------------------------------------------------------

/-- The 256-bit word `CALLDATALOAD 4` would push from `cd`. -/
def calldataN (cd : ByteArray) : UInt256 :=
  let bs := MachineState.readPadded cd 4 32
  UInt256.ofNat (Decode.beToNat bs)

/-!
## A pre-decoded view of the Fibonacci program

`Decode.decodeAt code pc` doesn't reduce by `rfl` on concrete `code` and
`pc` because `Array.extract` (used to slice out PUSH immediates) does not
weak-head-normalise in the Lean kernel. To unblock the block proofs we
write down the program as a `Nat → Option (Operation × Option (UInt256 ×
Nat))` function with one literal-pattern arm per byte offset that holds an
opcode (mid-immediate offsets fall through to `none`). Pattern-matching on
a literal `Nat` reduces by `rfl`, so the constructor's `s.decoded = …`
premise becomes a one-line rewrite.

The bridge lemma `decodeFib_eq` is closed below by case-splitting on `pc`
and discharging each live arm with `native_decide` (which compiles
`Decode.decodeAt code pc` to native code and evaluates it; this works
even though kernel reduction stalls on `ByteArray.extract`).
-/

/-- The Fibonacci program, decoded once and tabulated by byte offset.
    `none` at a PC means "no opcode starts here" (either out of range or
    in the middle of a PUSH immediate). The data matches
    `Decode.decodeAt code` at every PC where this returns `some _`. -/
def decodeFib : Nat → Option (Operation × Option (UInt256 × Nat))
  | 0  => some (.Push ⟨1, by decide⟩, some (UInt256.ofNat 4, 1))
  | 2  => some (.CALLDATALOAD, none)
  | 3  => some (.Push ⟨1, by decide⟩, some (UInt256.ofNat 0, 1))
  | 5  => some (.Push ⟨1, by decide⟩, some (UInt256.ofNat 1, 1))
  | 7  => some (.JUMPDEST, none)
  | 8  => some (.Dup ⟨2, by decide⟩, none)              -- DUP3
  | 9  => some (.ISZERO, none)
  | 10 => some (.Push ⟨1, by decide⟩, some (UInt256.ofNat 0x19, 1))
  | 12 => some (.JUMPI, none)
  | 13 => some (.Swap ⟨0, by decide⟩, none)             -- SWAP1
  | 14 => some (.Dup ⟨1, by decide⟩, none)              -- DUP2
  | 15 => some (.ADD, none)
  | 16 => some (.Swap ⟨1, by decide⟩, none)             -- SWAP2
  | 17 => some (.Push ⟨1, by decide⟩, some (UInt256.ofNat 1, 1))
  | 19 => some (.Swap ⟨0, by decide⟩, none)             -- SWAP1
  | 20 => some (.SUB, none)
  | 21 => some (.Swap ⟨1, by decide⟩, none)             -- SWAP2
  | 22 => some (.Push ⟨1, by decide⟩, some (UInt256.ofNat 7, 1))
  | 24 => some (.JUMP, none)
  | 25 => some (.JUMPDEST, none)
  | 26 => some (.POP, none)
  | 27 => some (.Push ⟨1, by decide⟩, some (UInt256.ofNat 0, 1))
  | 29 => some (.MSTORE, none)
  | 30 => some (.Push ⟨1, by decide⟩, some (UInt256.ofNat 0x20, 1))
  | 32 => some (.Push ⟨1, by decide⟩, some (UInt256.ofNat 0, 1))
  | 34 => some (.RETURN, none)
  | _  => none

/-- **Bridge lemma**, conditional form: whenever `decodeFib pc` returns
    `some (op, imm)`, `Decode.decodeAt code pc` returns the same thing.
    (The bridge only needs to relate the *opcode-aligned* PCs of
    interest; mid-immediate and out-of-range PCs trip the catch-all
    `_ => none` of `decodeFib` and never reach this lemma.)

    Each "live" PC is closed by `native_decide` after the `cases h`
    inverts `some _ = some (op, imm)`; the same VM that runs the
    bytecode reduces `Decode.decodeAt code pc` straight through
    `ByteArray.extract`. The "dead" PCs (in-range mid-immediate offsets
    and out-of-range tails) contradict `h` via `simp [decodeFib]`. -/
theorem decodeFib_eq {pc : Nat} {op : Operation} {imm : Option (UInt256 × Nat)}
    (h : decodeFib pc = some (op, imm)) :
    Decode.decodeAt code pc = some (op, imm) := by
  match pc with
  | 0  => cases h; native_decide
  | 1  => simp [decodeFib] at h
  | 2  => cases h; native_decide
  | 3  => cases h; native_decide
  | 4  => simp [decodeFib] at h
  | 5  => cases h; native_decide
  | 6  => simp [decodeFib] at h
  | 7  => cases h; native_decide
  | 8  => cases h; native_decide
  | 9  => cases h; native_decide
  | 10 => cases h; native_decide
  | 11 => simp [decodeFib] at h
  | 12 => cases h; native_decide
  | 13 => cases h; native_decide
  | 14 => cases h; native_decide
  | 15 => cases h; native_decide
  | 16 => cases h; native_decide
  | 17 => cases h; native_decide
  | 18 => simp [decodeFib] at h
  | 19 => cases h; native_decide
  | 20 => cases h; native_decide
  | 21 => cases h; native_decide
  | 22 => cases h; native_decide
  | 23 => simp [decodeFib] at h
  | 24 => cases h; native_decide
  | 25 => cases h; native_decide
  | 26 => cases h; native_decide
  | 27 => cases h; native_decide
  | 28 => simp [decodeFib] at h
  | 29 => cases h; native_decide
  | 30 => cases h; native_decide
  | 31 => simp [decodeFib] at h
  | 32 => cases h; native_decide
  | 33 => simp [decodeFib] at h
  | 34 => cases h; native_decide
  | _ + 35 => simp [decodeFib] at h

/-- Helper: given a state whose code and pc point inside the Fibonacci
    program, `s.decoded` is whatever `decodeFib` says it is. -/
private theorem decoded_via_decodeFib (s : State) (pc_n : Nat)
    {op : Operation} {imm : Option (UInt256 × Nat)}
    (h_code : s.executionEnv.code = code)
    (h_pc   : s.pc.toNat = pc_n)
    (h_fib  : decodeFib pc_n = some (op, imm)) :
    s.decoded = some (op, imm) := by
  show Decode.decodeAt s.executionEnv.code s.pc.toNat = _
  rw [h_code, h_pc]
  exact decodeFib_eq h_fib

/-- Specialised form: `decodedOp` only (no immediate). -/
private theorem decodedOp_via_decodeFib (s : State) (pc_n : Nat)
    {op : Operation} {imm : Option (UInt256 × Nat)}
    (h_code : s.executionEnv.code = code)
    (h_pc   : s.pc.toNat = pc_n)
    (h_fib  : decodeFib pc_n = some (op, imm)) :
    s.decodedOp = some op := by
  unfold State.decodedOp
  rw [decoded_via_decodeFib s pc_n h_code h_pc h_fib]
  rfl

open EvmSemantics.Hoare (Triple StateAt)

-- The generic Hoare-triple infrastructure (`Triple`, `Triple.seq`, the
-- `StateAt` state predicate, the per-opcode triples, and the `UInt256`
-- arithmetic helpers `pc_add`, `ofNat_toNat`, `uint256_eq_of_toNat`,
-- `ofNat_sub_one`) lives in `EvmSemantics/Hoare/Triple.lean`. This demo
-- only re-exports the names it uses verbatim and bridges its tabulated
-- decoder `decodeFib` to `Decode.decodeAt code`.

/-- Bridge: a `decodeFib pc = some (op, imm)` witness yields the same
    statement against `Decode.decodeAt env.code` when `env.code = code`. -/
private theorem decodeAt_of_decodeFib {env : ExecutionEnv} {pc_n : Nat}
    {op : Operation} {imm : Option (UInt256 × Nat)}
    (h_code : env.code = code)
    (h_fib : decodeFib pc_n = some (op, imm)) :
    Decode.decodeAt env.code pc_n = some (op, imm) := by
  rw [h_code]; exact decodeFib_eq h_fib

----------------------------------------------------------------------------
-- Program-level predicates: where each block "starts" and "ends".
----------------------------------------------------------------------------

/-- "At the loop head for `n`": `pc = 7`, stack has some `b :: a :: ofNat n`
    triple, and we have at least `55·n + 20 + 18` gas for the rest of the
    program (loop iterations + final check + end block). -/
def AtLoopHead (n : Nat) (s : State) : Prop :=
  s.executionEnv.code = code ∧
  s.pc.toNat = 7 ∧
  s.halt = .Running ∧
  s.toMachineState.activeWords.toNat = 0 ∧
  (∃ b a, s.stack = [b, a, UInt256.ofNat n]) ∧
  55 * n + 38 ≤ s.gasAvailable

/-- "At the end-block head": `pc = 25`, stack has some `b :: a :: 0 :: rest`,
    enough gas for `end_block`. -/
def AtEndHead (s : State) : Prop :=
  s.executionEnv.code = code ∧
  s.pc.toNat = 25 ∧
  s.halt = .Running ∧
  s.toMachineState.activeWords.toNat = 0 ∧
  (∃ b a rest, s.stack = b :: a :: UInt256.ofNat 0 :: rest) ∧
  18 ≤ s.gasAvailable

----------------------------------------------------------------------------
-- Per-opcode Hoare-triple wrappers.
--
-- Each `*_triple` is a thin wrapper around `EvmSemantics.Hoare.*_triple`
-- that takes the FibDemo-specific `h_code : env.code = code` + `h_dec :
-- decodeFib pc_n = some _` and forwards them as a single
-- `Decode.decodeAt env.code pc_n = some _` via `decodeAt_of_decodeFib`.
-- The block theorems below stay agnostic about the underlying decoder.
----------------------------------------------------------------------------

/-- `PUSH1 data` at `pc_n` (2 bytes, cost 3). -/
theorem push1_triple {env : ExecutionEnv} {pc_n : Nat} {data : UInt256}
    {rest : List UInt256} {gas_in : Nat} {active : UInt256}
    (h_code : env.code = code)
    (h_pcb : pc_n + 2 < UInt256.size)
    (h_dec : decodeFib pc_n = some (.Push ⟨1, by decide⟩, some (data, 1)))
    (h_gas : 3 ≤ gas_in) :
    Triple (StateAt env pc_n rest gas_in active)
           (StateAt env (pc_n + 2) (data :: rest) (gas_in - 3) active) :=
  Hoare.push1_triple h_pcb (decodeAt_of_decodeFib h_code h_dec) h_gas

/-- `CALLDATALOAD` at `pc_n` (1 byte, cost 3). -/
theorem calldataload_triple {env : ExecutionEnv} {pc_n : Nat} {i : UInt256}
    {rest : List UInt256} {gas_in : Nat} {active : UInt256}
    (h_code : env.code = code)
    (h_pcb : pc_n + 1 < UInt256.size)
    (h_dec : decodeFib pc_n = some (.CALLDATALOAD, none))
    (h_gas : 3 ≤ gas_in) :
    Triple (StateAt env pc_n (i :: rest) gas_in active)
           (StateAt env (pc_n + 1)
             (MachineState.readWord env.calldata i.toNat :: rest)
             (gas_in - 3) active) :=
  Hoare.calldataload_triple h_pcb (decodeAt_of_decodeFib h_code h_dec) h_gas

/-- `JUMPDEST` at `pc_n` (1 byte, base cost 1). -/
theorem jumpdest_triple {env : ExecutionEnv} {pc_n : Nat}
    {stack : List UInt256} {gas_in : Nat} {active : UInt256}
    (h_code : env.code = code)
    (h_pcb : pc_n + 1 < UInt256.size)
    (h_dec : decodeFib pc_n = some (.JUMPDEST, none))
    (h_gas : 1 ≤ gas_in) :
    Triple (StateAt env pc_n stack gas_in active)
           (StateAt env (pc_n + 1) stack (gas_in - 1) active) :=
  Hoare.jumpdest_triple h_pcb (decodeAt_of_decodeFib h_code h_dec) h_gas

/-- `DUPn` at `pc_n` (1 byte, cost 3). -/
theorem dup_triple {env : ExecutionEnv} {pc_n : Nat} {n : Fin 16} {v : UInt256}
    {stack : List UInt256} {gas_in : Nat} {active : UInt256}
    (h_code : env.code = code)
    (h_pcb : pc_n + 1 < UInt256.size)
    (h_dec : decodeFib pc_n = some (.Dup ⟨n⟩, none))
    (h_get : stack[n.val]? = some v)
    (h_gas : 3 ≤ gas_in) :
    Triple (StateAt env pc_n stack gas_in active)
           (StateAt env (pc_n + 1) (v :: stack) (gas_in - 3) active) :=
  Hoare.dup_triple h_pcb (decodeAt_of_decodeFib h_code h_dec) h_get h_gas

/-- `ISZERO` at `pc_n` (1 byte, cost 3). -/
theorem iszero_triple {env : ExecutionEnv} {pc_n : Nat} {a : UInt256}
    {rest : List UInt256} {gas_in : Nat} {active : UInt256}
    (h_code : env.code = code)
    (h_pcb : pc_n + 1 < UInt256.size)
    (h_dec : decodeFib pc_n = some (.ISZERO, none))
    (h_gas : 3 ≤ gas_in) :
    Triple (StateAt env pc_n (a :: rest) gas_in active)
           (StateAt env (pc_n + 1) (UInt256.isZero a :: rest) (gas_in - 3) active) :=
  Hoare.iszero_triple h_pcb (decodeAt_of_decodeFib h_code h_dec) h_gas

/-- `SWAPn` at `pc_n` (1 byte, cost 3). -/
theorem swap_triple {env : ExecutionEnv} {pc_n : Nat} {n : Fin 16}
    {stack stack' : List UInt256} {gas_in : Nat} {active : UInt256}
    (h_code : env.code = code)
    (h_pcb : pc_n + 1 < UInt256.size)
    (h_dec : decodeFib pc_n = some (.Swap ⟨n⟩, none))
    (h_sw : stack.exchange 0 (n.val + 1) = some stack')
    (h_gas : 3 ≤ gas_in) :
    Triple (StateAt env pc_n stack gas_in active)
           (StateAt env (pc_n + 1) stack' (gas_in - 3) active) :=
  Hoare.swap_triple h_pcb (decodeAt_of_decodeFib h_code h_dec) h_sw h_gas

/-- `ADD` at `pc_n` (1 byte, cost 3). -/
theorem add_triple {env : ExecutionEnv} {pc_n : Nat} {a b : UInt256}
    {rest : List UInt256} {gas_in : Nat} {active : UInt256}
    (h_code : env.code = code)
    (h_pcb : pc_n + 1 < UInt256.size)
    (h_dec : decodeFib pc_n = some (.ADD, none))
    (h_gas : 3 ≤ gas_in) :
    Triple (StateAt env pc_n (a :: b :: rest) gas_in active)
           (StateAt env (pc_n + 1) ((a + b) :: rest) (gas_in - 3) active) :=
  Hoare.add_triple h_pcb (decodeAt_of_decodeFib h_code h_dec) h_gas

/-- `SUB` at `pc_n` (1 byte, cost 3). -/
theorem sub_triple {env : ExecutionEnv} {pc_n : Nat} {a b : UInt256}
    {rest : List UInt256} {gas_in : Nat} {active : UInt256}
    (h_code : env.code = code)
    (h_pcb : pc_n + 1 < UInt256.size)
    (h_dec : decodeFib pc_n = some (.SUB, none))
    (h_gas : 3 ≤ gas_in) :
    Triple (StateAt env pc_n (a :: b :: rest) gas_in active)
           (StateAt env (pc_n + 1) ((a - b) :: rest) (gas_in - 3) active) :=
  Hoare.sub_triple h_pcb (decodeAt_of_decodeFib h_code h_dec) h_gas

/-- `POP` at `pc_n` (1 byte, cost 2). -/
theorem pop_triple {env : ExecutionEnv} {pc_n : Nat} {a : UInt256}
    {rest : List UInt256} {gas_in : Nat} {active : UInt256}
    (h_code : env.code = code)
    (h_pcb : pc_n + 1 < UInt256.size)
    (h_dec : decodeFib pc_n = some (.POP, none))
    (h_gas : 2 ≤ gas_in) :
    Triple (StateAt env pc_n (a :: rest) gas_in active)
           (StateAt env (pc_n + 1) rest (gas_in - 2) active) :=
  Hoare.pop_triple h_pcb (decodeAt_of_decodeFib h_code h_dec) h_gas

/-- `JUMP` at `pc_n` (1 byte, cost 8). -/
theorem jump_triple {env : ExecutionEnv} {pc_n : Nat} {dest : UInt256}
    {rest : List UInt256} {gas_in : Nat} {active : UInt256}
    (h_code : env.code = code)
    (h_dec : decodeFib pc_n = some (.JUMP, none))
    (h_valid : Decode.isValidJumpDest env.code dest.toNat = true)
    (h_gas : 8 ≤ gas_in) :
    Triple (StateAt env pc_n (dest :: rest) gas_in active)
           (StateAt env dest.toNat rest (gas_in - 8) active) :=
  Hoare.jump_triple (decodeAt_of_decodeFib h_code h_dec) h_valid h_gas

/-- `JUMPI` (taken branch) at `pc_n` (1 byte, cost 10). -/
theorem jumpi_taken_triple {env : ExecutionEnv} {pc_n : Nat} {dest cond : UInt256}
    {rest : List UInt256} {gas_in : Nat} {active : UInt256}
    (h_code : env.code = code)
    (h_dec : decodeFib pc_n = some (.JUMPI, none))
    (h_cond : UInt256.isTrue cond)
    (h_valid : Decode.isValidJumpDest env.code dest.toNat = true)
    (h_gas : 10 ≤ gas_in) :
    Triple (StateAt env pc_n (dest :: cond :: rest) gas_in active)
           (StateAt env dest.toNat rest (gas_in - 10) active) :=
  Hoare.jumpi_taken_triple (decodeAt_of_decodeFib h_code h_dec) h_cond h_valid h_gas

/-- `JUMPI` (not-taken branch) at `pc_n` (1 byte, cost 10). -/
theorem jumpi_notTaken_triple {env : ExecutionEnv} {pc_n : Nat} {dest cond : UInt256}
    {rest : List UInt256} {gas_in : Nat} {active : UInt256}
    (h_code : env.code = code)
    (h_pcb : pc_n + 1 < UInt256.size)
    (h_dec : decodeFib pc_n = some (.JUMPI, none))
    (h_cond : ¬ UInt256.isTrue cond)
    (h_gas : 10 ≤ gas_in) :
    Triple (StateAt env pc_n (dest :: cond :: rest) gas_in active)
           (StateAt env (pc_n + 1) rest (gas_in - 10) active) :=
  Hoare.jumpi_notTaken_triple h_pcb (decodeAt_of_decodeFib h_code h_dec) h_cond h_gas

/-- `MSTORE` at `pc_n` (offset 0, size 32, activeWords 0 → 1; cost 6). -/
theorem mstore_triple {env : ExecutionEnv} {pc_n : Nat} {value : UInt256}
    {rest : List UInt256} {gas_in : Nat}
    (h_code : env.code = code)
    (h_pcb : pc_n + 1 < UInt256.size)
    (h_dec : decodeFib pc_n = some (.MSTORE, none))
    (h_gas : 6 ≤ gas_in) :
    Triple
      (StateAt env pc_n (UInt256.ofNat 0 :: value :: rest) gas_in (UInt256.ofNat 0))
      (StateAt env (pc_n + 1) rest (gas_in - 6) (UInt256.ofNat 1)) :=
  Hoare.mstore_triple h_pcb (decodeAt_of_decodeFib h_code h_dec) h_gas

/-- `RETURN` at `pc_n` (offset 0, size 32, activeWords = 1; cost 0). -/
theorem return_triple {env : ExecutionEnv} {pc_n : Nat}
    {rest : List UInt256} {gas_in : Nat}
    (h_code : env.code = code)
    (h_dec : decodeFib pc_n = some (.RETURN, none)) :
    Triple
      (StateAt env pc_n (UInt256.ofNat 0 :: UInt256.ofNat 0x20 :: rest) gas_in
        (UInt256.ofNat 1))
      (fun sf => sf.halt = .Returned) :=
  Hoare.return_triple (decodeAt_of_decodeFib h_code h_dec)

/-- **Loop-check (taken branch) via per-opcode triples** — replaces ~100 lines
    of manual `Step.running`/`StepRunning.<op>` plumbing with a 5-line chain.
    `JUMPDEST ; DUP3 ; ISZERO ; PUSH1 0x19 ; JUMPI`. -/
theorem loop_check_taken_via_opcodes {env : ExecutionEnv}
    {b a : UInt256} {rest : List UInt256} {gas_in : Nat} {active : UInt256}
    (h_code : env.code = code) (h_gas : 20 ≤ gas_in) :
    Triple (StateAt env 7 (b :: a :: UInt256.ofNat 0 :: rest) gas_in active)
           (StateAt env 25 (b :: a :: UInt256.ofNat 0 :: rest) (gas_in - 20) active) := by
  have step1 := jumpdest_triple (env := env) (pc_n := 7) (gas_in := gas_in)
    (active := active) (stack := b :: a :: UInt256.ofNat 0 :: rest)
    h_code (by decide) rfl (by omega)
  have step2 := dup_triple (env := env) (pc_n := 8) (n := ⟨2, by decide⟩)
    (v := UInt256.ofNat 0) (gas_in := gas_in - 1) (active := active)
    (stack := b :: a :: UInt256.ofNat 0 :: rest)
    h_code (by decide) rfl rfl (by omega)
  have step3 := iszero_triple (env := env) (pc_n := 9) (a := UInt256.ofNat 0)
    (gas_in := gas_in - 1 - 3) (active := active)
    (rest := b :: a :: UInt256.ofNat 0 :: rest)
    h_code (by decide) rfl (by omega)
  have step4 := push1_triple (env := env) (pc_n := 10) (data := UInt256.ofNat 0x19)
    (gas_in := gas_in - 1 - 3 - 3) (active := active)
    (rest := UInt256.isZero (UInt256.ofNat 0) :: b :: a :: UInt256.ofNat 0 :: rest)
    h_code (by decide) rfl (by omega)
  have step5 := jumpi_taken_triple (env := env) (pc_n := 12)
    (dest := UInt256.ofNat 0x19) (cond := UInt256.isZero (UInt256.ofNat 0))
    (gas_in := gas_in - 1 - 3 - 3 - 3) (active := active)
    (rest := b :: a :: UInt256.ofNat 0 :: rest)
    h_code rfl (by decide) (by rw [h_code]; rfl) (by omega)
  -- Compose the five opcode triples.
  have chain := step1.seq <| step2.seq <| step3.seq <| step4.seq step5
  -- Final adjustment: `(UInt256.ofNat 0x19).toNat` and chained gas subtraction.
  intro s h_s
  obtain ⟨sf, hs, hf⟩ := chain s h_s
  refine ⟨sf, hs, hf.env_eq, ?_, hf.halt, hf.stack_eq, ?_, hf.active_eq⟩
  · -- pc.toNat: (UInt256.ofNat 0x19).toNat = 25
    show sf.pc.toNat = 25; rw [hf.pc]; rfl
  · -- gas: gas_in - 1 - 3 - 3 - 3 - 10 = gas_in - 20
    show sf.gasAvailable = gas_in - 20; rw [hf.gas_eq]; omega

/-- **Loop-check (continue branch) via per-opcode triples** — `i ≠ 0`, so the
    JUMPI falls through to `pc = 13`. Same 5 opcodes as the taken branch, but
    the last is `jumpi_notTaken_triple`. -/
theorem loop_check_continue_via_opcodes {env : ExecutionEnv}
    {b a i : UInt256} {rest : List UInt256} {gas_in : Nat} {active : UInt256}
    (h_code : env.code = code) (h_i_nz : i.toNat ≠ 0) (h_gas : 20 ≤ gas_in) :
    Triple (StateAt env 7 (b :: a :: i :: rest) gas_in active)
           (StateAt env 13 (b :: a :: i :: rest) (gas_in - 20) active) := by
  have step1 := jumpdest_triple (env := env) (pc_n := 7) (gas_in := gas_in)
    (active := active) (stack := b :: a :: i :: rest)
    h_code (by decide) rfl (by omega)
  have step2 := dup_triple (env := env) (pc_n := 8) (n := ⟨2, by decide⟩)
    (v := i) (gas_in := gas_in - 1) (active := active)
    (stack := b :: a :: i :: rest)
    h_code (by decide) rfl rfl (by omega)
  have step3 := iszero_triple (env := env) (pc_n := 9) (a := i)
    (gas_in := gas_in - 1 - 3) (active := active)
    (rest := b :: a :: i :: rest)
    h_code (by decide) rfl (by omega)
  have step4 := push1_triple (env := env) (pc_n := 10) (data := UInt256.ofNat 0x19)
    (gas_in := gas_in - 1 - 3 - 3) (active := active)
    (rest := UInt256.isZero i :: b :: a :: i :: rest)
    h_code (by decide) rfl (by omega)
  have step5 := jumpi_notTaken_triple (env := env) (pc_n := 12)
    (dest := UInt256.ofNat 0x19) (cond := UInt256.isZero i)
    (gas_in := gas_in - 1 - 3 - 3 - 3) (active := active)
    (rest := b :: a :: i :: rest)
    h_code (by decide) rfl
    (by simp [UInt256.isTrue, UInt256.isZero, h_i_nz]; rfl) (by omega)
  have chain := step1.seq <| step2.seq <| step3.seq <| step4.seq step5
  intro s h_s
  obtain ⟨sf, hs, hf⟩ := chain s h_s
  refine ⟨sf, hs, hf.env_eq, ?_, hf.halt, hf.stack_eq, ?_, hf.active_eq⟩
  · show sf.pc.toNat = 13; rw [hf.pc]
  · show sf.gasAvailable = gas_in - 20; rw [hf.gas_eq]; omega

/-- **Loop body via per-opcode triples** — replaces ~200 lines of manual step
    plumbing with a 10-line chain.
    `SWAP1 ; DUP2 ; ADD ; SWAP2 ; PUSH1 1 ; SWAP1 ; SUB ; SWAP2 ; PUSH1 7 ; JUMP`. -/
theorem loop_body_via_opcodes {env : ExecutionEnv}
    {b a i : UInt256} {rest : List UInt256} {gas_in : Nat} {active : UInt256}
    (h_code : env.code = code) (h_gas : 35 ≤ gas_in) :
    Triple (StateAt env 13 (b :: a :: i :: rest) gas_in active)
           (StateAt env 7 ((b + a) :: b :: (i - UInt256.ofNat 1) :: rest)
             (gas_in - 35) active) := by
  have step1 := swap_triple (env := env) (pc_n := 13) (n := ⟨0, by decide⟩)
    (stack := b :: a :: i :: rest) (stack' := a :: b :: i :: rest)
    (gas_in := gas_in) (active := active)
    h_code (by decide) rfl rfl (by omega)
  have step2 := dup_triple (env := env) (pc_n := 14) (n := ⟨1, by decide⟩)
    (v := b) (stack := a :: b :: i :: rest)
    (gas_in := gas_in - 3) (active := active)
    h_code (by decide) rfl rfl (by omega)
  have step3 := add_triple (env := env) (pc_n := 15) (a := b) (b := a)
    (rest := b :: i :: rest) (gas_in := gas_in - 3 - 3) (active := active)
    h_code (by decide) rfl (by omega)
  have step4 := swap_triple (env := env) (pc_n := 16) (n := ⟨1, by decide⟩)
    (stack := (b + a) :: b :: i :: rest) (stack' := i :: b :: (b + a) :: rest)
    (gas_in := gas_in - 3 - 3 - 3) (active := active)
    h_code (by decide) rfl rfl (by omega)
  have step5 := push1_triple (env := env) (pc_n := 17) (data := UInt256.ofNat 1)
    (rest := i :: b :: (b + a) :: rest)
    (gas_in := gas_in - 3 - 3 - 3 - 3) (active := active)
    h_code (by decide) rfl (by omega)
  have step6 := swap_triple (env := env) (pc_n := 19) (n := ⟨0, by decide⟩)
    (stack := UInt256.ofNat 1 :: i :: b :: (b + a) :: rest)
    (stack' := i :: UInt256.ofNat 1 :: b :: (b + a) :: rest)
    (gas_in := gas_in - 3 - 3 - 3 - 3 - 3) (active := active)
    h_code (by decide) rfl rfl (by omega)
  have step7 := sub_triple (env := env) (pc_n := 20) (a := i) (b := UInt256.ofNat 1)
    (rest := b :: (b + a) :: rest)
    (gas_in := gas_in - 3 - 3 - 3 - 3 - 3 - 3) (active := active)
    h_code (by decide) rfl (by omega)
  have step8 := swap_triple (env := env) (pc_n := 21) (n := ⟨1, by decide⟩)
    (stack := (i - UInt256.ofNat 1) :: b :: (b + a) :: rest)
    (stack' := (b + a) :: b :: (i - UInt256.ofNat 1) :: rest)
    (gas_in := gas_in - 3 - 3 - 3 - 3 - 3 - 3 - 3) (active := active)
    h_code (by decide) rfl rfl (by omega)
  have step9 := push1_triple (env := env) (pc_n := 22) (data := UInt256.ofNat 7)
    (rest := (b + a) :: b :: (i - UInt256.ofNat 1) :: rest)
    (gas_in := gas_in - 3 - 3 - 3 - 3 - 3 - 3 - 3 - 3) (active := active)
    h_code (by decide) rfl (by omega)
  have step10 := jump_triple (env := env) (pc_n := 24) (dest := UInt256.ofNat 7)
    (rest := (b + a) :: b :: (i - UInt256.ofNat 1) :: rest)
    (gas_in := gas_in - 3 - 3 - 3 - 3 - 3 - 3 - 3 - 3 - 3) (active := active)
    h_code rfl (by rw [h_code]; rfl) (by omega)
  have chain := step1.seq <| step2.seq <| step3.seq <| step4.seq <| step5.seq <|
                step6.seq <| step7.seq <| step8.seq <| step9.seq step10
  intro s h_s
  obtain ⟨sf, hs, hf⟩ := chain s h_s
  refine ⟨sf, hs, hf.env_eq, ?_, hf.halt, hf.stack_eq, ?_, hf.active_eq⟩
  · show sf.pc.toNat = 7; rw [hf.pc]; rfl
  · show sf.gasAvailable = gas_in - 35; rw [hf.gas_eq]; omega

/-- **End block via per-opcode triples** — `JUMPDEST ; POP ; PUSH1 0 ; MSTORE ;
    PUSH1 0x20 ; PUSH1 0 ; RETURN`. Replaces ~190 lines of manual step plumbing
    with a 7-line chain. -/
theorem end_block_via_opcodes {env : ExecutionEnv}
    {b a : UInt256} {rest : List UInt256} {gas_in : Nat}
    (h_code : env.code = code) (h_gas : 18 ≤ gas_in) :
    Triple
      (StateAt env 25 (b :: a :: UInt256.ofNat 0 :: rest) gas_in (UInt256.ofNat 0))
      (fun sf => sf.halt = .Returned) := by
  have step1 := jumpdest_triple (env := env) (pc_n := 25) (gas_in := gas_in)
    (active := UInt256.ofNat 0) (stack := b :: a :: UInt256.ofNat 0 :: rest)
    h_code (by decide) rfl (by omega)
  have step2 := pop_triple (env := env) (pc_n := 26) (a := b)
    (gas_in := gas_in - 1) (active := UInt256.ofNat 0)
    (rest := a :: UInt256.ofNat 0 :: rest)
    h_code (by decide) rfl (by omega)
  have step3 := push1_triple (env := env) (pc_n := 27) (data := UInt256.ofNat 0)
    (gas_in := gas_in - 1 - 2) (active := UInt256.ofNat 0)
    (rest := a :: UInt256.ofNat 0 :: rest)
    h_code (by decide) rfl (by omega)
  have step4 := mstore_triple (env := env) (pc_n := 29) (value := a)
    (gas_in := gas_in - 1 - 2 - 3) (rest := UInt256.ofNat 0 :: rest)
    h_code (by decide) rfl (by omega)
  have step5 := push1_triple (env := env) (pc_n := 30) (data := UInt256.ofNat 0x20)
    (gas_in := gas_in - 1 - 2 - 3 - 6) (active := UInt256.ofNat 1)
    (rest := UInt256.ofNat 0 :: rest)
    h_code (by decide) rfl (by omega)
  have step6 := push1_triple (env := env) (pc_n := 32) (data := UInt256.ofNat 0)
    (gas_in := gas_in - 1 - 2 - 3 - 6 - 3) (active := UInt256.ofNat 1)
    (rest := UInt256.ofNat 0x20 :: UInt256.ofNat 0 :: rest)
    h_code (by decide) rfl (by omega)
  have step7 := return_triple (env := env) (pc_n := 34)
    (gas_in := gas_in - 1 - 2 - 3 - 6 - 3 - 3)
    (rest := UInt256.ofNat 0 :: rest)
    h_code rfl
  exact step1.seq <| step2.seq <| step3.seq <| step4.seq <|
        step5.seq <| step6.seq step7

/-- Init block as a triple: from `initState n` (with the calldata-decoding
    side condition), land at the loop head for `n`. Composed from four
    per-opcode triples (`push1`, `calldataload`, `push1`, `push1`) via
    `Triple.seq`. -/
theorem init_triple (n : Nat) (h_n : n ≤ 1000)
    (h_calldata : calldataN (calldataFor n) = UInt256.ofNat n) :
    Triple (fun s => s = initState n) (AtLoopHead n) := by
  -- Type parameters fixed for this program.
  set env := (initState n).executionEnv with h_env_def
  have h_envcode : env.code = code := rfl
  have h_envcd : env.calldata = calldataFor n := rfl
  -- The four opcode triples, instantiated for our program's PCs.
  have step1 := push1_triple (env := env) (pc_n := 0) (data := UInt256.ofNat 4)
    (rest := []) (gas_in := 100000) (active := UInt256.ofNat 0)
    h_envcode (by decide) rfl (by decide)
  have step2 := calldataload_triple (env := env) (pc_n := 2) (i := UInt256.ofNat 4)
    (rest := []) (gas_in := 100000 - 3) (active := UInt256.ofNat 0)
    h_envcode (by decide) rfl (by decide)
  have step3 := push1_triple (env := env) (pc_n := 3) (data := UInt256.ofNat 0)
    (rest := [UInt256.ofNat (Decode.beToNat
                (MachineState.readPadded env.calldata (UInt256.ofNat 4).toNat 32))])
    (gas_in := 100000 - 6) (active := UInt256.ofNat 0)
    h_envcode (by decide) rfl (by decide)
  have step4 := push1_triple (env := env) (pc_n := 5) (data := UInt256.ofNat 1)
    (rest := [UInt256.ofNat 0, UInt256.ofNat (Decode.beToNat
                (MachineState.readPadded env.calldata (UInt256.ofNat 4).toNat 32))])
    (gas_in := 100000 - 9) (active := UInt256.ofNat 0)
    h_envcode (by decide) rfl (by decide)
  -- Compose: step1 ▶ step2 ▶ step3 ▶ step4.
  have chain := step1.seq <| step2.seq <| step3.seq step4
  -- Apply chain to the initial state.
  intro s h_s
  subst h_s
  obtain ⟨sf, hs, h_final⟩ := chain (initState n) ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨sf, hs, ?_, h_final.pc, h_final.halt, ?_, ?_, ?_⟩
  · -- code = code  (env.code = code)
    rw [h_final.env_eq]; rfl
  · -- activeWords.toNat = 0
    rw [h_final.active_eq]; rfl
  · -- ∃ b a, stack = [b, a, ofNat n]
    refine ⟨UInt256.ofNat 1, UInt256.ofNat 0, ?_⟩
    rw [h_final.stack_eq]
    show [UInt256.ofNat 1, UInt256.ofNat 0, calldataN (calldataFor n)] = _
    rw [h_calldata]
  · -- gas ≥ 55*n + 38
    rw [h_final.gas_eq]
    show 100000 - 9 - 3 ≥ _
    omega

----------------------------------------------------------------------------
-- The loop and the whole program.
----------------------------------------------------------------------------

/-- **The loop runs to completion.** By induction on `k`: the base case is
    one `loop_check_taken_via_opcodes`; the step is
    `loop_check_continue_via_opcodes ; loop_body_via_opcodes` followed by
    the IH. All chained through `StateAt` (no raw `StepRunning`). -/
theorem loop_total_via_opcodes {env : ExecutionEnv} (k : Nat)
    (h_k_lt : k + 1 < UInt256.size)
    {b a : UInt256} {rest : List UInt256} {gas_in : Nat}
    (h_code : env.code = code) (h_gas : 55 * k + 20 ≤ gas_in) :
    Triple
      (StateAt env 7 (b :: a :: UInt256.ofNat k :: rest) gas_in (UInt256.ofNat 0))
      (fun sf => ∃ b' a',
        StateAt env 25 (b' :: a' :: UInt256.ofNat 0 :: rest)
          (gas_in - (55 * k + 20)) (UInt256.ofNat 0) sf) := by
  induction k generalizing b a gas_in with
  | zero =>
    intro s h_pre
    obtain ⟨sf, hs, hf⟩ := loop_check_taken_via_opcodes (env := env) (b := b) (a := a)
      (rest := rest) (gas_in := gas_in) (active := UInt256.ofNat 0)
      h_code (by omega) s h_pre
    exact ⟨sf, hs, b, a, hf⟩
  | succ k' ih =>
    intro s h_pre
    have h_i_nz : (UInt256.ofNat (k' + 1)).toNat ≠ 0 := by
      rw [Hoare.ofNat_toNat (k'+1) (by omega)]; omega
    obtain ⟨s1, hs1, hf1⟩ := loop_check_continue_via_opcodes (env := env) (b := b)
      (a := a) (i := UInt256.ofNat (k'+1)) (rest := rest) (gas_in := gas_in)
      (active := UInt256.ofNat 0) h_code h_i_nz (by omega) s h_pre
    obtain ⟨s2, hs2, hf2⟩ := loop_body_via_opcodes (env := env) (b := b) (a := a)
      (i := UInt256.ofNat (k'+1)) (rest := rest) (gas_in := gas_in - 20)
      (active := UInt256.ofNat 0) h_code (by omega) s1 hf1
    have h_iter : UInt256.ofNat (k'+1) - UInt256.ofNat 1 = UInt256.ofNat k' :=
      Hoare.ofNat_sub_one k' (by omega)
    have hf2' : StateAt env 7 ((b + a) :: b :: UInt256.ofNat k' :: rest)
                  (gas_in - 20 - 35) (UInt256.ofNat 0) s2 := by
      rw [← h_iter]; exact hf2
    obtain ⟨sf, hs3, b', a', hf3⟩ := ih (b := b + a) (a := b)
      (gas_in := gas_in - 20 - 35) (by omega) (by omega) s2 hf2'
    refine ⟨sf, hs1.append (hs2.append hs3), b', a', ?_⟩
    have h_gas_eq : gas_in - 20 - 35 - (55 * k' + 20) = gas_in - (55 * (k' + 1) + 20) := by
      omega
    exact h_gas_eq ▸ hf3

/-- Loop as a triple: from the loop head, reach the end head.
    Wraps `loop_total_via_opcodes` to expose the `AtLoopHead`/`AtEndHead`
    interface to `fib_correct`. -/
theorem loop_triple (n : Nat) (h_n : n ≤ 1000) :
    Triple (AtLoopHead n) AtEndHead := by
  intro s ⟨h_code, h_pc, h_halt, h_aw, ⟨b, a, h_stack⟩, h_gas⟩
  have h_size_big : 1002 ≤ UInt256.size := by decide
  have h_active_word : s.toMachineState.activeWords = UInt256.ofNat 0 := by
    apply Hoare.uint256_eq_of_toNat
    rw [h_aw]; rfl
  have h_fib : StateAt s.executionEnv 7 (b :: a :: UInt256.ofNat n :: [])
                  s.gasAvailable (UInt256.ofNat 0) s :=
    ⟨rfl, h_pc, h_halt, h_stack, rfl, h_active_word⟩
  obtain ⟨sf, hs, b', a', hf⟩ :=
    loop_total_via_opcodes (env := s.executionEnv) n (by omega) (b := b) (a := a)
      (rest := []) (gas_in := s.gasAvailable) h_code (by omega) s h_fib
  refine ⟨sf, hs, ?_, hf.pc, hf.halt, ?_, ⟨b', a', [], hf.stack_eq⟩, ?_⟩
  · rw [hf.env_eq]; exact h_code
  · rw [hf.active_eq]; rfl
  · rw [hf.gas_eq]; omega

/-- End block as a triple: from the end head, halt with `.Returned`.
    Wraps `end_block_via_opcodes`. -/
theorem end_triple : Triple AtEndHead (fun sf => sf.halt = .Returned) := by
  intro s ⟨h_code, h_pc, h_halt, h_aw, ⟨b, a, rest, h_stack⟩, h_gas⟩
  have h_active_word : s.toMachineState.activeWords = UInt256.ofNat 0 := by
    apply Hoare.uint256_eq_of_toNat
    rw [h_aw]; rfl
  have h_fib : StateAt s.executionEnv 25 (b :: a :: UInt256.ofNat 0 :: rest)
                  s.gasAvailable (UInt256.ofNat 0) s :=
    ⟨rfl, h_pc, h_halt, h_stack, rfl, h_active_word⟩
  exact end_block_via_opcodes (env := s.executionEnv) (b := b) (a := a) (rest := rest)
    (gas_in := s.gasAvailable) h_code h_gas s h_fib

/-- **The full program is correct.** From `initState n` with a small enough
    `n`, the relational `Step` semantics reaches a state with
    `halt = .Returned`. The proof is three `Triple.seq` applications over
    the per-block triples — no `obtain`-and-thread-eight-equalities, no
    manual `Steps.append` chain.

    The `n ≤ 1000` bound is conservative: it leaves enough gas
    (`55·1000 + 50 = 55050 ≤ 100000`) and keeps every intermediate
    `UInt256.ofNat k` well below `2^256`. -/
theorem fib_correct (n : Nat) (h_n : n ≤ 1000)
    (h_calldata : calldataN (calldataFor n) = UInt256.ofNat n) :
    ∃ sf : State, Steps (initState n) sf ∧ sf.halt = .Returned :=
  ((init_triple n h_n h_calldata).seq <| (loop_triple n h_n).seq end_triple)
    _ rfl

----------------------------------------------------------------------------
-- Value-correctness: the program returns the encoded `fib n`.
--
-- The termination claim `fib_correct` above doesn't say what the program
-- returned. The theorems below strengthen the chain to carry the
-- Fibonacci invariant through the loop and the memory/`hReturn`
-- equations through the end block. They culminate in `fib_returns`,
-- which asserts that the halted state's `hReturn` is exactly
-- `readPadded (writeBytes empty (wordBytes (ofNat (fib n))) 0) 0 32`
-- — i.e. the 32-byte big-endian encoding of `fib n` (modulo `2^256`
-- when `fib (n+1)` overflows, but we guard that with `h_fib_size`).
----------------------------------------------------------------------------

/-- Local memory-tracking wrappers — same pattern as the per-opcode
    wrappers above, but each takes/produces an extra `s.memory = m`
    conjunct so we can thread memory through the end block. -/
theorem calldataload_triple_mem {env : ExecutionEnv} {pc_n : Nat} {i : UInt256}
    {rest : List UInt256} {gas_in : Nat} {active : UInt256} {m : ByteArray}
    (h_code : env.code = code)
    (h_pcb : pc_n + 1 < UInt256.size)
    (h_dec : decodeFib pc_n = some (.CALLDATALOAD, none))
    (h_gas : 3 ≤ gas_in) :
    Triple
      (fun s => StateAt env pc_n (i :: rest) gas_in active s ∧ s.memory = m)
      (fun s => StateAt env (pc_n + 1)
                  (MachineState.readWord env.calldata i.toNat :: rest)
                  (gas_in - 3) active s ∧ s.memory = m) :=
  Hoare.calldataload_triple_mem h_pcb (decodeAt_of_decodeFib h_code h_dec) h_gas

theorem jumpdest_triple_mem {env : ExecutionEnv} {pc_n : Nat}
    {stack : List UInt256} {gas_in : Nat} {active : UInt256} {m : ByteArray}
    (h_code : env.code = code)
    (h_pcb : pc_n + 1 < UInt256.size)
    (h_dec : decodeFib pc_n = some (.JUMPDEST, none))
    (h_gas : 1 ≤ gas_in) :
    Triple
      (fun s => StateAt env pc_n stack gas_in active s ∧ s.memory = m)
      (fun s => StateAt env (pc_n + 1) stack (gas_in - 1) active s ∧ s.memory = m) :=
  Hoare.jumpdest_triple_mem h_pcb (decodeAt_of_decodeFib h_code h_dec) h_gas

theorem pop_triple_mem {env : ExecutionEnv} {pc_n : Nat} {a : UInt256}
    {rest : List UInt256} {gas_in : Nat} {active : UInt256} {m : ByteArray}
    (h_code : env.code = code)
    (h_pcb : pc_n + 1 < UInt256.size)
    (h_dec : decodeFib pc_n = some (.POP, none))
    (h_gas : 2 ≤ gas_in) :
    Triple
      (fun s => StateAt env pc_n (a :: rest) gas_in active s ∧ s.memory = m)
      (fun s => StateAt env (pc_n + 1) rest (gas_in - 2) active s ∧ s.memory = m) :=
  Hoare.pop_triple_mem h_pcb (decodeAt_of_decodeFib h_code h_dec) h_gas

theorem push1_triple_mem {env : ExecutionEnv} {pc_n : Nat} {data : UInt256}
    {rest : List UInt256} {gas_in : Nat} {active : UInt256} {m : ByteArray}
    (h_code : env.code = code)
    (h_pcb : pc_n + 2 < UInt256.size)
    (h_dec : decodeFib pc_n = some (.Push ⟨1, by decide⟩, some (data, 1)))
    (h_gas : 3 ≤ gas_in) :
    Triple
      (fun s => StateAt env pc_n rest gas_in active s ∧ s.memory = m)
      (fun s => StateAt env (pc_n + 2) (data :: rest) (gas_in - 3) active s
                ∧ s.memory = m) :=
  Hoare.push1_triple_mem h_pcb (decodeAt_of_decodeFib h_code h_dec) h_gas

theorem mstore_triple_mem {env : ExecutionEnv} {pc_n : Nat} {value : UInt256}
    {rest : List UInt256} {gas_in : Nat} {m : ByteArray}
    (h_code : env.code = code)
    (h_pcb : pc_n + 1 < UInt256.size)
    (h_dec : decodeFib pc_n = some (.MSTORE, none))
    (h_gas : 6 ≤ gas_in) :
    Triple
      (fun s => StateAt env pc_n (UInt256.ofNat 0 :: value :: rest) gas_in
                  (UInt256.ofNat 0) s ∧ s.memory = m)
      (fun s => StateAt env (pc_n + 1) rest (gas_in - 6) (UInt256.ofNat 1) s
                ∧ s.memory =
                  MachineState.writeBytes m (MachineState.wordBytes value) 0) :=
  Hoare.mstore_triple_mem h_pcb (decodeAt_of_decodeFib h_code h_dec) h_gas

theorem return_triple_mem {env : ExecutionEnv} {pc_n : Nat}
    {rest : List UInt256} {gas_in : Nat} {m : ByteArray}
    (h_code : env.code = code)
    (h_dec : decodeFib pc_n = some (.RETURN, none)) :
    Triple
      (fun s => StateAt env pc_n (UInt256.ofNat 0 :: UInt256.ofNat 0x20 :: rest)
                  gas_in (UInt256.ofNat 1) s ∧ s.memory = m)
      (fun sf => sf.halt = .Returned ∧
        sf.hReturn = MachineState.readPadded m 0 32) :=
  Hoare.return_triple_mem (decodeAt_of_decodeFib h_code h_dec)

theorem dup_triple_mem {env : ExecutionEnv} {pc_n : Nat} {n : Fin 16} {v : UInt256}
    {stack : List UInt256} {gas_in : Nat} {active : UInt256} {m : ByteArray}
    (h_code : env.code = code)
    (h_pcb : pc_n + 1 < UInt256.size)
    (h_dec : decodeFib pc_n = some (.Dup ⟨n⟩, none))
    (h_get : stack[n.val]? = some v)
    (h_gas : 3 ≤ gas_in) :
    Triple
      (fun s => StateAt env pc_n stack gas_in active s ∧ s.memory = m)
      (fun s => StateAt env (pc_n + 1) (v :: stack) (gas_in - 3) active s ∧ s.memory = m) :=
  Hoare.dup_triple_mem h_pcb (decodeAt_of_decodeFib h_code h_dec) h_get h_gas

theorem iszero_triple_mem {env : ExecutionEnv} {pc_n : Nat} {a : UInt256}
    {rest : List UInt256} {gas_in : Nat} {active : UInt256} {m : ByteArray}
    (h_code : env.code = code)
    (h_pcb : pc_n + 1 < UInt256.size)
    (h_dec : decodeFib pc_n = some (.ISZERO, none))
    (h_gas : 3 ≤ gas_in) :
    Triple
      (fun s => StateAt env pc_n (a :: rest) gas_in active s ∧ s.memory = m)
      (fun s => StateAt env (pc_n + 1) (UInt256.isZero a :: rest) (gas_in - 3) active s
                ∧ s.memory = m) :=
  Hoare.iszero_triple_mem h_pcb (decodeAt_of_decodeFib h_code h_dec) h_gas

theorem swap_triple_mem {env : ExecutionEnv} {pc_n : Nat} {n : Fin 16}
    {stack stack' : List UInt256} {gas_in : Nat} {active : UInt256} {m : ByteArray}
    (h_code : env.code = code)
    (h_pcb : pc_n + 1 < UInt256.size)
    (h_dec : decodeFib pc_n = some (.Swap ⟨n⟩, none))
    (h_sw : stack.exchange 0 (n.val + 1) = some stack')
    (h_gas : 3 ≤ gas_in) :
    Triple
      (fun s => StateAt env pc_n stack gas_in active s ∧ s.memory = m)
      (fun s => StateAt env (pc_n + 1) stack' (gas_in - 3) active s ∧ s.memory = m) :=
  Hoare.swap_triple_mem h_pcb (decodeAt_of_decodeFib h_code h_dec) h_sw h_gas

theorem add_triple_mem {env : ExecutionEnv} {pc_n : Nat} {a b : UInt256}
    {rest : List UInt256} {gas_in : Nat} {active : UInt256} {m : ByteArray}
    (h_code : env.code = code)
    (h_pcb : pc_n + 1 < UInt256.size)
    (h_dec : decodeFib pc_n = some (.ADD, none))
    (h_gas : 3 ≤ gas_in) :
    Triple
      (fun s => StateAt env pc_n (a :: b :: rest) gas_in active s ∧ s.memory = m)
      (fun s => StateAt env (pc_n + 1) ((a + b) :: rest) (gas_in - 3) active s
                ∧ s.memory = m) :=
  Hoare.add_triple_mem h_pcb (decodeAt_of_decodeFib h_code h_dec) h_gas

theorem sub_triple_mem {env : ExecutionEnv} {pc_n : Nat} {a b : UInt256}
    {rest : List UInt256} {gas_in : Nat} {active : UInt256} {m : ByteArray}
    (h_code : env.code = code)
    (h_pcb : pc_n + 1 < UInt256.size)
    (h_dec : decodeFib pc_n = some (.SUB, none))
    (h_gas : 3 ≤ gas_in) :
    Triple
      (fun s => StateAt env pc_n (a :: b :: rest) gas_in active s ∧ s.memory = m)
      (fun s => StateAt env (pc_n + 1) ((a - b) :: rest) (gas_in - 3) active s
                ∧ s.memory = m) :=
  Hoare.sub_triple_mem h_pcb (decodeAt_of_decodeFib h_code h_dec) h_gas

theorem jump_triple_mem {env : ExecutionEnv} {pc_n : Nat} {dest : UInt256}
    {rest : List UInt256} {gas_in : Nat} {active : UInt256} {m : ByteArray}
    (h_code : env.code = code)
    (h_dec : decodeFib pc_n = some (.JUMP, none))
    (h_valid : Decode.isValidJumpDest env.code dest.toNat = true)
    (h_gas : 8 ≤ gas_in) :
    Triple
      (fun s => StateAt env pc_n (dest :: rest) gas_in active s ∧ s.memory = m)
      (fun s => StateAt env dest.toNat rest (gas_in - 8) active s ∧ s.memory = m) :=
  Hoare.jump_triple_mem (decodeAt_of_decodeFib h_code h_dec) h_valid h_gas

theorem jumpi_taken_triple_mem {env : ExecutionEnv} {pc_n : Nat} {dest cond : UInt256}
    {rest : List UInt256} {gas_in : Nat} {active : UInt256} {m : ByteArray}
    (h_code : env.code = code)
    (h_dec : decodeFib pc_n = some (.JUMPI, none))
    (h_cond : UInt256.isTrue cond)
    (h_valid : Decode.isValidJumpDest env.code dest.toNat = true)
    (h_gas : 10 ≤ gas_in) :
    Triple
      (fun s => StateAt env pc_n (dest :: cond :: rest) gas_in active s ∧ s.memory = m)
      (fun s => StateAt env dest.toNat rest (gas_in - 10) active s ∧ s.memory = m) :=
  Hoare.jumpi_taken_triple_mem (decodeAt_of_decodeFib h_code h_dec) h_cond h_valid h_gas

theorem jumpi_notTaken_triple_mem {env : ExecutionEnv} {pc_n : Nat} {dest cond : UInt256}
    {rest : List UInt256} {gas_in : Nat} {active : UInt256} {m : ByteArray}
    (h_code : env.code = code)
    (h_pcb : pc_n + 1 < UInt256.size)
    (h_dec : decodeFib pc_n = some (.JUMPI, none))
    (h_cond : ¬ UInt256.isTrue cond)
    (h_gas : 10 ≤ gas_in) :
    Triple
      (fun s => StateAt env pc_n (dest :: cond :: rest) gas_in active s ∧ s.memory = m)
      (fun s => StateAt env (pc_n + 1) rest (gas_in - 10) active s ∧ s.memory = m) :=
  Hoare.jumpi_notTaken_triple_mem h_pcb (decodeAt_of_decodeFib h_code h_dec) h_cond h_gas

/-- Memory-tracking variant of `loop_check_taken_via_opcodes`. Same proof
    structure but uses the `_mem` per-opcode wrappers so `s.memory = m`
    threads through to the post-condition. -/
theorem loop_check_taken_via_opcodes_mem {env : ExecutionEnv}
    {b a : UInt256} {rest : List UInt256} {gas_in : Nat} {active : UInt256}
    {m : ByteArray}
    (h_code : env.code = code) (h_gas : 20 ≤ gas_in) :
    Triple
      (fun s => StateAt env 7 (b :: a :: UInt256.ofNat 0 :: rest) gas_in active s
                ∧ s.memory = m)
      (fun s => StateAt env 25 (b :: a :: UInt256.ofNat 0 :: rest) (gas_in - 20)
                  active s ∧ s.memory = m) := by
  have step1 := jumpdest_triple_mem (env := env) (pc_n := 7) (gas_in := gas_in)
    (active := active) (stack := b :: a :: UInt256.ofNat 0 :: rest) (m := m)
    h_code (by decide) rfl (by omega)
  have step2 := dup_triple_mem (env := env) (pc_n := 8) (n := ⟨2, by decide⟩)
    (v := UInt256.ofNat 0) (gas_in := gas_in - 1) (active := active)
    (stack := b :: a :: UInt256.ofNat 0 :: rest) (m := m)
    h_code (by decide) rfl rfl (by omega)
  have step3 := iszero_triple_mem (env := env) (pc_n := 9) (a := UInt256.ofNat 0)
    (gas_in := gas_in - 1 - 3) (active := active)
    (rest := b :: a :: UInt256.ofNat 0 :: rest) (m := m)
    h_code (by decide) rfl (by omega)
  have step4 := push1_triple_mem (env := env) (pc_n := 10) (data := UInt256.ofNat 0x19)
    (gas_in := gas_in - 1 - 3 - 3) (active := active)
    (rest := UInt256.isZero (UInt256.ofNat 0) :: b :: a :: UInt256.ofNat 0 :: rest)
    (m := m)
    h_code (by decide) rfl (by omega)
  have step5 := jumpi_taken_triple_mem (env := env) (pc_n := 12)
    (dest := UInt256.ofNat 0x19) (cond := UInt256.isZero (UInt256.ofNat 0))
    (gas_in := gas_in - 1 - 3 - 3 - 3) (active := active)
    (rest := b :: a :: UInt256.ofNat 0 :: rest) (m := m)
    h_code rfl (by decide) (by rw [h_code]; rfl) (by omega)
  have chain := step1.seq <| step2.seq <| step3.seq <| step4.seq step5
  intro s h_s
  obtain ⟨sf, hs, hf, h_mem⟩ := chain s h_s
  refine ⟨sf, hs, ⟨hf.env_eq, ?_, hf.halt, hf.stack_eq, ?_, hf.active_eq⟩, h_mem⟩
  · show sf.pc.toNat = 25; rw [hf.pc]; rfl
  · show sf.gasAvailable = gas_in - 20; rw [hf.gas_eq]; omega

/-- Memory-tracking variant of `loop_check_continue_via_opcodes`. -/
theorem loop_check_continue_via_opcodes_mem {env : ExecutionEnv}
    {b a i : UInt256} {rest : List UInt256} {gas_in : Nat} {active : UInt256}
    {m : ByteArray}
    (h_code : env.code = code) (h_i_nz : i.toNat ≠ 0) (h_gas : 20 ≤ gas_in) :
    Triple
      (fun s => StateAt env 7 (b :: a :: i :: rest) gas_in active s ∧ s.memory = m)
      (fun s => StateAt env 13 (b :: a :: i :: rest) (gas_in - 20) active s
                ∧ s.memory = m) := by
  have step1 := jumpdest_triple_mem (env := env) (pc_n := 7) (gas_in := gas_in)
    (active := active) (stack := b :: a :: i :: rest) (m := m)
    h_code (by decide) rfl (by omega)
  have step2 := dup_triple_mem (env := env) (pc_n := 8) (n := ⟨2, by decide⟩)
    (v := i) (gas_in := gas_in - 1) (active := active)
    (stack := b :: a :: i :: rest) (m := m)
    h_code (by decide) rfl rfl (by omega)
  have step3 := iszero_triple_mem (env := env) (pc_n := 9) (a := i)
    (gas_in := gas_in - 1 - 3) (active := active)
    (rest := b :: a :: i :: rest) (m := m)
    h_code (by decide) rfl (by omega)
  have step4 := push1_triple_mem (env := env) (pc_n := 10) (data := UInt256.ofNat 0x19)
    (gas_in := gas_in - 1 - 3 - 3) (active := active)
    (rest := UInt256.isZero i :: b :: a :: i :: rest) (m := m)
    h_code (by decide) rfl (by omega)
  have step5 := jumpi_notTaken_triple_mem (env := env) (pc_n := 12)
    (dest := UInt256.ofNat 0x19) (cond := UInt256.isZero i)
    (gas_in := gas_in - 1 - 3 - 3 - 3) (active := active)
    (rest := b :: a :: i :: rest) (m := m)
    h_code (by decide) rfl
    (by simp [UInt256.isTrue, UInt256.isZero, h_i_nz]; rfl) (by omega)
  have chain := step1.seq <| step2.seq <| step3.seq <| step4.seq step5
  intro s h_s
  obtain ⟨sf, hs, hf, h_mem⟩ := chain s h_s
  refine ⟨sf, hs, ⟨hf.env_eq, ?_, hf.halt, hf.stack_eq, ?_, hf.active_eq⟩, h_mem⟩
  · show sf.pc.toNat = 13; rw [hf.pc]
  · show sf.gasAvailable = gas_in - 20; rw [hf.gas_eq]; omega

/-- Memory-tracking variant of `loop_body_via_opcodes`. -/
theorem loop_body_via_opcodes_mem {env : ExecutionEnv}
    {b a i : UInt256} {rest : List UInt256} {gas_in : Nat} {active : UInt256}
    {m : ByteArray}
    (h_code : env.code = code) (h_gas : 35 ≤ gas_in) :
    Triple
      (fun s => StateAt env 13 (b :: a :: i :: rest) gas_in active s ∧ s.memory = m)
      (fun s => StateAt env 7 ((b + a) :: b :: (i - UInt256.ofNat 1) :: rest)
                  (gas_in - 35) active s ∧ s.memory = m) := by
  have step1 := swap_triple_mem (env := env) (pc_n := 13) (n := ⟨0, by decide⟩)
    (stack := b :: a :: i :: rest) (stack' := a :: b :: i :: rest)
    (gas_in := gas_in) (active := active) (m := m)
    h_code (by decide) rfl rfl (by omega)
  have step2 := dup_triple_mem (env := env) (pc_n := 14) (n := ⟨1, by decide⟩)
    (v := b) (stack := a :: b :: i :: rest)
    (gas_in := gas_in - 3) (active := active) (m := m)
    h_code (by decide) rfl rfl (by omega)
  have step3 := add_triple_mem (env := env) (pc_n := 15) (a := b) (b := a)
    (rest := b :: i :: rest) (gas_in := gas_in - 3 - 3) (active := active) (m := m)
    h_code (by decide) rfl (by omega)
  have step4 := swap_triple_mem (env := env) (pc_n := 16) (n := ⟨1, by decide⟩)
    (stack := (b + a) :: b :: i :: rest) (stack' := i :: b :: (b + a) :: rest)
    (gas_in := gas_in - 3 - 3 - 3) (active := active) (m := m)
    h_code (by decide) rfl rfl (by omega)
  have step5 := push1_triple_mem (env := env) (pc_n := 17) (data := UInt256.ofNat 1)
    (rest := i :: b :: (b + a) :: rest)
    (gas_in := gas_in - 3 - 3 - 3 - 3) (active := active) (m := m)
    h_code (by decide) rfl (by omega)
  have step6 := swap_triple_mem (env := env) (pc_n := 19) (n := ⟨0, by decide⟩)
    (stack := UInt256.ofNat 1 :: i :: b :: (b + a) :: rest)
    (stack' := i :: UInt256.ofNat 1 :: b :: (b + a) :: rest)
    (gas_in := gas_in - 3 - 3 - 3 - 3 - 3) (active := active) (m := m)
    h_code (by decide) rfl rfl (by omega)
  have step7 := sub_triple_mem (env := env) (pc_n := 20) (a := i) (b := UInt256.ofNat 1)
    (rest := b :: (b + a) :: rest)
    (gas_in := gas_in - 3 - 3 - 3 - 3 - 3 - 3) (active := active) (m := m)
    h_code (by decide) rfl (by omega)
  have step8 := swap_triple_mem (env := env) (pc_n := 21) (n := ⟨1, by decide⟩)
    (stack := (i - UInt256.ofNat 1) :: b :: (b + a) :: rest)
    (stack' := (b + a) :: b :: (i - UInt256.ofNat 1) :: rest)
    (gas_in := gas_in - 3 - 3 - 3 - 3 - 3 - 3 - 3) (active := active) (m := m)
    h_code (by decide) rfl rfl (by omega)
  have step9 := push1_triple_mem (env := env) (pc_n := 22) (data := UInt256.ofNat 7)
    (rest := (b + a) :: b :: (i - UInt256.ofNat 1) :: rest)
    (gas_in := gas_in - 3 - 3 - 3 - 3 - 3 - 3 - 3 - 3) (active := active) (m := m)
    h_code (by decide) rfl (by omega)
  have step10 := jump_triple_mem (env := env) (pc_n := 24) (dest := UInt256.ofNat 7)
    (rest := (b + a) :: b :: (i - UInt256.ofNat 1) :: rest)
    (gas_in := gas_in - 3 - 3 - 3 - 3 - 3 - 3 - 3 - 3 - 3)
    (active := active) (m := m)
    h_code rfl (by rw [h_code]; rfl) (by omega)
  have chain := step1.seq <| step2.seq <| step3.seq <| step4.seq <| step5.seq <|
                step6.seq <| step7.seq <| step8.seq <| step9.seq step10
  intro s h_s
  obtain ⟨sf, hs, hf, h_mem⟩ := chain s h_s
  refine ⟨sf, hs, ⟨hf.env_eq, ?_, hf.halt, hf.stack_eq, ?_, hf.active_eq⟩, h_mem⟩
  · show sf.pc.toNat = 7; rw [hf.pc]; rfl
  · show sf.gasAvailable = gas_in - 35; rw [hf.gas_eq]; omega
/-- Strengthened loop: from PC 7 with the Fibonacci-pair invariant
    `[ofNat (fib (j+1)), ofNat (fib j), ofNat k, rest]` and `k`
    iterations to run, reach PC 25 with stack
    `[ofNat (fib (j+k+1)), ofNat (fib (j+k)), 0, rest]`. The two
    side-conditions `h_size` and `h_fib_size` keep all intermediate
    `ofNat (·)` values below `2^256` so the loop body's modular
    `UInt256.add` agrees with `Nat.add`. -/
theorem loop_total_fib (j k : Nat)
    (h_size : j + k + 1 < UInt256.size)
    (h_fib_size : fib (j + k + 1) < UInt256.size)
    {env : ExecutionEnv} {rest : List UInt256} {gas_in : Nat} {m : ByteArray}
    (h_code : env.code = code) (h_gas : 55 * k + 20 ≤ gas_in) :
    Triple
      (fun s => StateAt env 7
        (UInt256.ofNat (fib (j+1)) :: UInt256.ofNat (fib j) ::
          UInt256.ofNat k :: rest)
        gas_in (UInt256.ofNat 0) s ∧ s.memory = m)
      (fun s => StateAt env 25
        (UInt256.ofNat (fib (j+k+1)) :: UInt256.ofNat (fib (j+k)) ::
          UInt256.ofNat 0 :: rest)
        (gas_in - (55 * k + 20)) (UInt256.ofNat 0) s ∧ s.memory = m) := by
  induction k generalizing j gas_in with
  | zero =>
    intro s h_pre
    have step := loop_check_taken_via_opcodes_mem (env := env)
      (b := UInt256.ofNat (fib (j+1))) (a := UInt256.ofNat (fib j))
      (rest := rest) (gas_in := gas_in) (active := UInt256.ofNat 0) (m := m)
      h_code (by omega) s h_pre
    have h1 : j + 0 + 1 = j + 1 := by omega
    have h2 : j + 0 = j := by omega
    rw [h1, h2]
    exact step
  | succ k' ih =>
    intro s h_pre
    have h_i_nz : (UInt256.ofNat (k'+1)).toNat ≠ 0 := by
      rw [Hoare.ofNat_toNat (k'+1) (by omega)]; omega
    obtain ⟨s1, hs1, hf1⟩ := loop_check_continue_via_opcodes_mem (env := env)
      (b := UInt256.ofNat (fib (j+1))) (a := UInt256.ofNat (fib j))
      (i := UInt256.ofNat (k'+1))
      (rest := rest) (gas_in := gas_in) (active := UInt256.ofNat 0) (m := m)
      h_code h_i_nz (by omega) s h_pre
    obtain ⟨s2, hs2, hf2⟩ := loop_body_via_opcodes_mem (env := env)
      (b := UInt256.ofNat (fib (j+1))) (a := UInt256.ofNat (fib j))
      (i := UInt256.ofNat (k'+1)) (rest := rest) (gas_in := gas_in - 20)
      (active := UInt256.ofNat 0) (m := m)
      h_code (by omega) s1 hf1
    have h_add : UInt256.ofNat (fib (j+1)) + UInt256.ofNat (fib j)
                 = UInt256.ofNat (fib (j+2)) := by
      have h_bound : fib (j+1) + fib j < UInt256.size := by
        have h_def : fib (j+1) + fib j = fib (j+2) := rfl
        rw [h_def]
        have h_le : fib (j+2) ≤ fib (j + (k'+1) + 1) := by
          have h_idx : j + (k'+1) + 1 = (j + 2) + k' := by omega
          rw [h_idx]; exact fib_le_add (j+2) k'
        omega
      rw [Hoare.ofNat_add (fib (j+1)) (fib j) h_bound]
      rfl
    have h_sub : UInt256.ofNat (k'+1) - UInt256.ofNat 1 = UInt256.ofNat k' :=
      Hoare.ofNat_sub_one k' (by omega)
    have hf2' :
        StateAt env 7
          (UInt256.ofNat (fib (j+2)) :: UInt256.ofNat (fib (j+1)) ::
            UInt256.ofNat k' :: rest)
          (gas_in - 20 - 35) (UInt256.ofNat 0) s2
        ∧ s2.memory = m := by
      have h_stack :
          (UInt256.ofNat (fib (j+1)) + UInt256.ofNat (fib j)) ::
            UInt256.ofNat (fib (j+1)) ::
            (UInt256.ofNat (k'+1) - UInt256.ofNat 1) :: rest
          = UInt256.ofNat (fib (j+2)) ::
            UInt256.ofNat (fib (j+1)) ::
            UInt256.ofNat k' :: rest := by
        rw [h_add, h_sub]
      exact ⟨h_stack ▸ hf2.1, hf2.2⟩
    have h_idx_size : (j + 1) + k' + 1 < UInt256.size := by omega
    have h_idx_fib : fib ((j+1) + k' + 1) < UInt256.size := by
      have : (j+1) + k' + 1 = j + (k'+1) + 1 := by omega
      rw [this]; exact h_fib_size
    obtain ⟨sf, hs3, hf3⟩ :=
      ih (j := j+1) (gas_in := gas_in - 20 - 35) h_idx_size h_idx_fib
         (by omega) s2 hf2'
    refine ⟨sf, hs1.append (hs2.append hs3), ?_⟩
    have h_idx1 : (j + 1) + k' + 1 = j + (k' + 1) + 1 := by omega
    have h_idx2 : (j + 1) + k' = j + (k' + 1) := by omega
    have h_gas_eq : gas_in - 20 - 35 - (55 * k' + 20) = gas_in - (55 * (k'+1) + 20) := by
      omega
    rw [← h_idx1, ← h_idx2, ← h_gas_eq]
    exact hf3

/-- Loop as a triple, with the Fibonacci invariant: starting from
    `[ofNat 1, ofNat 0, ofNat n]` at PC 7 (i.e. `[fib 1, fib 0, n]`),
    reach `[ofNat (fib (n+1)), ofNat (fib n), 0]` at PC 25. -/
theorem loop_fib_triple (n : Nat) (h_n : n ≤ 1000)
    (h_fib_size : fib (n + 1) < UInt256.size)
    {env : ExecutionEnv} {rest : List UInt256} {gas_in : Nat} {m : ByteArray}
    (h_code : env.code = code) (h_gas : 55 * n + 20 ≤ gas_in) :
    Triple
      (fun s => StateAt env 7
        (UInt256.ofNat 1 :: UInt256.ofNat 0 :: UInt256.ofNat n :: rest)
        gas_in (UInt256.ofNat 0) s ∧ s.memory = m)
      (fun s => StateAt env 25
        (UInt256.ofNat (fib (n+1)) :: UInt256.ofNat (fib n) ::
          UInt256.ofNat 0 :: rest)
        (gas_in - (55 * n + 20)) (UInt256.ofNat 0) s ∧ s.memory = m) := by
  have h_size : 0 + n + 1 < UInt256.size := by
    have : UInt256.size = 2^256 := by decide
    omega
  have h_fib : fib (0 + n + 1) < UInt256.size := by
    have h : 0 + n + 1 = n + 1 := by omega
    rw [h]; exact h_fib_size
  have h_pre_eq :
      UInt256.ofNat 1 :: UInt256.ofNat 0 :: UInt256.ofNat n :: rest
    = UInt256.ofNat (fib (0+1)) :: UInt256.ofNat (fib 0) ::
      UInt256.ofNat n :: rest := rfl
  have h_post_eq :
      UInt256.ofNat (fib (0+n+1)) :: UInt256.ofNat (fib (0+n)) ::
      UInt256.ofNat 0 :: rest
    = UInt256.ofNat (fib (n+1)) :: UInt256.ofNat (fib n) ::
      UInt256.ofNat 0 :: rest := by
    have h1 : 0 + n + 1 = n + 1 := by omega
    have h2 : 0 + n = n := by omega
    rw [h1, h2]
  rw [h_pre_eq, ← h_post_eq]
  exact loop_total_fib 0 n h_size h_fib h_code h_gas

/-- End-block with value tracking — chained from the 5 memory-tracking
    per-opcode triples via `Triple.seq`. From PC 25 with stack
    `[b, a, 0, rest]` and `memory = memIn`, reach `halt = .Returned`
    with `sf.hReturn = readPadded (writeBytes memIn (wordBytes a) 0) 0 32`. -/
theorem end_block_value_via_opcodes {env : ExecutionEnv}
    {b a : UInt256} {rest : List UInt256} {gas_in : Nat} {memIn : ByteArray}
    (h_code : env.code = code) (h_gas : 18 ≤ gas_in) :
    Triple
      (fun s => StateAt env 25 (b :: a :: UInt256.ofNat 0 :: rest) gas_in
                  (UInt256.ofNat 0) s ∧ s.memory = memIn)
      (fun sf => sf.halt = .Returned ∧
        sf.hReturn = MachineState.readPadded
          (MachineState.writeBytes memIn (MachineState.wordBytes a) 0) 0 32) := by
  have step1 := jumpdest_triple_mem (env := env) (pc_n := 25)
    (stack := b :: a :: UInt256.ofNat 0 :: rest) (gas_in := gas_in)
    (active := UInt256.ofNat 0) (m := memIn)
    h_code (by decide) rfl (by omega)
  have step2 := pop_triple_mem (env := env) (pc_n := 26) (a := b)
    (rest := a :: UInt256.ofNat 0 :: rest) (gas_in := gas_in - 1)
    (active := UInt256.ofNat 0) (m := memIn)
    h_code (by decide) rfl (by omega)
  have step3 := push1_triple_mem (env := env) (pc_n := 27)
    (data := UInt256.ofNat 0)
    (rest := a :: UInt256.ofNat 0 :: rest) (gas_in := gas_in - 1 - 2)
    (active := UInt256.ofNat 0) (m := memIn)
    h_code (by decide) rfl (by omega)
  have step4 := mstore_triple_mem (env := env) (pc_n := 29) (value := a)
    (rest := UInt256.ofNat 0 :: rest) (gas_in := gas_in - 1 - 2 - 3) (m := memIn)
    h_code (by decide) rfl (by omega)
  let memOut := MachineState.writeBytes memIn (MachineState.wordBytes a) 0
  have step5 := push1_triple_mem (env := env) (pc_n := 30)
    (data := UInt256.ofNat 0x20)
    (rest := UInt256.ofNat 0 :: rest) (gas_in := gas_in - 12)
    (active := UInt256.ofNat 1) (m := memOut)
    h_code (by decide) rfl (by omega)
  have step6 := push1_triple_mem (env := env) (pc_n := 32)
    (data := UInt256.ofNat 0)
    (rest := UInt256.ofNat 0x20 :: UInt256.ofNat 0 :: rest)
    (gas_in := gas_in - 12 - 3) (active := UInt256.ofNat 1) (m := memOut)
    h_code (by decide) rfl (by omega)
  have step7 := return_triple_mem (env := env) (pc_n := 34)
    (rest := UInt256.ofNat 0 :: rest)
    (gas_in := gas_in - 12 - 3 - 3) (m := memOut)
    h_code rfl
  exact step1.seq <| step2.seq <| step3.seq <| step4.seq <|
        step5.seq <| step6.seq step7

/-- Init triple, value version: from `initState n` (with the
    calldata-decoding side condition), reach PC 7 with stack
    `[ofNat 1, ofNat 0, ofNat n]` and memory `ByteArray.empty`. The
    chain uses memory-tracking triples so `s.memory = ByteArray.empty`
    threads through automatically. -/
theorem init_value_triple (n : Nat) (_h_n : n ≤ 1000)
    (h_calldata : calldataN (calldataFor n) = UInt256.ofNat n) :
    Triple (fun s => s = initState n)
      (fun s =>
        StateAt (initState n).executionEnv 7
          (UInt256.ofNat 1 :: UInt256.ofNat 0 :: UInt256.ofNat n :: [])
          (100000 - 12) (UInt256.ofNat 0) s
        ∧ s.memory = ByteArray.empty) := by
  set env := (initState n).executionEnv with h_env_def
  have h_envcode : env.code = code := rfl
  have step1 := push1_triple_mem (env := env) (pc_n := 0) (data := UInt256.ofNat 4)
    (rest := []) (gas_in := 100000) (active := UInt256.ofNat 0)
    (m := ByteArray.empty)
    h_envcode (by decide) rfl (by decide)
  have step2 := calldataload_triple_mem (env := env) (pc_n := 2)
    (i := UInt256.ofNat 4) (rest := []) (gas_in := 100000 - 3)
    (active := UInt256.ofNat 0) (m := ByteArray.empty)
    h_envcode (by decide) rfl (by decide)
  have step3 := push1_triple_mem (env := env) (pc_n := 3) (data := UInt256.ofNat 0)
    (rest := [MachineState.readWord env.calldata (UInt256.ofNat 4).toNat])
    (gas_in := 100000 - 6) (active := UInt256.ofNat 0)
    (m := ByteArray.empty)
    h_envcode (by decide) rfl (by decide)
  have step4 := push1_triple_mem (env := env) (pc_n := 5) (data := UInt256.ofNat 1)
    (rest := [UInt256.ofNat 0,
              MachineState.readWord env.calldata (UInt256.ofNat 4).toNat])
    (gas_in := 100000 - 9) (active := UInt256.ofNat 0)
    (m := ByteArray.empty)
    h_envcode (by decide) rfl (by decide)
  intro s h_s
  subst h_s
  obtain ⟨sf, hs, hf, h_mem⟩ :=
    (step1.seq <| step2.seq <| step3.seq step4)
    (initState n) ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  refine ⟨sf, hs, ⟨hf.env_eq, hf.pc, hf.halt, ?_, hf.gas_eq, hf.active_eq⟩, h_mem⟩
  rw [hf.stack_eq]
  show [UInt256.ofNat 1, UInt256.ofNat 0,
        MachineState.readWord env.calldata (UInt256.ofNat 4).toNat] =
       [UInt256.ofNat 1, UInt256.ofNat 0, UInt256.ofNat n]
  have : MachineState.readWord env.calldata (UInt256.ofNat 4).toNat
       = calldataN (calldataFor n) := rfl
  rw [this, h_calldata]

/-- **Headline theorem.** From `initState n` (with `n ≤ 1000` for the
    gas/PC bounds and `fib (n+1) < 2^256` so the loop's modular
    `UInt256.add` matches `Nat.add`), the program halts in `.Returned`
    with `hReturn` equal to the 32-byte big-endian encoding of
    `ofNat (fib n)`. -/
theorem fib_returns (n : Nat) (h_n : n ≤ 1000)
    (h_fib_size : fib (n + 1) < UInt256.size)
    (h_calldata : calldataN (calldataFor n) = UInt256.ofNat n) :
    ∃ sf : State,
      Steps (initState n) sf ∧
      sf.halt = .Returned ∧
      sf.hReturn = MachineState.readPadded
        (MachineState.writeBytes ByteArray.empty
          (MachineState.wordBytes (UInt256.ofNat (fib n))) 0) 0 32 := by
  set env := (initState n).executionEnv with h_env_def
  have h_code : env.code = code := rfl
  -- Compose `init_value_triple`, `loop_fib_triple`, and `end_block_value_via_opcodes`,
  -- threading `memory = ByteArray.empty` through the whole chain via the
  -- memory-tracking variants.
  obtain ⟨s1, hs1, hf1, hmem1⟩ :=
    init_value_triple n h_n h_calldata (initState n) rfl
  obtain ⟨s2, hs2, hf2, hmem2⟩ :=
    loop_fib_triple n h_n h_fib_size (rest := []) (gas_in := 100000 - 12)
      (m := ByteArray.empty)
      h_code (by omega) s1 ⟨hf1, hmem1⟩
  obtain ⟨sf, hs3, h_halt, h_hReturn⟩ :=
    end_block_value_via_opcodes (env := env)
      (b := UInt256.ofNat (fib (n+1))) (a := UInt256.ofNat (fib n))
      (rest := []) (gas_in := 100000 - 12 - (55 * n + 20)) (memIn := ByteArray.empty)
      h_code (by omega) s2 ⟨hf2, hmem2⟩
  exact ⟨sf, hs1.append (hs2.append hs3), h_halt, h_hReturn⟩

def main : IO Unit := do
  IO.println "FibDemo — iterative Fibonacci in EVM bytecode"
  IO.println s!"  bytecode size: {code.size} bytes"
  for n in [0, 1, 2, 3, 5, 10, 15, 20] do
    let s0 := initState n
    match run s0 100000 with
    | .ok sf =>
      let got      := bytesToNat sf.hReturn
      let expected := fib n
      let mark     := if got = expected then "OK  " else "FAIL"
      IO.println s!"  [{mark}] fib({n}) = {got}  (expected {expected}, \
gas left {sf.gasAvailable}, return size {sf.hReturn.size})"
    | .error e =>
      IO.println s!"  [ERROR] fib({n}): {repr e}"

end FibDemo

def main : IO Unit := FibDemo.main
