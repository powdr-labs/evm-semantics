module

public import EvmSemantics
public import EvmSemantics.Hoare.Block
public meta import EvmSemantics.Hoare.Block
public meta import EvmSemantics.Data.UInt256
public meta import EvmSemantics.EVM.Operation
public meta import EvmSemantics.EVM.Decode

/-!
`BlockFibDemo` — the Fibonacci value-correctness proof against the new
`EvmSemantics.Hoare.Block` framework.
-/

@[expose] public section

open EvmSemantics EvmSemantics.EVM EvmSemantics.Hoare.Block

namespace BlockFibDemo

/-- The Fibonacci bytecode (35 bytes). -/
def code : ByteArray :=
  ⟨#[0x60, 0x04,       -- PUSH1 4              (offset 0)
     0x35,             -- CALLDATALOAD         (offset 2)
     0x60, 0x00,       -- PUSH1 0  (a)         (offset 3)
     0x60, 0x01,       -- PUSH1 1  (b)         (offset 5)
     0x5b,             -- JUMPDEST loop_head   (offset 7)
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

/-- Reference Fibonacci. -/
def fib : Nat → Nat
  | 0     => 0
  | 1     => 1
  | n + 2 => fib (n + 1) + fib n

theorem fib_le_succ (n : Nat) : fib n ≤ fib (n + 1) := by
  match n with
  | 0     => decide
  | 1     => decide
  | m + 2 => show fib (m + 2) ≤ fib (m + 2) + fib (m + 1); omega

theorem fib_le_add (m k : Nat) : fib m ≤ fib (m + k) := by
  induction k with
  | zero => exact Nat.le_refl _
  | succ k' ih =>
    have : m + k' + 1 = m + (k' + 1) := by omega
    exact this ▸ Nat.le_trans ih (fib_le_succ (m + k'))

/-- 36-byte calldata = 4 selector bytes + `n` as a 256-bit big-endian word. -/
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

/-- Initial execution environment. -/
def initEnv (n : Nat) : ExecutionEnv :=
  { address := 0, origin := 0, caller := 0, weiValue := ⟨0⟩
    calldata := calldataFor n, code := code
    gasPrice := ⟨0⟩, header := default, depth := 0
    permitStateMutation := true, blobVersionedHashes := #[]
    fork := .Cancun }

/-- Initial state with `calldataFor n` as calldata. -/
def initState (n : Nat) : State :=
  { toMachineState :=
      { gasAvailable := 100000, activeWords := ⟨0⟩
        memory := .empty, returnData := .empty, hReturn := .empty }
    accountMap   := AccountMap.empty
    substate     := Substate.empty
    executionEnv := initEnv n
    pc := ⟨0⟩, stack := [], execLength := 0, halt := .Running }

partial def run (s : State) (fuel : Nat) : Except ExecutionException State :=
  if fuel = 0 then .error .OutOfFuel else
    if s.isDone then .ok s else
      match stepF s with
      | .ok s'   => run s' (fuel - 1)
      | .error e => .error e

def bytesToNat (bs : ByteArray) : Nat :=
  bs.toList.foldl (fun acc b => acc * 256 + b.toNat) 0

def calldataN (cd : ByteArray) : UInt256 :=
  let bs := MachineState.readPadded cd 4 32
  UInt256.ofNat (Decode.beToNat bs)

----------------------------------------------------------------------------
-- The four blocks as instruction lists.
----------------------------------------------------------------------------

/-- Init block: PUSH1 4 ; CALLDATALOAD ; PUSH1 0 ; PUSH1 1. -/
def init_block : Block :=
  [push1 (UInt256.ofNat 4), calldataload,
   push1 (UInt256.ofNat 0), push1 (UInt256.ofNat 1)]

/-- Loop head block: JUMPDEST ; DUP3 ; ISZERO ; PUSH1 0x19 ; JUMPI. -/
def head_block : Block :=
  [jumpdest, dup ⟨2, by decide⟩, iszero,
   push1 (UInt256.ofNat 0x19), jumpi]

/-- Loop body block: SWAP1 ; DUP2 ; ADD ; SWAP2 ; PUSH1 1 ; SWAP1 ;
    SUB ; SWAP2 ; PUSH1 7 ; JUMP. -/
def body_block : Block :=
  [swap ⟨0, by decide⟩, dup ⟨1, by decide⟩, add, swap ⟨1, by decide⟩,
   push1 (UInt256.ofNat 1), swap ⟨0, by decide⟩, sub, swap ⟨1, by decide⟩,
   push1 (UInt256.ofNat 7), jump]

/-- End block: JUMPDEST ; POP ; PUSH1 0 ; MSTORE ; PUSH1 0x20 ;
    PUSH1 0 ; RETURN. -/
def end_block : Block :=
  [jumpdest, pop, push1 (UInt256.ofNat 0), mstore,
   push1 (UInt256.ofNat 0x20), push1 (UInt256.ofNat 0), retn]

----------------------------------------------------------------------------
-- Block decode witnesses.
----------------------------------------------------------------------------

theorem init_decodes : Block.decodesAt init_block code 0 := by
  unfold init_block Block.decodesAt
  refine ⟨?_, ?_, ?_, ?_, trivial⟩ <;> native_decide

theorem head_decodes : Block.decodesAt head_block code 7 := by
  unfold head_block Block.decodesAt
  refine ⟨?_, ?_, ?_, ?_, ?_, trivial⟩ <;> native_decide

theorem body_decodes : Block.decodesAt body_block code 13 := by
  unfold body_block Block.decodesAt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> native_decide

theorem end_decodes : Block.decodesAt end_block code 25 := by
  unfold end_block Block.decodesAt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> native_decide

theorem valid_jumpdest_25 : Decode.isValidJumpDest code 25 = true := by native_decide
theorem valid_jumpdest_7  : Decode.isValidJumpDest code 7  = true := by native_decide

----------------------------------------------------------------------------
-- Program context (parameterised by `n` — the Fibonacci index).
----------------------------------------------------------------------------

def pctx (n : Nat) : ProgramCtx where
  code := BlockFibDemo.code
  env := initEnv n
  env_code := rfl

/-- Init block context: entry pc 0, 100000 gas, size 7, cost 12. -/
def init_ctx (n : Nat) : BlockCtx (pctx n) where
  pc_init := 0
  gas_init := 100000
  block_size := 7
  block_cost := 12
  no_overflow := by decide
  gas_ok := by decide

/-- Head block context: entry pc 7, 100000 - 12 gas, size 6, cost 20. -/
def head_ctx (n : Nat) (gas_in : Nat) (h : 20 ≤ gas_in) : BlockCtx (pctx n) where
  pc_init := 7
  gas_init := gas_in
  block_size := 6
  block_cost := 20
  no_overflow := by decide
  gas_ok := h

/-- Body block context: entry pc 13, size 12, cost 35. -/
def body_ctx (n : Nat) (gas_in : Nat) (h : 35 ≤ gas_in) : BlockCtx (pctx n) where
  pc_init := 13
  gas_init := gas_in
  block_size := 12
  block_cost := 35
  no_overflow := by decide
  gas_ok := h

/-- End block context: entry pc 25, size 10, cost 18. -/
def end_ctx (n : Nat) (gas_in : Nat) (h : 18 ≤ gas_in) : BlockCtx (pctx n) where
  pc_init := 25
  gas_init := gas_in
  block_size := 10
  block_cost := 18
  no_overflow := by decide
  gas_ok := h

/-- `readWord cd 4 = calldataN cd`. -/
private theorem readWord_4_eq_calldataN (cd : ByteArray) :
    MachineState.readWord cd (UInt256.ofNat 4).toNat = calldataN cd := rfl

----------------------------------------------------------------------------
-- Init block triple: from `initState n`, reach pc 7 with stack [1, 0, n].
----------------------------------------------------------------------------

/-- Init block: from pc 0 / empty stack / 100000 gas, end at pc 7 with
    stack [1, 0, n] and 12 gas spent. -/
theorem init_block_triple (n : Nat)
    (h_calldata : calldataN (calldataFor n) = UInt256.ofNat n) :
    Triple init_block .falls
      (fun s => AtOffset (init_ctx n) 0 0 ByteArray.empty (UInt256.ofNat 0) s ∧ s.stack = [])
      (fun sf => AtOffset (init_ctx n) 7 12 ByteArray.empty (UInt256.ofNat 0) sf ∧
                 sf.stack = [UInt256.ofNat 1, UInt256.ofNat 0, UInt256.ofNat n]) := by
  unfold init_block
  -- Chain the 4 per-opcode triples. The `show` tactic helps Lean see
  -- the block-size/cost bounds reduce through `init_ctx n`.
  have h_size : (init_ctx n).block_size = 7 := rfl
  have h_cost : (init_ctx n).block_cost = 12 := rfl
  have t1 := @push1_triple (pctx n) (init_ctx n) 0 0 (UInt256.ofNat 4)
              (by show 0 + 2 ≤ (init_ctx n).block_size; rw [h_size]; omega)
              (by show 0 + 3 ≤ (init_ctx n).block_cost; rw [h_cost]; omega)
              [] ByteArray.empty (UInt256.ofNat 0)
  have t2 := @calldataload_triple (pctx n) (init_ctx n) 2 3
              (by show 2 + 1 ≤ (init_ctx n).block_size; rw [h_size]; omega)
              (by show 3 + 3 ≤ (init_ctx n).block_cost; rw [h_cost]; omega)
              (UInt256.ofNat 4) [] ByteArray.empty (UInt256.ofNat 0)
  have t3 := @push1_triple (pctx n) (init_ctx n) 3 6 (UInt256.ofNat 0)
              (by show 3 + 2 ≤ (init_ctx n).block_size; rw [h_size]; omega)
              (by show 6 + 3 ≤ (init_ctx n).block_cost; rw [h_cost]; omega)
              [MachineState.readWord (pctx n).env.calldata (UInt256.ofNat 4).toNat]
              ByteArray.empty (UInt256.ofNat 0)
  have t4 := @push1_triple (pctx n) (init_ctx n) 5 9 (UInt256.ofNat 1)
              (by show 5 + 2 ≤ (init_ctx n).block_size; rw [h_size])
              (by show 9 + 3 ≤ (init_ctx n).block_cost; rw [h_cost])
              [UInt256.ofNat 0,
               MachineState.readWord (pctx n).env.calldata (UInt256.ofNat 4).toNat]
              ByteArray.empty (UInt256.ofNat 0)
  -- Compose and weaken final post.
  refine (((t1.seq t2).seq t3).seq t4).imp (fun _ h => h) ?_
  -- Bridge: `readWord (pctx n).env.calldata 4 = UInt256.ofNat n`.
  intro sf ⟨h_at, h_stack⟩
  refine ⟨h_at, ?_⟩
  rw [h_stack]
  show [UInt256.ofNat 1, UInt256.ofNat 0,
        MachineState.readWord (pctx n).env.calldata (UInt256.ofNat 4).toNat] = _
  rw [show (pctx n).env.calldata = calldataFor n from rfl,
      readWord_4_eq_calldataN, h_calldata]

----------------------------------------------------------------------------
-- Head block (taken): when the counter is zero, jump to pc 25.
----------------------------------------------------------------------------

/-- Head block, taken branch (counter `i = 0`): JUMPDEST ; DUP3 ; ISZERO ;
    PUSH1 0x19 ; JUMPI(taken→25). Exits via `.jump 25`. -/
theorem head_block_taken_triple (n : Nat) (gas_in : Nat) (h_gas : 20 ≤ gas_in)
    (b a : UInt256) (rest : List UInt256) (memory : ByteArray) :
    Triple head_block (.jump 25)
      (fun s => AtOffset (head_ctx n gas_in h_gas) 0 0 memory (UInt256.ofNat 0) s ∧
                s.stack = b :: a :: UInt256.ofNat 0 :: rest)
      (fun sf => sf.executionEnv = (pctx n).env ∧
                 sf.memory = memory ∧
                 sf.activeWords = UInt256.ofNat 0 ∧
                 sf.stack = b :: a :: UInt256.ofNat 0 :: rest ∧
                 sf.gasAvailable = gas_in - 20) := by
  unfold head_block
  set hctx := head_ctx n gas_in h_gas with hctx_def
  have h_size : hctx.block_size = 6 := by rw [hctx_def]; rfl
  have h_cost : hctx.block_cost = 20 := by rw [hctx_def]; rfl
  have h_gas_init : hctx.gas_init = gas_in := by rw [hctx_def]; rfl
  have t1 := @jumpdest_triple (pctx n) hctx 0 0
              (by rw [h_size]; try omega) (by rw [h_cost]; try omega)
              (b :: a :: UInt256.ofNat 0 :: rest) memory (UInt256.ofNat 0)
  have t2 := @dup_triple (pctx n) hctx 1 1 ⟨2, by decide⟩ (UInt256.ofNat 0)
              (by rw [h_size]; try omega) (by rw [h_cost]; try omega)
              (b :: a :: UInt256.ofNat 0 :: rest) memory (UInt256.ofNat 0) rfl
  have t3 := @iszero_triple (pctx n) hctx 2 4
              (by rw [h_size]; try omega) (by rw [h_cost]; try omega)
              (UInt256.ofNat 0) (b :: a :: UInt256.ofNat 0 :: rest) memory
              (UInt256.ofNat 0)
  have t4 := @push1_triple (pctx n) hctx 3 7 (UInt256.ofNat 0x19)
              (by rw [h_size]; try omega) (by rw [h_cost]; try omega)
              (UInt256.isZero (UInt256.ofNat 0) :: b :: a :: UInt256.ofNat 0 :: rest)
              memory (UInt256.ofNat 0)
  have t5 := @jumpi_taken_triple (pctx n) hctx 5 10
              (by rw [h_cost])
              (UInt256.ofNat 0x19) (UInt256.isZero (UInt256.ofNat 0))
              (b :: a :: UInt256.ofNat 0 :: rest) memory (UInt256.ofNat 0)
              (by decide) valid_jumpdest_25
  refine ((((t1.seq t2).seq t3).seq t4).seq t5).imp (fun _ h => h) ?_
  -- Adjust the gas value: `gas_in - (10 + 10)` → `gas_in - 20`.
  intro sf ⟨h_env, h_mem, h_active, h_stack, h_g⟩
  refine ⟨h_env, h_mem, h_active, h_stack, ?_⟩
  rw [h_g, h_gas_init]

----------------------------------------------------------------------------
-- Head block (not taken): when the counter is nonzero, fall through to pc 13.
----------------------------------------------------------------------------

/-- Head block, not-taken branch (counter `i = ofNat k`, k > 0). -/
theorem head_block_notTaken_triple (n : Nat) (gas_in : Nat) (h_gas : 20 ≤ gas_in)
    (b a i : UInt256) (rest : List UInt256) (memory : ByteArray)
    (h_i_nz : i.toNat ≠ 0) :
    Triple head_block .falls
      (fun s => AtOffset (head_ctx n gas_in h_gas) 0 0 memory (UInt256.ofNat 0) s ∧
                s.stack = b :: a :: i :: rest)
      (fun sf => AtOffset (head_ctx n gas_in h_gas) 6 20 memory (UInt256.ofNat 0) sf ∧
                 sf.stack = b :: a :: i :: rest) := by
  unfold head_block
  set hctx := head_ctx n gas_in h_gas with hctx_def
  have h_size : hctx.block_size = 6 := by rw [hctx_def]; rfl
  have h_cost : hctx.block_cost = 20 := by rw [hctx_def]; rfl
  have t1 := @jumpdest_triple (pctx n) hctx 0 0
              (by rw [h_size]; try omega) (by rw [h_cost]; try omega)
              (b :: a :: i :: rest) memory (UInt256.ofNat 0)
  have t2 := @dup_triple (pctx n) hctx 1 1 ⟨2, by decide⟩ i
              (by rw [h_size]; try omega) (by rw [h_cost]; try omega)
              (b :: a :: i :: rest) memory (UInt256.ofNat 0) rfl
  have t3 := @iszero_triple (pctx n) hctx 2 4
              (by rw [h_size]; try omega) (by rw [h_cost]; try omega)
              i (b :: a :: i :: rest) memory (UInt256.ofNat 0)
  have t4 := @push1_triple (pctx n) hctx 3 7 (UInt256.ofNat 0x19)
              (by rw [h_size]; try omega) (by rw [h_cost]; try omega)
              (UInt256.isZero i :: b :: a :: i :: rest)
              memory (UInt256.ofNat 0)
  have h_cond_false : ¬ UInt256.isTrue (UInt256.isZero i) := by
    show ¬ ((UInt256.isZero i).toNat ≠ 0)
    push_neg
    show (UInt256.isZero i).toNat = 0
    simp [UInt256.isZero, h_i_nz]; rfl
  have t5 := @jumpi_notTaken_triple (pctx n) hctx 5 10
              (by rw [h_size]; try omega) (by rw [h_cost]; try omega)
              (UInt256.ofNat 0x19) (UInt256.isZero i)
              (b :: a :: i :: rest) memory (UInt256.ofNat 0)
              h_cond_false
  exact ((((t1.seq t2).seq t3).seq t4).seq t5)

----------------------------------------------------------------------------
-- Body block: one loop iteration. Ends in `.jump 7`.
----------------------------------------------------------------------------

/-- Body block: SWAP1 ; DUP2 ; ADD ; SWAP2 ; PUSH1 1 ; SWAP1 ; SUB ;
    SWAP2 ; PUSH1 7 ; JUMP. From stack `[b, a, i, rest]`, end with
    stack `[(b+a), b, (i-1), rest]` at pc 7. -/
theorem body_block_triple (n : Nat) (gas_in : Nat) (h_gas : 35 ≤ gas_in)
    (b a i : UInt256) (rest : List UInt256) (memory : ByteArray) :
    Triple body_block (.jump 7)
      (fun s => AtOffset (body_ctx n gas_in h_gas) 0 0 memory (UInt256.ofNat 0) s ∧
                s.stack = b :: a :: i :: rest)
      (fun sf => sf.executionEnv = (pctx n).env ∧
                 sf.memory = memory ∧
                 sf.activeWords = UInt256.ofNat 0 ∧
                 sf.stack = (b + a) :: b :: (i - UInt256.ofNat 1) :: rest ∧
                 sf.gasAvailable = gas_in - 35) := by
  unfold body_block
  set bctx := body_ctx n gas_in h_gas with bctx_def
  have h_size : bctx.block_size = 12 := by rw [bctx_def]; rfl
  have h_cost : bctx.block_cost = 35 := by rw [bctx_def]; rfl
  have h_gas_init : bctx.gas_init = gas_in := by rw [bctx_def]; rfl
  -- Stack evolution:
  -- (0): [b, a, i, rest]
  -- (1) after SWAP1: [a, b, i, rest]
  -- (2) after DUP2:  [b, a, b, i, rest]
  -- (3) after ADD:   [b+a, b, i, rest]
  -- (4) after SWAP2: [i, b, b+a, rest]
  -- (5) after PUSH1 1: [1, i, b, b+a, rest]
  -- (6) after SWAP1: [i, 1, b, b+a, rest]
  -- (7) after SUB:   [i-1, b, b+a, rest]
  -- (8) after SWAP2: [b+a, b, i-1, rest]
  -- (9) after PUSH1 7: [7, b+a, b, i-1, rest]
  -- (10) after JUMP: [b+a, b, i-1, rest], pc = 7
  have t1 := @swap_triple (pctx n) bctx 0 0 ⟨0, by decide⟩
              (by rw [h_size]; try omega) (by rw [h_cost]; try omega)
              (b :: a :: i :: rest) (a :: b :: i :: rest) memory (UInt256.ofNat 0) rfl
  have t2 := @dup_triple (pctx n) bctx 1 3 ⟨1, by decide⟩ b
              (by rw [h_size]; try omega) (by rw [h_cost]; try omega)
              (a :: b :: i :: rest) memory (UInt256.ofNat 0) rfl
  have t3 := @add_triple (pctx n) bctx 2 6
              (by rw [h_size]; try omega) (by rw [h_cost]; try omega)
              b a (b :: i :: rest) memory (UInt256.ofNat 0)
  have t4 := @swap_triple (pctx n) bctx 3 9 ⟨1, by decide⟩
              (by rw [h_size]; try omega) (by rw [h_cost]; try omega)
              ((b + a) :: b :: i :: rest) (i :: b :: (b + a) :: rest) memory (UInt256.ofNat 0) rfl
  have t5 := @push1_triple (pctx n) bctx 4 12 (UInt256.ofNat 1)
              (by rw [h_size]; try omega) (by rw [h_cost]; try omega)
              (i :: b :: (b + a) :: rest) memory (UInt256.ofNat 0)
  have t6 := @swap_triple (pctx n) bctx 6 15 ⟨0, by decide⟩
              (by rw [h_size]; try omega) (by rw [h_cost]; try omega)
              (UInt256.ofNat 1 :: i :: b :: (b + a) :: rest)
              (i :: UInt256.ofNat 1 :: b :: (b + a) :: rest) memory (UInt256.ofNat 0) rfl
  have t7 := @sub_triple (pctx n) bctx 7 18
              (by rw [h_size]; try omega) (by rw [h_cost]; try omega)
              i (UInt256.ofNat 1) (b :: (b + a) :: rest) memory (UInt256.ofNat 0)
  have t8 := @swap_triple (pctx n) bctx 8 21 ⟨1, by decide⟩
              (by rw [h_size]; try omega) (by rw [h_cost]; try omega)
              ((i - UInt256.ofNat 1) :: b :: (b + a) :: rest)
              ((b + a) :: b :: (i - UInt256.ofNat 1) :: rest) memory (UInt256.ofNat 0) rfl
  have t9 := @push1_triple (pctx n) bctx 9 24 (UInt256.ofNat 7)
              (by rw [h_size]; try omega) (by rw [h_cost]; try omega)
              ((b + a) :: b :: (i - UInt256.ofNat 1) :: rest) memory (UInt256.ofNat 0)
  have t10 := @jump_triple (pctx n) bctx 11 27
              (by rw [h_cost]; try omega)
              (UInt256.ofNat 7) ((b + a) :: b :: (i - UInt256.ofNat 1) :: rest)
              memory (UInt256.ofNat 0) valid_jumpdest_7
  have chain := t1.seq t2 |>.seq t3 |>.seq t4 |>.seq t5 |>.seq t6 |>.seq t7
                  |>.seq t8 |>.seq t9 |>.seq t10
  refine chain.imp (fun _ h => h) ?_
  intro sf ⟨h_env, h_mem, h_active, h_stack, h_g⟩
  refine ⟨h_env, h_mem, h_active, h_stack, ?_⟩
  rw [h_g, h_gas_init]

----------------------------------------------------------------------------
-- End block: JUMPDEST ; POP ; PUSH1 0 ; MSTORE ; PUSH1 0x20 ;
-- PUSH1 0 ; RETURN. Halts with `hReturn = wordBytes a`.
----------------------------------------------------------------------------

/-- End block: from stack `[b, a, 0, rest]`, memory `m_in`, halts with
    `hReturn = readPadded (writeBytes m_in (wordBytes a) 0) 0 32`. -/
theorem end_block_triple (n : Nat) (gas_in : Nat) (h_gas : 18 ≤ gas_in)
    (b a : UInt256) (rest : List UInt256) (memIn : ByteArray) :
    Triple end_block .halted
      (fun s => AtOffset (end_ctx n gas_in h_gas) 0 0 memIn (UInt256.ofNat 0) s ∧
                s.stack = b :: a :: UInt256.ofNat 0 :: rest)
      (fun sf => sf.halt = .Returned ∧
                 sf.hReturn = MachineState.readPadded
                   (MachineState.writeBytes memIn (MachineState.wordBytes a) 0)
                   0 32) := by
  unfold end_block
  set ectx := end_ctx n gas_in h_gas with ectx_def
  have h_size : ectx.block_size = 10 := by rw [ectx_def]; rfl
  have h_cost : ectx.block_cost = 18 := by rw [ectx_def]; rfl
  have t1 := @jumpdest_triple (pctx n) ectx 0 0
              (by rw [h_size]; try omega) (by rw [h_cost]; try omega)
              (b :: a :: UInt256.ofNat 0 :: rest) memIn (UInt256.ofNat 0)
  have t2 := @pop_triple (pctx n) ectx 1 1
              (by rw [h_size]; try omega) (by rw [h_cost]; try omega)
              b (a :: UInt256.ofNat 0 :: rest) memIn (UInt256.ofNat 0)
  have t3 := @push1_triple (pctx n) ectx 2 3 (UInt256.ofNat 0)
              (by rw [h_size]; try omega) (by rw [h_cost]; try omega)
              (a :: UInt256.ofNat 0 :: rest) memIn (UInt256.ofNat 0)
  have t4 := @mstore_triple (pctx n) ectx 4 6
              (by rw [h_size]; try omega) (by rw [h_cost]; try omega)
              a (UInt256.ofNat 0 :: rest) memIn
  have t5 := @push1_triple (pctx n) ectx 5 12 (UInt256.ofNat 0x20)
              (by rw [h_size]; try omega) (by rw [h_cost]; try omega)
              (UInt256.ofNat 0 :: rest)
              (MachineState.writeBytes memIn (MachineState.wordBytes a) 0)
              (UInt256.ofNat 1)
  have t6 := @push1_triple (pctx n) ectx 7 15 (UInt256.ofNat 0)
              (by rw [h_size]; try omega) (by rw [h_cost]; try omega)
              (UInt256.ofNat 0x20 :: UInt256.ofNat 0 :: rest)
              (MachineState.writeBytes memIn (MachineState.wordBytes a) 0)
              (UInt256.ofNat 1)
  have t7 := @return_triple (pctx n) ectx 9 18 (UInt256.ofNat 0 :: rest)
              (MachineState.writeBytes memIn (MachineState.wordBytes a) 0)
  exact (((((t1.seq t2).seq t3).seq t4).seq t5).seq t6).seq t7

----------------------------------------------------------------------------
-- Loop induction
----------------------------------------------------------------------------

/-- Loop invariant: starting at pc 7 with `[fib(j+1), fib(j), k]`, after
    `k` iterations end at pc 25 with `[fib(j+k+1), fib(j+k), 0]`.
    Proven by induction on `k`. -/
theorem loop_total (n : Nat) (j k : Nat)
    (h_size : j + k + 1 < UInt256.size)
    (h_fib_size : fib (j + k + 1) < UInt256.size) :
    ∀ (gas_in : Nat) (h_gas : 55 * k + 20 ≤ gas_in) (memory : ByteArray)
      (rest : List UInt256) (s : State),
        s.executionEnv = (pctx n).env →
        s.pc.toNat = 7 →
        s.halt = .Running →
        s.callStack = [] →
        s.stack = UInt256.ofNat (fib (j+1)) :: UInt256.ofNat (fib j) ::
                  UInt256.ofNat k :: rest →
        s.gasAvailable = gas_in →
        s.memory = memory →
        s.activeWords = UInt256.ofNat 0 →
      ∃ sf, Steps s sf ∧
        sf.executionEnv = (pctx n).env ∧
        sf.pc.toNat = 25 ∧
        sf.halt = .Running ∧
        sf.callStack = [] ∧
        sf.stack = UInt256.ofNat (fib (j+k+1)) :: UInt256.ofNat (fib (j+k)) ::
                  UInt256.ofNat 0 :: rest ∧
        sf.gasAvailable = gas_in - (55 * k + 20) ∧
        sf.memory = memory ∧
        sf.activeWords = UInt256.ofNat 0 := by
  induction k generalizing j with
  | zero =>
    intro gas_in h_gas memory rest s h_env h_pc h_halt h_cs h_stack h_g h_mem h_active
    have h_gas_le : 20 ≤ gas_in := by omega
    have h_dec : Block.decodesAt head_block s.executionEnv.code s.pc.toNat := by
      rw [h_env, h_pc]; exact head_decodes
    have h_at : AtOffset (head_ctx n gas_in h_gas_le) 0 0 memory (UInt256.ofNat 0) s := by
      refine ⟨?_, h_g, h_env, h_mem, h_active, Nat.zero_le _, Nat.zero_le _⟩
      show s.pc.toNat = (head_ctx n gas_in h_gas_le).pc_init + 0
      rw [h_pc]; rfl
    obtain ⟨sf, hs, h_env_f, h_cs_f, ⟨h_env_q, h_mem_q, h_active_q, h_stack_q, h_g_q⟩,
            h_pc_f, h_halt_f⟩ :=
      head_block_taken_triple n gas_in h_gas_le
        (UInt256.ofNat (fib (j+1))) (UInt256.ofNat (fib j)) rest memory
        s h_dec h_halt h_cs ⟨h_at, h_stack⟩
    refine ⟨sf, hs, h_env_q, h_pc_f, h_halt_f, ?_, h_stack_q, ?_, h_mem_q, h_active_q⟩
    · rw [h_cs_f, h_cs]
    · exact h_g_q
  | succ k' ih =>
    intro gas_in h_gas memory rest s h_env h_pc h_halt h_cs h_stack h_g h_mem h_active
    -- Step 1: head_block_notTaken (i ≠ 0).
    have h_gas_le : 20 ≤ gas_in := by omega
    have h_dec1 : Block.decodesAt head_block s.executionEnv.code s.pc.toNat := by
      rw [h_env, h_pc]; exact head_decodes
    have h_at1 : AtOffset (head_ctx n gas_in h_gas_le) 0 0 memory (UInt256.ofNat 0) s := by
      refine ⟨?_, h_g, h_env, h_mem, h_active, Nat.zero_le _, Nat.zero_le _⟩
      show s.pc.toNat = (head_ctx n gas_in h_gas_le).pc_init + 0
      rw [h_pc]; rfl
    have h_k1_size : k' + 1 < UInt256.size := by omega
    have h_i_toNat : (UInt256.ofNat (k' + 1)).toNat = k' + 1 :=
      ofNat_toNat _ h_k1_size
    have h_i_nz : (UInt256.ofNat (k' + 1)).toNat ≠ 0 := by rw [h_i_toNat]; omega
    obtain ⟨s1, hs1, h_env1, h_cs1, ⟨h_at_q, h_stack1⟩, h_pc1, h_halt1⟩ :=
      head_block_notTaken_triple n gas_in h_gas_le
        (UInt256.ofNat (fib (j+1))) (UInt256.ofNat (fib j))
        (UInt256.ofNat (k' + 1)) rest memory h_i_nz
        s h_dec1 h_halt h_cs ⟨h_at1, h_stack⟩
    -- Extract s1 invariants from AtOffset.
    obtain ⟨h_pc1', h_g1, h_env1', h_mem1, h_active1, _, _⟩ := h_at_q
    have h_s1_pc : s1.pc.toNat = 13 := by
      rw [h_pc1']; show (head_ctx n gas_in h_gas_le).pc_init + 6 = 13; rfl
    -- Step 2: body_block.
    have h_gas2 : 35 ≤ s1.gasAvailable := by
      rw [h_g1]; show 35 ≤ (head_ctx n gas_in h_gas_le).gas_init - 20
      show 35 ≤ gas_in - 20; omega
    have h_dec2 : Block.decodesAt body_block s1.executionEnv.code s1.pc.toNat := by
      rw [h_env1', h_s1_pc]; exact body_decodes
    have h_at2 : AtOffset (body_ctx n s1.gasAvailable h_gas2) 0 0 memory
                  (UInt256.ofNat 0) s1 := by
      refine ⟨?_, rfl, h_env1', h_mem1, h_active1, Nat.zero_le _, Nat.zero_le _⟩
      show s1.pc.toNat = (body_ctx n s1.gasAvailable h_gas2).pc_init + 0
      rw [h_s1_pc]; rfl
    have h_cs1' : s1.callStack = [] := h_cs1.trans h_cs
    obtain ⟨s2, hs2, h_env2, h_cs2, ⟨h_env2', h_mem2, h_active2, h_stack2, h_g2⟩,
            h_pc2, h_halt2⟩ :=
      body_block_triple n s1.gasAvailable h_gas2
        (UInt256.ofNat (fib (j+1))) (UInt256.ofNat (fib j))
        (UInt256.ofNat (k' + 1)) rest memory
        s1 h_dec2 h_halt1 h_cs1' ⟨h_at2, h_stack1⟩
    -- Step 3: Apply IH at (j+1, k').
    -- Bridges: fib(j+2) = fib(j+1) + fib(j) (no overflow); ofNat(k+1) - 1 = ofNat k.
    have h_fib_size_ih : fib ((j + 1) + k' + 1) < UInt256.size := by
      have : (j + 1) + k' + 1 = j + (k' + 1) + 1 := by omega
      rw [this]; exact h_fib_size
    have h_size_ih : (j + 1) + k' + 1 < UInt256.size := by omega
    have h_fib_sum_size : fib (j+1) + fib j < UInt256.size := by
      have : fib (j+2) = fib (j+1) + fib j := by simp [fib, Nat.add_comm]
      have h_mono : fib (j+2) ≤ fib (j + (k'+1) + 1) := by
        have : j + (k' + 1) + 1 = (j + 2) + k' := by omega
        rw [this]; exact fib_le_add (j+2) k'
      omega
    have h_add_eq : UInt256.ofNat (fib (j+1)) + UInt256.ofNat (fib j) =
                    UInt256.ofNat (fib (j+2)) := by
      rw [ofNat_add _ _ h_fib_sum_size]
      have : fib (j+2) = fib (j+1) + fib j := by simp [fib, Nat.add_comm]
      rw [this]
    have h_sub_eq : UInt256.ofNat (k' + 1) - UInt256.ofNat 1 = UInt256.ofNat k' :=
      ofNat_sub_one k' (by omega)
    have h_stack2' : s2.stack = UInt256.ofNat (fib ((j+1)+1)) :: UInt256.ofNat (fib (j+1)) ::
                    UInt256.ofNat k' :: rest := by
      rw [h_stack2, h_add_eq, h_sub_eq]
    have h_g1' : s1.gasAvailable = gas_in - 20 := by
      rw [h_g1]; show gas_in - 20 = gas_in - 20; rfl
    have h_g2' : s2.gasAvailable = (gas_in - 55) := by
      rw [h_g2, h_g1']; omega
    have h_gas_ih : 55 * k' + 20 ≤ s2.gasAvailable := by
      rw [h_g2']; omega
    have h_s2_pc : s2.pc.toNat = 7 := h_pc2
    have h_s2_env : s2.executionEnv = (pctx n).env := h_env2'
    have h_s2_halt : s2.halt = .Running := h_halt2
    have h_cs2' : s2.callStack = [] := h_cs2.trans h_cs1'
    obtain ⟨sf, hsf, h_env_f, h_pc_f, h_halt_f, h_cs_f, h_stack_f,
            h_g_f, h_mem_f, h_active_f⟩ :=
      ih (j+1) h_size_ih h_fib_size_ih s2.gasAvailable h_gas_ih memory rest
        s2 h_s2_env h_s2_pc h_s2_halt h_cs2' h_stack2' rfl h_mem2 h_active2
    refine ⟨sf, ?_, h_env_f, h_pc_f, h_halt_f, h_cs_f, ?_, ?_, h_mem_f, h_active_f⟩
    · exact (hs1.append hs2).append hsf
    · rw [h_stack_f]
      have : (j + 1) + k' + 1 = j + (k' + 1) + 1 := by omega
      rw [this]
      have h2 : (j + 1) + k' = j + (k' + 1) := by omega
      rw [h2]
    · rw [h_g_f, h_g2']; omega

----------------------------------------------------------------------------
-- Headline: fib_returns
----------------------------------------------------------------------------

/-- **Headline theorem.** From `initState n`, the chain reaches a state
    with `halt = .Returned` and `hReturn = readPadded (writeBytes empty
    (wordBytes (ofNat (fib n))) 0) 0 32`. Composes init_block,
    loop_total, and end_block at the Steps level. -/
theorem fib_returns (n : Nat) (h_n : n ≤ 1000)
    (h_fib_size : fib (n + 1) < UInt256.size)
    (h_calldata : calldataN (calldataFor n) = UInt256.ofNat n)
    (h_gas : 55 * n + 50 ≤ 100000) :
    ∃ sf : State,
      Steps (initState n) sf ∧
      sf.halt = .Returned ∧
      sf.hReturn = MachineState.readPadded
        (MachineState.writeBytes ByteArray.empty
          (MachineState.wordBytes (UInt256.ofNat (fib n))) 0) 0 32 := by
  set s0 := initState n
  -- Step 1: Apply init_block_triple.
  have h_dec0 : Block.decodesAt init_block s0.executionEnv.code s0.pc.toNat := by
    show Block.decodesAt init_block code 0; exact init_decodes
  have h_halt0 : s0.halt = .Running := rfl
  have h_cs0 : s0.callStack = [] := rfl
  have h_at0 : AtOffset (init_ctx n) 0 0 ByteArray.empty (UInt256.ofNat 0) s0 := by
    refine ⟨?_, rfl, rfl, rfl, rfl, Nat.zero_le _, Nat.zero_le _⟩
    show (0 : Nat) = 0; rfl
  have h_stack0 : s0.stack = [] := rfl
  obtain ⟨s1, hs1, h_env1, h_cs1, ⟨h_at1, h_stack1⟩, h_pc1, h_halt1⟩ :=
    init_block_triple n h_calldata s0 h_dec0 h_halt0 h_cs0 ⟨h_at0, h_stack0⟩
  obtain ⟨h_pc1', h_g1, h_env1', h_mem1, h_active1, _, _⟩ := h_at1
  have h_s1_pc : s1.pc.toNat = 7 := by
    rw [h_pc1']; show (init_ctx n).pc_init + 7 = 7; rfl
  have h_s1_g : s1.gasAvailable = 100000 - 12 := by
    rw [h_g1]; rfl
  -- Step 2: Apply loop_total at (j=0, k=n).
  have h_n_lt : n + 1 < UInt256.size := by
    show n + 1 < 2^256; omega
  have h_size0 : 0 + n + 1 < UInt256.size := by omega
  have h_fib_size0 : fib (0 + n + 1) < UInt256.size := by
    have h_eq : 0 + n + 1 = n + 1 := by omega
    rw [h_eq]; exact h_fib_size
  have h_gas_loop : 55 * n + 20 ≤ s1.gasAvailable := by
    rw [h_s1_g]; omega
  have h_stack1' : s1.stack = UInt256.ofNat (fib (0+1)) ::
                  UInt256.ofNat (fib 0) :: UInt256.ofNat n :: [] := by
    rw [h_stack1]; rfl
  obtain ⟨s2, hs2, h_env2, h_pc2, h_halt2, h_cs2, h_stack2,
          h_g2, h_mem2, h_active2⟩ :=
    loop_total n 0 n h_size0 h_fib_size0 s1.gasAvailable h_gas_loop ByteArray.empty []
      s1 h_env1' h_s1_pc h_halt1 (h_cs1.trans h_cs0) h_stack1' rfl h_mem1 h_active1
  have h_s2_g : s2.gasAvailable = 100000 - 12 - (55 * n + 20) := by
    rw [h_g2, h_s1_g]
  -- Step 3: Apply end_block_triple.
  have h_g_end : 18 ≤ s2.gasAvailable := by rw [h_s2_g]; omega
  have h_dec_end : Block.decodesAt end_block s2.executionEnv.code s2.pc.toNat := by
    rw [h_env2, h_pc2]; exact end_decodes
  have h_at_end : AtOffset (end_ctx n s2.gasAvailable h_g_end) 0 0 ByteArray.empty
                    (UInt256.ofNat 0) s2 := by
    refine ⟨?_, rfl, h_env2, h_mem2, h_active2, Nat.zero_le _, Nat.zero_le _⟩
    show s2.pc.toNat = (end_ctx n s2.gasAvailable h_g_end).pc_init + 0
    rw [h_pc2]; rfl
  have h_stack_end : s2.stack = UInt256.ofNat (fib (0+n+1)) ::
                      UInt256.ofNat (fib (0+n)) :: UInt256.ofNat 0 :: [] := h_stack2
  -- Reshape s2.stack to end_block's expected form: b :: a :: ofNat 0 :: rest
  have h_stack_end' : s2.stack = UInt256.ofNat (fib (n+1)) ::
                       UInt256.ofNat (fib n) :: UInt256.ofNat 0 :: [] := by
    rw [h_stack_end]
    have h_eq1 : 0 + n + 1 = n + 1 := by omega
    have h_eq2 : 0 + n = n := by omega
    rw [h_eq1, h_eq2]
  obtain ⟨s3, hs3, h_env3, h_cs3, ⟨h_halt3, h_hReturn3⟩, h_exit3⟩ :=
    end_block_triple n s2.gasAvailable h_g_end
      (UInt256.ofNat (fib (n+1))) (UInt256.ofNat (fib n)) [] ByteArray.empty
      s2 h_dec_end h_halt2 h_cs2 ⟨h_at_end, h_stack_end'⟩
  refine ⟨s3, ?_, h_halt3, ?_⟩
  · exact (hs1.append hs2).append hs3
  · rw [h_hReturn3]

end BlockFibDemo

def main : IO Unit := pure ()
