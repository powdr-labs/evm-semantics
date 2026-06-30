module

public import EvmSemantics

/-!
# `Hoare.Block` — block-list Hoare-triple framework for EVM bytecode.

## Design

A *block* is a `List Insn` — a sequence of decoded EVM instructions
with known byte widths. A `Triple b ex P Q` says: starting at any
state where `b` decodes at `s.pc`, satisfying `P`, the chain reaches
some `sf` with `Q sf`, exiting via `ex` (fall through, jump to label,
or halt).

State invariants threaded into the Triple:
- `executionEnv` is preserved (per the underlying StepRunning rules).
- `callStack` is preserved (Fibonacci has no CALL/CREATE).
- `pc`, `gas`, `memory` evolve in a *known* way, tracked via `AtOffset`
  parameterised over a `BlockCtx` (and `ProgramCtx` for env-pinning).

The key invention is `ProgramCtx`: pinning `executionEnv` to a single
value across the whole proof. With this, opcode triples that read from
`env.calldata` (CALLDATALOAD) reference *concrete* values in their
posts, so composition unifies syntactically without env-bridging via
`Triple.imp_with_pre`.
-/

@[expose] public section

set_option linter.dupNamespace false

open EvmSemantics EvmSemantics.EVM

namespace EvmSemantics
namespace Hoare
namespace Block

----------------------------------------------------------------------------
-- Instruction representation
----------------------------------------------------------------------------

/-- A decoded EVM instruction with its byte width. -/
structure Insn where
  op    : Operation
  imm   : Option (UInt256 × Nat)
  width : Nat
  deriving Repr

/-- A block is a list of instructions. -/
abbrev Block := List Insn

/-- Total byte width of a block. -/
def Block.size : Block → Nat
  | []        => 0
  | i :: rest => i.width + Block.size rest

/-- "The bytecode `code` decodes to this block starting at `pc`." -/
def Block.decodesAt : Block → ByteArray → Nat → Prop
  | [],          _,    _  => True
  | i :: rest,   code, pc => Decode.decodeAt code pc = some (i.op, i.imm)
                          ∧ Block.decodesAt rest code (pc + i.width)

theorem Block.size_append : ∀ (b₁ b₂ : Block),
    Block.size (b₁ ++ b₂) = b₁.size + b₂.size
  | [],       _   => by simp [Block.size]
  | i :: rest, b₂ => by
    show i.width + Block.size (rest ++ b₂) = (i.width + Block.size rest) + Block.size b₂
    rw [Block.size_append rest b₂]; omega

theorem Block.decodesAt_append :
    ∀ (b₁ b₂ : Block) (code : ByteArray) (pc : Nat),
      Block.decodesAt (b₁ ++ b₂) code pc ↔
      Block.decodesAt b₁ code pc ∧ Block.decodesAt b₂ code (pc + b₁.size)
  | [],       _, _,    _  => by simp [Block.decodesAt, Block.size]
  | i :: rest, b₂, code, pc => by
    simp only [List.cons_append, Block.decodesAt]
    constructor
    · rintro ⟨h_head, h_rest⟩
      have ⟨ih1, ih2⟩ := (Block.decodesAt_append rest b₂ code (pc + i.width)).mp h_rest
      refine ⟨⟨h_head, ih1⟩, ?_⟩
      have h_eq : pc + i.width + Block.size rest = pc + (i.width + Block.size rest) := by omega
      rw [h_eq] at ih2; exact ih2
    · rintro ⟨⟨h_head, h1⟩, h2⟩
      refine ⟨h_head, (Block.decodesAt_append rest b₂ code (pc + i.width)).mpr ?_⟩
      refine ⟨h1, ?_⟩
      have h_eq : pc + i.width + Block.size rest = pc + (i.width + Block.size rest) := by omega
      rw [h_eq]; exact h2

----------------------------------------------------------------------------
-- Program and block contexts
----------------------------------------------------------------------------

/-- Program-wide context: the bytecode + the execution environment. -/
structure ProgramCtx where
  code     : ByteArray
  env      : ExecutionEnv
  env_code : env.code = code

/-- Per-block envelope: where it starts, how much gas, how big, how
    much it costs. Parameterised over a `ProgramCtx`. -/
structure BlockCtx (pctx : ProgramCtx) where
  pc_init     : Nat
  gas_init    : Nat
  block_size  : Nat
  block_cost  : Nat
  no_overflow : pc_init + block_size < UInt256.size
  gas_ok      : block_cost ≤ gas_init

/-- "State `s` is at offset `(pc_off, gas_off)` within block `ctx`,
    with current memory `memory` and active-words count `active`":
    every relevant component pinned. -/
def AtOffset {pctx : ProgramCtx} (ctx : BlockCtx pctx)
    (pc_off gas_off : Nat) (memory : ByteArray) (active : UInt256)
    (s : State) : Prop :=
  s.pc.toNat = ctx.pc_init + pc_off ∧
  s.gasAvailable = ctx.gas_init - gas_off ∧
  s.executionEnv = pctx.env ∧
  s.memory = memory ∧
  s.activeWords = active ∧
  pc_off ≤ ctx.block_size ∧
  gas_off ≤ ctx.block_cost

----------------------------------------------------------------------------
-- Exit kinds and Triple
----------------------------------------------------------------------------

inductive Exit where
  | falls
  | jump (label : Nat)
  | halted
  deriving Repr

/-- Position-independent Hoare triple. -/
def Triple (b : Block) (ex : Exit) (P Q : State → Prop) : Prop :=
  ∀ s, Block.decodesAt b s.executionEnv.code s.pc.toNat →
       s.halt = .Running →
       s.callStack = [] →
       P s →
    ∃ sf, Steps s sf ∧
      sf.executionEnv = s.executionEnv ∧
      sf.callStack = s.callStack ∧
      Q sf ∧
      (match ex with
       | .falls       => sf.pc.toNat = s.pc.toNat + b.size ∧ sf.halt = .Running
       | .jump label  => sf.pc.toNat = label ∧ sf.halt = .Running
       | .halted      => sf.halt ≠ .Running)

/-- Sequencing: `.falls`-block + any-block. -/
theorem Triple.seq {b₁ b₂ : Block} {ex : Exit} {P Q R : State → Prop}
    (h1 : Triple b₁ .falls P Q) (h2 : Triple b₂ ex Q R) :
    Triple (b₁ ++ b₂) ex P R := by
  intro s h_dec h_halt h_cs hp
  obtain ⟨h_dec1, h_dec2⟩ := (Block.decodesAt_append b₁ b₂ _ _).mp h_dec
  obtain ⟨s1, hs1, h_env1, h_cs1, hq, h_pc1, h_halt1⟩ := h1 s h_dec1 h_halt h_cs hp
  have h_dec2' : Block.decodesAt b₂ s1.executionEnv.code s1.pc.toNat := by
    rw [h_env1, h_pc1]; exact h_dec2
  have h_cs1' : s1.callStack = [] := h_cs1.trans h_cs
  obtain ⟨sf, hs2, h_env2, h_cs2, hr, h_exit⟩ := h2 s1 h_dec2' h_halt1 h_cs1' hq
  refine ⟨sf, hs1.append hs2, h_env2.trans h_env1, h_cs2.trans h_cs1, hr, ?_⟩
  cases ex with
  | falls =>
    obtain ⟨h_pc2, h_halt2⟩ := h_exit
    refine ⟨?_, h_halt2⟩
    rw [h_pc2, h_pc1, Block.size_append]; omega
  | jump label   => exact h_exit
  | halted       => exact h_exit

/-- Weaken pre / strengthen post. -/
theorem Triple.imp {b : Block} {ex : Exit} {P P' Q Q' : State → Prop}
    (h_p : ∀ s, P' s → P s) (h_q : ∀ s, Q s → Q' s) (h : Triple b ex P Q) :
    Triple b ex P' Q' := by
  intro s h_dec h_halt h_cs hp
  obtain ⟨sf, hs, h_env, h_cs', hq, h_exit⟩ := h s h_dec h_halt h_cs (h_p _ hp)
  exact ⟨sf, hs, h_env, h_cs', h_q _ hq, h_exit⟩

----------------------------------------------------------------------------
-- UInt256 arithmetic helpers
----------------------------------------------------------------------------

theorem pc_add (a : UInt256) (n : Nat) (h : a.toNat + n < UInt256.size) :
    (a + UInt256.ofNat n).toNat = a.toNat + n := by
  show (UInt256.add a (UInt256.ofNat n)).val.val = a.toNat + n
  unfold UInt256.add UInt256.ofNat UInt256.toNat at *
  simp [Fin.add_def, Nat.mod_eq_of_lt h]

theorem ofNat_toNat (k : Nat) (h : k < UInt256.size) :
    (UInt256.ofNat k).toNat = k := by
  show (Fin.ofNat UInt256.size k).val = k
  exact Nat.mod_eq_of_lt h

theorem uint256_eq_of_toNat (i j : UInt256) (h : i.toNat = j.toNat) : i = j := by
  cases i; cases j; congr 1; exact Fin.ext h

theorem ofNat_add (a b : Nat) (h : a + b < UInt256.size) :
    UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) := by
  apply uint256_eq_of_toNat
  rw [ofNat_toNat _ h]
  have := pc_add (UInt256.ofNat a) b (by rw [ofNat_toNat a (by omega)]; omega)
  rw [this, ofNat_toNat a (by omega)]

theorem ofNat_sub_one (k : Nat) (h : k + 1 < UInt256.size) :
    UInt256.ofNat (k + 1) - UInt256.ofNat 1 = UInt256.ofNat k := by
  apply uint256_eq_of_toNat
  rw [ofNat_toNat k (by omega)]
  show (UInt256.sub (UInt256.ofNat (k+1)) (UInt256.ofNat 1)).toNat = k
  unfold UInt256.toNat UInt256.sub
  have e1 : (UInt256.ofNat (k+1)).val.val = k + 1 := ofNat_toNat (k+1) h
  have e2 : (UInt256.ofNat 1).val.val = 1 := ofNat_toNat 1 (by decide)
  show ((UInt256.ofNat (k+1)).val - (UInt256.ofNat 1).val).val = k
  simp only [Fin.sub_def, e1, e2]
  have : (UInt256.size - 1) + (k + 1) = UInt256.size + k := by
    have : 1 ≤ UInt256.size := by decide
    omega
  rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : k < UInt256.size)]

----------------------------------------------------------------------------
-- Per-opcode triples (all 13 needed for Fibonacci).
----------------------------------------------------------------------------

/-- Helper: from `Block.decodesAt [insn]`, derive the `decoded` /
    `decodedOp` projection on `s` when `s.executionEnv = pctx.env`. -/
private theorem decoded_of_block {pctx : ProgramCtx} {s : State} {insn : Insn}
    (h_env : s.executionEnv = pctx.env)
    (h_dec : Block.decodesAt [insn] s.executionEnv.code s.pc.toNat) :
    s.decoded = some (insn.op, insn.imm) := by
  obtain ⟨h_d, _⟩ := h_dec
  show Decode.decodeAt s.executionEnv.code s.pc.toNat = _
  exact h_d

private theorem decodedOp_of_block {pctx : ProgramCtx} {s : State} {insn : Insn}
    (h_env : s.executionEnv = pctx.env)
    (h_dec : Block.decodesAt [insn] s.executionEnv.code s.pc.toNat) :
    s.decodedOp = some insn.op := by
  unfold State.decodedOp
  rw [decoded_of_block h_env h_dec]; rfl

----------------------------------------------------------------------------
-- PUSH1
----------------------------------------------------------------------------

def push1 (data : UInt256) : Insn := ⟨.Push ⟨1, by decide⟩, some (data, 1), 2⟩

theorem push1_triple {pctx : ProgramCtx} (ctx : BlockCtx pctx)
    (pc_off gas_off : Nat) (data : UInt256)
    (h_pc_room  : pc_off + 2 ≤ ctx.block_size)
    (h_gas_room : gas_off + 3 ≤ ctx.block_cost)
    {rest : List UInt256} {memory : ByteArray} {active : UInt256} :
    Triple [push1 data] .falls
      (fun s => AtOffset ctx pc_off gas_off memory active s ∧ s.stack = rest)
      (fun sf => AtOffset ctx (pc_off + 2) (gas_off + 3) memory active sf ∧
                 sf.stack = data :: rest) := by
  intro s h_dec h_halt _h_cs ⟨⟨h_pc, h_g, h_env, h_mem, h_active, _, _⟩, h_stack⟩
  have h_op := decoded_of_block h_env h_dec
  have h_pcb : s.pc.toNat + 2 < UInt256.size := by
    rw [h_pc]; have := ctx.no_overflow; omega
  have h_gas_bd : Gas.baseCost s.fork (.Push ⟨1, by decide⟩) ≤ s.gasAvailable := by
    show 3 ≤ _; rw [h_g]; have := ctx.gas_ok; omega
  refine ⟨_, Steps.refl s |>.snoc (Step.running h_halt
    (StepRunning.pushN s ⟨1, by decide⟩ data 1 (by decide) h_op h_gas_bd)),
    rfl, rfl, ?_, ?_, h_halt⟩
  · refine ⟨⟨?_, ?_, h_env, h_mem, h_active, h_pc_room, h_gas_room⟩, ?_⟩ <;> dsimp only
    · show (s.pc + UInt256.ofNat 2).toNat = ctx.pc_init + pc_off + 2
      rw [pc_add _ _ h_pcb, h_pc]
    · show s.gasAvailable - 3 = ctx.gas_init - (gas_off + 3)
      rw [h_g]; have := ctx.gas_ok; omega
    · show data :: s.stack = data :: rest; rw [h_stack]
  · show (s.pc + UInt256.ofNat 2).toNat = s.pc.toNat + Block.size [push1 data]
    rw [pc_add _ _ h_pcb]; rfl

----------------------------------------------------------------------------
-- JUMPDEST
----------------------------------------------------------------------------

def jumpdest : Insn := ⟨.JUMPDEST, none, 1⟩

theorem jumpdest_triple {pctx : ProgramCtx} (ctx : BlockCtx pctx)
    (pc_off gas_off : Nat)
    (h_pc_room  : pc_off + 1 ≤ ctx.block_size)
    (h_gas_room : gas_off + 1 ≤ ctx.block_cost)
    {stack : List UInt256} {memory : ByteArray} {active : UInt256} :
    Triple [jumpdest] .falls
      (fun s => AtOffset ctx pc_off gas_off memory active s ∧ s.stack = stack)
      (fun sf => AtOffset ctx (pc_off + 1) (gas_off + 1) memory active sf ∧
                 sf.stack = stack) := by
  intro s h_dec h_halt _h_cs ⟨⟨h_pc, h_g, h_env, h_mem, h_active, _, _⟩, h_stack⟩
  have h_op := decodedOp_of_block h_env h_dec
  have h_pcb : s.pc.toNat + 1 < UInt256.size := by
    rw [h_pc]; have := ctx.no_overflow; omega
  have h_gas_bd : Gas.baseCost s.fork .JUMPDEST ≤ s.gasAvailable := by
    show 1 ≤ _; rw [h_g]; have := ctx.gas_ok; omega
  refine ⟨_, Steps.refl s |>.snoc (Step.running h_halt
    (StepRunning.jumpdest s h_op h_gas_bd)),
    rfl, rfl, ?_, ?_, h_halt⟩
  · refine ⟨⟨?_, ?_, h_env, h_mem, h_active, h_pc_room, h_gas_room⟩, ?_⟩ <;> dsimp only
    · show (s.pc + UInt256.ofNat 1).toNat = ctx.pc_init + pc_off + 1
      rw [pc_add _ _ h_pcb, h_pc]
    · show s.gasAvailable - 1 = ctx.gas_init - (gas_off + 1)
      rw [h_g]; have := ctx.gas_ok; omega
    · exact h_stack
  · show (s.pc + UInt256.ofNat 1).toNat = s.pc.toNat + Block.size [jumpdest]
    rw [pc_add _ _ h_pcb]; rfl

----------------------------------------------------------------------------
-- POP
----------------------------------------------------------------------------

def pop : Insn := ⟨.POP, none, 1⟩

theorem pop_triple {pctx : ProgramCtx} (ctx : BlockCtx pctx)
    (pc_off gas_off : Nat)
    (h_pc_room  : pc_off + 1 ≤ ctx.block_size)
    (h_gas_room : gas_off + 2 ≤ ctx.block_cost)
    {a : UInt256} {rest : List UInt256} {memory : ByteArray} {active : UInt256} :
    Triple [pop] .falls
      (fun s => AtOffset ctx pc_off gas_off memory active s ∧ s.stack = a :: rest)
      (fun sf => AtOffset ctx (pc_off + 1) (gas_off + 2) memory active sf ∧
                 sf.stack = rest) := by
  intro s h_dec h_halt _h_cs ⟨⟨h_pc, h_g, h_env, h_mem, h_active, _, _⟩, h_stack⟩
  have h_op := decodedOp_of_block h_env h_dec
  have h_pcb : s.pc.toNat + 1 < UInt256.size := by
    rw [h_pc]; have := ctx.no_overflow; omega
  have h_gas_bd : Gas.baseCost s.fork .POP ≤ s.gasAvailable := by
    show 2 ≤ _; rw [h_g]; have := ctx.gas_ok; omega
  refine ⟨_, Steps.refl s |>.snoc (Step.running h_halt
    (StepRunning.pop s a rest h_op h_gas_bd h_stack)),
    rfl, rfl, ?_, ?_, h_halt⟩
  · refine ⟨⟨?_, ?_, h_env, h_mem, h_active, h_pc_room, h_gas_room⟩, ?_⟩ <;> dsimp only
    · show (s.pc + UInt256.ofNat 1).toNat = ctx.pc_init + pc_off + 1
      rw [pc_add _ _ h_pcb, h_pc]
    · show s.gasAvailable - 2 = ctx.gas_init - (gas_off + 2)
      rw [h_g]; have := ctx.gas_ok; omega
  · show (s.pc + UInt256.ofNat 1).toNat = s.pc.toNat + Block.size [pop]
    rw [pc_add _ _ h_pcb]; rfl

----------------------------------------------------------------------------
-- ADD
----------------------------------------------------------------------------

def add : Insn := ⟨.ADD, none, 1⟩

theorem add_triple {pctx : ProgramCtx} (ctx : BlockCtx pctx)
    (pc_off gas_off : Nat)
    (h_pc_room  : pc_off + 1 ≤ ctx.block_size)
    (h_gas_room : gas_off + 3 ≤ ctx.block_cost)
    {a b : UInt256} {rest : List UInt256} {memory : ByteArray} {active : UInt256} :
    Triple [add] .falls
      (fun s => AtOffset ctx pc_off gas_off memory active s ∧ s.stack = a :: b :: rest)
      (fun sf => AtOffset ctx (pc_off + 1) (gas_off + 3) memory active sf ∧
                 sf.stack = (a + b) :: rest) := by
  intro s h_dec h_halt _h_cs ⟨⟨h_pc, h_g, h_env, h_mem, h_active, _, _⟩, h_stack⟩
  have h_op := decodedOp_of_block h_env h_dec
  have h_pcb : s.pc.toNat + 1 < UInt256.size := by
    rw [h_pc]; have := ctx.no_overflow; omega
  have h_gas_bd : Gas.baseCost s.fork .ADD ≤ s.gasAvailable := by
    show 3 ≤ _; rw [h_g]; have := ctx.gas_ok; omega
  refine ⟨_, Steps.refl s |>.snoc (Step.running h_halt
    (StepRunning.add s a b rest h_op h_gas_bd h_stack)),
    rfl, rfl, ?_, ?_, h_halt⟩
  · refine ⟨⟨?_, ?_, h_env, h_mem, h_active, h_pc_room, h_gas_room⟩, ?_⟩ <;> dsimp only
    · show (s.pc + UInt256.ofNat 1).toNat = ctx.pc_init + pc_off + 1
      rw [pc_add _ _ h_pcb, h_pc]
    · show s.gasAvailable - 3 = ctx.gas_init - (gas_off + 3)
      rw [h_g]; have := ctx.gas_ok; omega
  · show (s.pc + UInt256.ofNat 1).toNat = s.pc.toNat + Block.size [add]
    rw [pc_add _ _ h_pcb]; rfl

----------------------------------------------------------------------------
-- SUB
----------------------------------------------------------------------------

def sub : Insn := ⟨.SUB, none, 1⟩

theorem sub_triple {pctx : ProgramCtx} (ctx : BlockCtx pctx)
    (pc_off gas_off : Nat)
    (h_pc_room  : pc_off + 1 ≤ ctx.block_size)
    (h_gas_room : gas_off + 3 ≤ ctx.block_cost)
    {a b : UInt256} {rest : List UInt256} {memory : ByteArray} {active : UInt256} :
    Triple [sub] .falls
      (fun s => AtOffset ctx pc_off gas_off memory active s ∧ s.stack = a :: b :: rest)
      (fun sf => AtOffset ctx (pc_off + 1) (gas_off + 3) memory active sf ∧
                 sf.stack = (a - b) :: rest) := by
  intro s h_dec h_halt _h_cs ⟨⟨h_pc, h_g, h_env, h_mem, h_active, _, _⟩, h_stack⟩
  have h_op := decodedOp_of_block h_env h_dec
  have h_pcb : s.pc.toNat + 1 < UInt256.size := by
    rw [h_pc]; have := ctx.no_overflow; omega
  have h_gas_bd : Gas.baseCost s.fork .SUB ≤ s.gasAvailable := by
    show 3 ≤ _; rw [h_g]; have := ctx.gas_ok; omega
  refine ⟨_, Steps.refl s |>.snoc (Step.running h_halt
    (StepRunning.sub s a b rest h_op h_gas_bd h_stack)),
    rfl, rfl, ?_, ?_, h_halt⟩
  · refine ⟨⟨?_, ?_, h_env, h_mem, h_active, h_pc_room, h_gas_room⟩, ?_⟩ <;> dsimp only
    · show (s.pc + UInt256.ofNat 1).toNat = ctx.pc_init + pc_off + 1
      rw [pc_add _ _ h_pcb, h_pc]
    · show s.gasAvailable - 3 = ctx.gas_init - (gas_off + 3)
      rw [h_g]; have := ctx.gas_ok; omega
  · show (s.pc + UInt256.ofNat 1).toNat = s.pc.toNat + Block.size [sub]
    rw [pc_add _ _ h_pcb]; rfl

----------------------------------------------------------------------------
-- ISZERO
----------------------------------------------------------------------------

def iszero : Insn := ⟨.ISZERO, none, 1⟩

theorem iszero_triple {pctx : ProgramCtx} (ctx : BlockCtx pctx)
    (pc_off gas_off : Nat)
    (h_pc_room  : pc_off + 1 ≤ ctx.block_size)
    (h_gas_room : gas_off + 3 ≤ ctx.block_cost)
    {a : UInt256} {rest : List UInt256} {memory : ByteArray} {active : UInt256} :
    Triple [iszero] .falls
      (fun s => AtOffset ctx pc_off gas_off memory active s ∧ s.stack = a :: rest)
      (fun sf => AtOffset ctx (pc_off + 1) (gas_off + 3) memory active sf ∧
                 sf.stack = UInt256.isZero a :: rest) := by
  intro s h_dec h_halt _h_cs ⟨⟨h_pc, h_g, h_env, h_mem, h_active, _, _⟩, h_stack⟩
  have h_op := decodedOp_of_block h_env h_dec
  have h_pcb : s.pc.toNat + 1 < UInt256.size := by
    rw [h_pc]; have := ctx.no_overflow; omega
  have h_gas_bd : Gas.baseCost s.fork .ISZERO ≤ s.gasAvailable := by
    show 3 ≤ _; rw [h_g]; have := ctx.gas_ok; omega
  refine ⟨_, Steps.refl s |>.snoc (Step.running h_halt
    (StepRunning.iszero s a rest h_op h_gas_bd h_stack)),
    rfl, rfl, ?_, ?_, h_halt⟩
  · refine ⟨⟨?_, ?_, h_env, h_mem, h_active, h_pc_room, h_gas_room⟩, ?_⟩ <;> dsimp only
    · show (s.pc + UInt256.ofNat 1).toNat = ctx.pc_init + pc_off + 1
      rw [pc_add _ _ h_pcb, h_pc]
    · show s.gasAvailable - 3 = ctx.gas_init - (gas_off + 3)
      rw [h_g]; have := ctx.gas_ok; omega
  · show (s.pc + UInt256.ofNat 1).toNat = s.pc.toNat + Block.size [iszero]
    rw [pc_add _ _ h_pcb]; rfl

----------------------------------------------------------------------------
-- DUPn
----------------------------------------------------------------------------

def dup (n : Fin 16) : Insn := ⟨.Dup ⟨n⟩, none, 1⟩

theorem dup_triple {pctx : ProgramCtx} (ctx : BlockCtx pctx)
    (pc_off gas_off : Nat) (n : Fin 16) (v : UInt256)
    (h_pc_room  : pc_off + 1 ≤ ctx.block_size)
    (h_gas_room : gas_off + 3 ≤ ctx.block_cost)
    {stack : List UInt256} {memory : ByteArray} {active : UInt256}
    (h_get : stack[n.val]? = some v) :
    Triple [dup n] .falls
      (fun s => AtOffset ctx pc_off gas_off memory active s ∧ s.stack = stack)
      (fun sf => AtOffset ctx (pc_off + 1) (gas_off + 3) memory active sf ∧
                 sf.stack = v :: stack) := by
  intro s h_dec h_halt _h_cs ⟨⟨h_pc, h_g, h_env, h_mem, h_active, _, _⟩, h_stack⟩
  have h_op := decodedOp_of_block h_env h_dec
  have h_pcb : s.pc.toNat + 1 < UInt256.size := by
    rw [h_pc]; have := ctx.no_overflow; omega
  have h_gas_bd : Gas.baseCost s.fork (.Dup ⟨n⟩) ≤ s.gasAvailable := by
    show 3 ≤ _; rw [h_g]; have := ctx.gas_ok; omega
  have h_get_s : s.stack[n.val]? = some v := by rw [h_stack]; exact h_get
  refine ⟨_, Steps.refl s |>.snoc (Step.running h_halt
    (StepRunning.dup s n v h_op h_gas_bd h_get_s)),
    rfl, rfl, ?_, ?_, h_halt⟩
  · refine ⟨⟨?_, ?_, h_env, h_mem, h_active, h_pc_room, h_gas_room⟩, ?_⟩ <;> dsimp only
    · show (s.pc + UInt256.ofNat 1).toNat = ctx.pc_init + pc_off + 1
      rw [pc_add _ _ h_pcb, h_pc]
    · show s.gasAvailable - 3 = ctx.gas_init - (gas_off + 3)
      rw [h_g]; have := ctx.gas_ok; omega
    · show v :: s.stack = v :: stack; rw [h_stack]
  · show (s.pc + UInt256.ofNat 1).toNat = s.pc.toNat + Block.size [dup n]
    rw [pc_add _ _ h_pcb]; rfl

----------------------------------------------------------------------------
-- SWAPn
----------------------------------------------------------------------------

def swap (n : Fin 16) : Insn := ⟨.Swap ⟨n⟩, none, 1⟩

theorem swap_triple {pctx : ProgramCtx} (ctx : BlockCtx pctx)
    (pc_off gas_off : Nat) (n : Fin 16)
    (h_pc_room  : pc_off + 1 ≤ ctx.block_size)
    (h_gas_room : gas_off + 3 ≤ ctx.block_cost)
    {stack stack' : List UInt256} {memory : ByteArray} {active : UInt256}
    (h_sw : stack.exchange 0 (n.val + 1) = some stack') :
    Triple [swap n] .falls
      (fun s => AtOffset ctx pc_off gas_off memory active s ∧ s.stack = stack)
      (fun sf => AtOffset ctx (pc_off + 1) (gas_off + 3) memory active sf ∧
                 sf.stack = stack') := by
  intro s h_dec h_halt _h_cs ⟨⟨h_pc, h_g, h_env, h_mem, h_active, _, _⟩, h_stack⟩
  have h_op := decodedOp_of_block h_env h_dec
  have h_pcb : s.pc.toNat + 1 < UInt256.size := by
    rw [h_pc]; have := ctx.no_overflow; omega
  have h_gas_bd : Gas.baseCost s.fork (.Swap ⟨n⟩) ≤ s.gasAvailable := by
    show 3 ≤ _; rw [h_g]; have := ctx.gas_ok; omega
  have h_sw_s : s.stack.exchange 0 (n.val + 1) = some stack' := by
    rw [h_stack]; exact h_sw
  refine ⟨_, Steps.refl s |>.snoc (Step.running h_halt
    (StepRunning.swap s n stack' h_op h_gas_bd h_sw_s)),
    rfl, rfl, ?_, ?_, h_halt⟩
  · refine ⟨⟨?_, ?_, h_env, h_mem, h_active, h_pc_room, h_gas_room⟩, ?_⟩ <;> dsimp only
    · show (s.pc + UInt256.ofNat 1).toNat = ctx.pc_init + pc_off + 1
      rw [pc_add _ _ h_pcb, h_pc]
    · show s.gasAvailable - 3 = ctx.gas_init - (gas_off + 3)
      rw [h_g]; have := ctx.gas_ok; omega
  · show (s.pc + UInt256.ofNat 1).toNat = s.pc.toNat + Block.size [swap n]
    rw [pc_add _ _ h_pcb]; rfl

----------------------------------------------------------------------------
-- CALLDATALOAD — references `pctx.env.calldata` thanks to env-pinning.
----------------------------------------------------------------------------

def calldataload : Insn := ⟨.CALLDATALOAD, none, 1⟩

theorem calldataload_triple {pctx : ProgramCtx} (ctx : BlockCtx pctx)
    (pc_off gas_off : Nat)
    (h_pc_room  : pc_off + 1 ≤ ctx.block_size)
    (h_gas_room : gas_off + 3 ≤ ctx.block_cost)
    {i : UInt256} {rest : List UInt256} {memory : ByteArray} {active : UInt256} :
    Triple [calldataload] .falls
      (fun s => AtOffset ctx pc_off gas_off memory active s ∧ s.stack = i :: rest)
      (fun sf => AtOffset ctx (pc_off + 1) (gas_off + 3) memory active sf ∧
                 sf.stack =
                   MachineState.readWord pctx.env.calldata i.toNat :: rest) := by
  intro s h_dec h_halt _h_cs ⟨⟨h_pc, h_g, h_env, h_mem, h_active, _, _⟩, h_stack⟩
  have h_op := decodedOp_of_block h_env h_dec
  have h_pcb : s.pc.toNat + 1 < UInt256.size := by
    rw [h_pc]; have := ctx.no_overflow; omega
  have h_gas_bd : Gas.baseCost s.fork .CALLDATALOAD ≤ s.gasAvailable := by
    show 3 ≤ _; rw [h_g]; have := ctx.gas_ok; omega
  refine ⟨_, Steps.refl s |>.snoc (Step.running h_halt
    (StepRunning.calldataload s i rest h_op h_gas_bd h_stack)),
    rfl, rfl, ?_, ?_, h_halt⟩
  · refine ⟨⟨?_, ?_, h_env, h_mem, h_active, h_pc_room, h_gas_room⟩, ?_⟩ <;> dsimp only
    · show (s.pc + UInt256.ofNat 1).toNat = ctx.pc_init + pc_off + 1
      rw [pc_add _ _ h_pcb, h_pc]
    · show s.gasAvailable - 3 = ctx.gas_init - (gas_off + 3)
      rw [h_g]; have := ctx.gas_ok; omega
    · show MachineState.readWord s.executionEnv.calldata _ :: rest = _
      rw [h_env]
  · show (s.pc + UInt256.ofNat 1).toNat = s.pc.toNat + Block.size [calldataload]
    rw [pc_add _ _ h_pcb]; rfl

----------------------------------------------------------------------------
-- JUMP — exits via `.jump dest.toNat`.
----------------------------------------------------------------------------

def jump : Insn := ⟨.JUMP, none, 1⟩

theorem jump_triple {pctx : ProgramCtx} (ctx : BlockCtx pctx)
    (pc_off gas_off : Nat)
    (h_gas_room : gas_off + 8 ≤ ctx.block_cost)
    {dest : UInt256} {rest : List UInt256} {memory : ByteArray} {active : UInt256}
    (h_valid : Decode.isValidJumpDest pctx.code dest.toNat = true) :
    Triple [jump] (.jump dest.toNat)
      (fun s => AtOffset ctx pc_off gas_off memory active s ∧ s.stack = dest :: rest)
      (fun sf => sf.executionEnv = pctx.env ∧
                 sf.memory = memory ∧
                 sf.activeWords = active ∧
                 sf.stack = rest ∧
                 sf.gasAvailable = ctx.gas_init - (gas_off + 8)) := by
  intro s h_dec h_halt _h_cs ⟨⟨h_pc, h_g, h_env, h_mem, h_active, _, _⟩, h_stack⟩
  have h_op := decodedOp_of_block h_env h_dec
  have h_gas_bd : Gas.baseCost s.fork .JUMP ≤ s.gasAvailable := by
    show 8 ≤ _; rw [h_g]; have := ctx.gas_ok; omega
  have h_valid_s : Decode.isValidJumpDest s.executionEnv.code dest.toNat = true := by
    rw [h_env, pctx.env_code]; exact h_valid
  refine ⟨_, Steps.refl s |>.snoc (Step.running h_halt
    (StepRunning.jump s dest rest h_op h_gas_bd h_stack h_valid_s)),
    rfl, rfl, ?_, rfl, h_halt⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only
  · exact h_env
  · exact h_mem
  · exact h_active
  · show s.gasAvailable - 8 = ctx.gas_init - (gas_off + 8)
    rw [h_g]; have := ctx.gas_ok; omega

----------------------------------------------------------------------------
-- JUMPI (taken / not-taken branches)
----------------------------------------------------------------------------

def jumpi : Insn := ⟨.JUMPI, none, 1⟩

theorem jumpi_taken_triple {pctx : ProgramCtx} (ctx : BlockCtx pctx)
    (pc_off gas_off : Nat)
    (h_gas_room : gas_off + 10 ≤ ctx.block_cost)
    {dest cond : UInt256} {rest : List UInt256} {memory : ByteArray} {active : UInt256}
    (h_cond : UInt256.isTrue cond)
    (h_valid : Decode.isValidJumpDest pctx.code dest.toNat = true) :
    Triple [jumpi] (.jump dest.toNat)
      (fun s => AtOffset ctx pc_off gas_off memory active s ∧
                s.stack = dest :: cond :: rest)
      (fun sf => sf.executionEnv = pctx.env ∧
                 sf.memory = memory ∧
                 sf.activeWords = active ∧
                 sf.stack = rest ∧
                 sf.gasAvailable = ctx.gas_init - (gas_off + 10)) := by
  intro s h_dec h_halt _h_cs ⟨⟨h_pc, h_g, h_env, h_mem, h_active, _, _⟩, h_stack⟩
  have h_op := decodedOp_of_block h_env h_dec
  have h_gas_bd : Gas.baseCost s.fork .JUMPI ≤ s.gasAvailable := by
    show 10 ≤ _; rw [h_g]; have := ctx.gas_ok; omega
  have h_valid_s : Decode.isValidJumpDest s.executionEnv.code dest.toNat = true := by
    rw [h_env, pctx.env_code]; exact h_valid
  refine ⟨_, Steps.refl s |>.snoc (Step.running h_halt
    (StepRunning.jumpi_taken s dest cond rest h_op h_gas_bd h_stack h_cond h_valid_s)),
    rfl, rfl, ?_, rfl, h_halt⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only
  · exact h_env
  · exact h_mem
  · exact h_active
  · show s.gasAvailable - 10 = ctx.gas_init - (gas_off + 10)
    rw [h_g]; have := ctx.gas_ok; omega

theorem jumpi_notTaken_triple {pctx : ProgramCtx} (ctx : BlockCtx pctx)
    (pc_off gas_off : Nat)
    (h_pc_room  : pc_off + 1 ≤ ctx.block_size)
    (h_gas_room : gas_off + 10 ≤ ctx.block_cost)
    {dest cond : UInt256} {rest : List UInt256} {memory : ByteArray} {active : UInt256}
    (h_cond : ¬ UInt256.isTrue cond) :
    Triple [jumpi] .falls
      (fun s => AtOffset ctx pc_off gas_off memory active s ∧
                s.stack = dest :: cond :: rest)
      (fun sf => AtOffset ctx (pc_off + 1) (gas_off + 10) memory active sf ∧
                 sf.stack = rest) := by
  intro s h_dec h_halt _h_cs ⟨⟨h_pc, h_g, h_env, h_mem, h_active, _, _⟩, h_stack⟩
  have h_op := decodedOp_of_block h_env h_dec
  have h_pcb : s.pc.toNat + 1 < UInt256.size := by
    rw [h_pc]; have := ctx.no_overflow; omega
  have h_gas_bd : Gas.baseCost s.fork .JUMPI ≤ s.gasAvailable := by
    show 10 ≤ _; rw [h_g]; have := ctx.gas_ok; omega
  refine ⟨_, Steps.refl s |>.snoc (Step.running h_halt
    (StepRunning.jumpi_notTaken s dest cond rest h_op h_gas_bd h_stack h_cond)),
    rfl, rfl, ?_, ?_, h_halt⟩
  · refine ⟨⟨?_, ?_, h_env, h_mem, h_active, h_pc_room, h_gas_room⟩, ?_⟩ <;> dsimp only
    · show (s.pc + UInt256.ofNat 1).toNat = ctx.pc_init + pc_off + 1
      rw [pc_add _ _ h_pcb, h_pc]
    · show s.gasAvailable - 10 = ctx.gas_init - (gas_off + 10)
      rw [h_g]; have := ctx.gas_ok; omega
  · show (s.pc + UInt256.ofNat 1).toNat = s.pc.toNat + Block.size [jumpi]
    rw [pc_add _ _ h_pcb]; rfl

----------------------------------------------------------------------------
-- MSTORE — memory is updated.
----------------------------------------------------------------------------

def mstore : Insn := ⟨.MSTORE, none, 1⟩

theorem mstore_triple {pctx : ProgramCtx} (ctx : BlockCtx pctx)
    (pc_off gas_off : Nat)
    (h_pc_room  : pc_off + 1 ≤ ctx.block_size)
    (h_gas_room : gas_off + 6 ≤ ctx.block_cost)
    {value : UInt256} {rest : List UInt256} {memory : ByteArray} :
    Triple [mstore] .falls
      (fun s => AtOffset ctx pc_off gas_off memory (UInt256.ofNat 0) s ∧
                s.stack = UInt256.ofNat 0 :: value :: rest)
      (fun sf => AtOffset ctx (pc_off + 1) (gas_off + 6)
                   (MachineState.writeBytes memory (MachineState.wordBytes value) 0)
                   (UInt256.ofNat 1) sf ∧
                 sf.stack = rest) := by
  intro s h_dec h_halt _h_cs ⟨⟨h_pc, h_g, h_env, h_mem, h_active, _, _⟩, h_stack⟩
  have h_op := decodedOp_of_block h_env h_dec
  have h_pcb : s.pc.toNat + 1 < UInt256.size := by
    rw [h_pc]; have := ctx.no_overflow; omega
  have h_active_nat : s.activeWords.toNat = 0 := by rw [h_active]; rfl
  have h_total : Gas.mstoreTotal s (UInt256.ofNat 0) ≤ s.gasAvailable := by
    show Gas.baseCost s.fork .MSTORE + MachineState.memExpansionDelta _ _ _ ≤ _
    rw [h_active_nat, h_g]; show 3 + 3 ≤ _
    have := ctx.gas_ok; omega
  refine ⟨_, Steps.refl s |>.snoc (Step.running h_halt
    (StepRunning.mstore s (UInt256.ofNat 0) value rest h_op h_stack h_total)),
    rfl, rfl, ?_, ?_, h_halt⟩
  · refine ⟨⟨?_, ?_, h_env, ?_, ?_, h_pc_room, h_gas_room⟩, ?_⟩ <;> dsimp only
    · show (s.pc + UInt256.ofNat 1).toNat = ctx.pc_init + pc_off + 1
      rw [pc_add _ _ h_pcb, h_pc]
    · show s.gasAvailable - Gas.mstoreTotal s (UInt256.ofNat 0) =
          ctx.gas_init - (gas_off + 6)
      show s.gasAvailable - (Gas.baseCost s.fork .MSTORE +
        MachineState.memExpansionDelta _ _ _) = ctx.gas_init - (gas_off + 6)
      rw [h_active_nat, h_g]; show ctx.gas_init - gas_off - (3 + 3) = _
      have := ctx.gas_ok; omega
    · show MachineState.writeBytes s.memory _ _ = _
      rw [h_mem]; rfl
    · show s.activeWordsAfterUInt256 (UInt256.ofNat 0).toNat 32 = UInt256.ofNat 1
      show UInt256.ofNat (MachineState.activeWordsAfter _ _ _) = UInt256.ofNat 1
      rw [h_active_nat]; rfl
  · show (s.pc + UInt256.ofNat 1).toNat = s.pc.toNat + Block.size [mstore]
    rw [pc_add _ _ h_pcb]; rfl

----------------------------------------------------------------------------
-- RETURN — halts with `hReturn = readPadded memory 0 32`.
----------------------------------------------------------------------------

def retn : Insn := ⟨.RETURN, none, 1⟩

theorem return_triple {pctx : ProgramCtx} (ctx : BlockCtx pctx)
    (pc_off gas_off : Nat)
    {rest : List UInt256} {memory : ByteArray} :
    Triple [retn] .halted
      (fun s => AtOffset ctx pc_off gas_off memory (UInt256.ofNat 1) s ∧
                s.stack = UInt256.ofNat 0 :: UInt256.ofNat 0x20 :: rest)
      (fun sf => sf.halt = .Returned ∧
                 sf.hReturn = MachineState.readPadded memory 0 32) := by
  intro s h_dec h_halt _h_cs ⟨⟨h_pc, h_g, h_env, h_mem, h_active, _, _⟩, h_stack⟩
  have h_op := decodedOp_of_block h_env h_dec
  have h_active_nat : s.activeWords.toNat = 1 := by rw [h_active]; rfl
  have h_total : Gas.returnTotal s (UInt256.ofNat 0) (UInt256.ofNat 0x20) ≤ s.gasAvailable := by
    show Gas.baseCost s.fork .RETURN + MachineState.memExpansionDelta _ _ _ ≤ _
    rw [h_active_nat]; show 0 + MachineState.memExpansionDelta 1 0 32 ≤ _
    show 0 ≤ _; omega
  refine ⟨_, Steps.refl s |>.snoc (Step.running h_halt
    (StepRunning.return_ s (UInt256.ofNat 0) (UInt256.ofNat 0x20) rest
      h_op h_stack h_total)),
    rfl, rfl, ?_, ?_⟩
  · refine ⟨rfl, ?_⟩
    dsimp only
    show MachineState.readPadded s.memory _ _ = MachineState.readPadded memory 0 32
    rw [h_mem]; rfl
  · intro h; dsimp only at h; cases h

end Block
end Hoare
end EvmSemantics
