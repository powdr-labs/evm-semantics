module

public import EvmSemantics

/-!
`Hoare.Triple` — a thin Hoare-triple layer over the relational small-step
semantics, plus per-opcode triples for every opcode the demos use.

The basic shape is

```
def Triple (P Q : State → Prop) : Prop :=
  ∀ s, P s → ∃ sf, Steps s sf ∧ Q sf
```

— "from any state satisfying `P`, the `Steps` closure reaches some state
satisfying `Q`". `Triple.seq` composes triples. `StateAt env pc stack
gas active` is the standard state predicate threaded by the per-opcode
triples: it fixes the execution environment, program counter,
operand-stack contents, remaining gas, and active-words count.

Each per-opcode `*_triple` is parametric in the surrounding stack frame,
gas budget, and `pc`, and takes a `Decode.decodeAt env.code pc_n =
some (.OP, …)` hypothesis at the head. Callers typically tabulate their
program's decoder once (a `decodeAt`-equivalent `Nat → Option …` lookup,
discharged by `decide` on each live PC) and bridge it to
`Decode.decodeAt code` with a single helper — see `FibDemo.lean` for the
worked example.

The triples are written against the relational `StepRunning` rules
(flat `{ s with … }` post-states, bundled `Gas.<op>Total` totals), so
their post-state field equations close by direct `rfl` projections —
no `consumeGas`/`replaceStackAndIncrPC` plumbing leaks into the block
proofs.
-/

@[expose] public section

open EvmSemantics EvmSemantics.EVM

namespace EvmSemantics
namespace Hoare

----------------------------------------------------------------------------
-- UInt256 arithmetic helpers used by the per-opcode triples.
----------------------------------------------------------------------------

/-- `(a + UInt256.ofNat n).toNat = a.toNat + n` provided no overflow.
    Used to track `pc` arithmetic across the steps of each block. -/
theorem pc_add (a : UInt256) (n : Nat)
    (h : a.toNat + n < UInt256.size) :
    (a + UInt256.ofNat n).toNat = a.toNat + n := by
  show (UInt256.add a (UInt256.ofNat n)).val.val = a.toNat + n
  unfold UInt256.add UInt256.ofNat UInt256.toNat at *
  simp [Fin.add_def, Nat.mod_eq_of_lt h]

/-- `(UInt256.ofNat k).toNat = k` provided `k < 2^256`. -/
theorem ofNat_toNat (k : Nat) (h : k < UInt256.size) :
    (UInt256.ofNat k).toNat = k := by
  show (Fin.ofNat UInt256.size k).val = k
  exact Nat.mod_eq_of_lt h

/-- Equal `.toNat` implies equal `UInt256` (since `UInt256 = Fin 2^256`). -/
theorem uint256_eq_of_toNat (i j : UInt256) (h : i.toNat = j.toNat) : i = j := by
  cases i; cases j; congr 1; exact Fin.ext h

/-- `UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b)` when `a + b < 2^256`. -/
theorem ofNat_add (a b : Nat) (h : a + b < UInt256.size) :
    UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) := by
  apply uint256_eq_of_toNat
  rw [ofNat_toNat _ h]
  have := pc_add (UInt256.ofNat a) b
    (by rw [ofNat_toNat a (by omega)]; omega)
  rw [this, ofNat_toNat a (by omega)]

/-- `UInt256.ofNat (k+1) - UInt256.ofNat 1 = UInt256.ofNat k` when `k+1 < 2^256`. -/
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
-- The Triple datatype.
----------------------------------------------------------------------------

/-- Bytecode-level Hoare triple over `Steps`. `Triple P Q` says: from any
    state satisfying `P`, the `Steps` closure reaches some state
    satisfying `Q`. The bytecode is fixed at the `executionEnv.code`
    level — where a block "ends" lives inside `Q` (typically `pc = m ∧
    stack = …`). -/
def Triple (P Q : State → Prop) : Prop :=
  ∀ s, P s → ∃ sf, Steps s sf ∧ Q sf

/-- Sequencing: `{P} ▷ {Q}` and `{Q} ▷ {R}` compose to `{P} ▷ {R}`. -/
theorem Triple.seq {P Q R : State → Prop} (h1 : Triple P Q) (h2 : Triple Q R) :
    Triple P R := fun s hp =>
  let ⟨s1, hs1, hq⟩ := h1 s hp
  let ⟨sf, hsf, hr⟩ := h2 s1 hq
  ⟨sf, hs1.append hsf, hr⟩

----------------------------------------------------------------------------
-- The standard state predicate.
----------------------------------------------------------------------------

/-- The "standard" state predicate threaded by every per-opcode triple.
    Bundles the full `ExecutionEnv` (so calldata, address, etc. are
    preserved across opcodes that don't touch them) plus the moving
    parts (`pc`, `stack`, `gasAvailable`, `activeWords`). The active
    field carries `UInt256` rather than `Nat` so it can be compared
    against post-state record-update results directly. -/
structure StateAt (env : ExecutionEnv) (pc_n : Nat) (stack : List UInt256)
    (gas : Nat) (active : UInt256) (s : State) : Prop where
  env_eq : s.executionEnv = env
  pc : s.pc.toNat = pc_n
  halt : s.halt = .Running
  stack_eq : s.stack = stack
  gas_eq : s.gasAvailable = gas
  active_eq : s.toMachineState.activeWords = active

/-- Convenience: from `StateAt env pc … s`, `s.decoded = some (op, imm)` follows
    from `Decode.decodeAt env.code pc_n = some (op, imm)`. -/
private theorem decoded_of_decodeAt {env : ExecutionEnv} {pc_n : Nat}
    {op : Operation} {imm : Option (UInt256 × Nat)} {s : State}
    (h_env : s.executionEnv = env) (h_pc : s.pc.toNat = pc_n)
    (h_dec : Decode.decodeAt env.code pc_n = some (op, imm)) :
    s.decoded = some (op, imm) := by
  show Decode.decodeAt s.executionEnv.code s.pc.toNat = _
  rw [h_env, h_pc]; exact h_dec

private theorem decodedOp_of_decodeAt {env : ExecutionEnv} {pc_n : Nat}
    {op : Operation} {imm : Option (UInt256 × Nat)} {s : State}
    (h_env : s.executionEnv = env) (h_pc : s.pc.toNat = pc_n)
    (h_dec : Decode.decodeAt env.code pc_n = some (op, imm)) :
    s.decodedOp = some op := by
  unfold State.decodedOp
  rw [decoded_of_decodeAt h_env h_pc h_dec]; rfl

----------------------------------------------------------------------------
-- Per-opcode triples.
--
-- One triple per opcode the demos exercise. Each triple is parametric
-- in the surrounding stack frame, gas budget, and program counter. The
-- decode premise is `Decode.decodeAt env.code pc_n = some (.OP, …)` —
-- callers typically supply this via a program-specific tabulated
-- decoder + a bridge lemma to `Decode.decodeAt`.
----------------------------------------------------------------------------

/-- `PUSH1 data` at `pc_n` (2 bytes, cost 3). -/
theorem push1_triple {env : ExecutionEnv} {pc_n : Nat} {data : UInt256}
    {rest : List UInt256} {gas_in : Nat} {active : UInt256}
    (h_pcb : pc_n + 2 < UInt256.size)
    (h_dec : Decode.decodeAt env.code pc_n =
              some (.Push ⟨1, by decide⟩, some (data, 1)))
    (h_gas : 3 ≤ gas_in) :
    Triple (StateAt env pc_n rest gas_in active)
           (StateAt env (pc_n + 2) (data :: rest) (gas_in - 3) active) := by
  intro s ⟨h_env, h_pc, h_halt, h_stack, h_g, h_active⟩
  have hd : s.decoded = some (.Push ⟨1, by decide⟩, some (data, 1)) :=
    decoded_of_decodeAt h_env h_pc h_dec
  have h_gas_bd : Gas.baseCost s.fork (.Push ⟨1, by decide⟩) ≤ s.gasAvailable := by
    show 3 ≤ _; rw [h_g]; omega
  refine ⟨_, Steps.refl s |>.snoc (Step.running h_halt
    (StepRunning.pushN s ⟨1, by decide⟩ data 1 (by decide) hd h_gas_bd)), ?_⟩
  refine ⟨h_env, ?_, h_halt, ?_, ?_, h_active⟩
  · show (s.pc + UInt256.ofNat 2).toNat = pc_n + 2
    rw [pc_add _ _ (by rw [h_pc]; omega), h_pc]
  · show data :: s.stack = data :: rest
    rw [h_stack]
  · show s.gasAvailable - 3 = gas_in - 3
    rw [h_g]

/-- `CALLDATALOAD` at `pc_n` (1 byte, cost 3). Pops the offset, pushes 32
    bytes of calldata as a `UInt256`. -/
theorem calldataload_triple {env : ExecutionEnv} {pc_n : Nat} {i : UInt256}
    {rest : List UInt256} {gas_in : Nat} {active : UInt256}
    (h_pcb : pc_n + 1 < UInt256.size)
    (h_dec : Decode.decodeAt env.code pc_n = some (.CALLDATALOAD, none))
    (h_gas : 3 ≤ gas_in) :
    Triple (StateAt env pc_n (i :: rest) gas_in active)
           (StateAt env (pc_n + 1)
             (MachineState.readWord env.calldata i.toNat :: rest)
             (gas_in - 3) active) := by
  intro s ⟨h_env, h_pc, h_halt, h_stack, h_g, h_active⟩
  have h_op : s.decodedOp = some .CALLDATALOAD :=
    decodedOp_of_decodeAt h_env h_pc h_dec
  have h_gas_bd : Gas.baseCost s.fork .CALLDATALOAD ≤ s.gasAvailable := by
    show 3 ≤ _; rw [h_g]; omega
  refine ⟨_, Steps.refl s |>.snoc (Step.running h_halt
    (StepRunning.calldataload s i rest h_op h_gas_bd h_stack)), ?_⟩
  refine ⟨h_env, ?_, h_halt, ?_, ?_, h_active⟩
  · show (s.pc + UInt256.ofNat 1).toNat = pc_n + 1
    rw [pc_add _ _ (by rw [h_pc]; omega), h_pc]
  · show MachineState.readWord s.executionEnv.calldata _ :: rest = _
    rw [h_env]
  · show s.gasAvailable - 3 = gas_in - 3
    rw [h_g]

/-- `JUMPDEST` at `pc_n` (1 byte, base cost 1). No-op for the stack. -/
theorem jumpdest_triple {env : ExecutionEnv} {pc_n : Nat}
    {stack : List UInt256} {gas_in : Nat} {active : UInt256}
    (h_pcb : pc_n + 1 < UInt256.size)
    (h_dec : Decode.decodeAt env.code pc_n = some (.JUMPDEST, none))
    (h_gas : 1 ≤ gas_in) :
    Triple (StateAt env pc_n stack gas_in active)
           (StateAt env (pc_n + 1) stack (gas_in - 1) active) := by
  intro s ⟨h_env, h_pc, h_halt, h_stack, h_g, h_active⟩
  have h_op : s.decodedOp = some .JUMPDEST :=
    decodedOp_of_decodeAt h_env h_pc h_dec
  have h_gas_bd : Gas.baseCost s.fork .JUMPDEST ≤ s.gasAvailable := by
    show 1 ≤ _; rw [h_g]; omega
  refine ⟨_, Steps.refl s |>.snoc (Step.running h_halt
    (StepRunning.jumpdest s h_op h_gas_bd)), ?_⟩
  refine ⟨h_env, ?_, h_halt, h_stack, ?_, h_active⟩
  · show (s.pc + UInt256.ofNat 1).toNat = pc_n + 1
    rw [pc_add _ _ (by rw [h_pc]; omega), h_pc]
  · show s.gasAvailable - 1 = gas_in - 1
    rw [h_g]

/-- `DUPn` at `pc_n` (1 byte, cost 3). Copies `stack[n]` (0-indexed) to top. -/
theorem dup_triple {env : ExecutionEnv} {pc_n : Nat} {n : Fin 16} {v : UInt256}
    {stack : List UInt256} {gas_in : Nat} {active : UInt256}
    (h_pcb : pc_n + 1 < UInt256.size)
    (h_dec : Decode.decodeAt env.code pc_n = some (.Dup ⟨n⟩, none))
    (h_get : stack[n.val]? = some v)
    (h_gas : 3 ≤ gas_in) :
    Triple (StateAt env pc_n stack gas_in active)
           (StateAt env (pc_n + 1) (v :: stack) (gas_in - 3) active) := by
  intro s ⟨h_env, h_pc, h_halt, h_stack, h_g, h_active⟩
  have h_op : s.decodedOp = some (.Dup ⟨n⟩) :=
    decodedOp_of_decodeAt h_env h_pc h_dec
  have h_gas_bd : Gas.baseCost s.fork (.Dup ⟨n⟩) ≤ s.gasAvailable := by
    show 3 ≤ _; rw [h_g]; omega
  have h_get_s : s.stack[n.val]? = some v := by rw [h_stack]; exact h_get
  refine ⟨_, Steps.refl s |>.snoc (Step.running h_halt
    (StepRunning.dup s n v h_op h_gas_bd h_get_s)), ?_⟩
  refine ⟨h_env, ?_, h_halt, ?_, ?_, h_active⟩
  · show (s.pc + UInt256.ofNat 1).toNat = pc_n + 1
    rw [pc_add _ _ (by rw [h_pc]; omega), h_pc]
  · show v :: s.stack = v :: stack
    rw [h_stack]
  · show s.gasAvailable - 3 = gas_in - 3
    rw [h_g]

/-- `ISZERO` at `pc_n` (1 byte, cost 3). Pops `a`, pushes `isZero a`. -/
theorem iszero_triple {env : ExecutionEnv} {pc_n : Nat} {a : UInt256}
    {rest : List UInt256} {gas_in : Nat} {active : UInt256}
    (h_pcb : pc_n + 1 < UInt256.size)
    (h_dec : Decode.decodeAt env.code pc_n = some (.ISZERO, none))
    (h_gas : 3 ≤ gas_in) :
    Triple (StateAt env pc_n (a :: rest) gas_in active)
           (StateAt env (pc_n + 1) (UInt256.isZero a :: rest) (gas_in - 3) active) := by
  intro s ⟨h_env, h_pc, h_halt, h_stack, h_g, h_active⟩
  have h_op : s.decodedOp = some .ISZERO :=
    decodedOp_of_decodeAt h_env h_pc h_dec
  have h_gas_bd : Gas.baseCost s.fork .ISZERO ≤ s.gasAvailable := by
    show 3 ≤ _; rw [h_g]; omega
  refine ⟨_, Steps.refl s |>.snoc (Step.running h_halt
    (StepRunning.iszero s a rest h_op h_gas_bd h_stack)), ?_⟩
  refine ⟨h_env, ?_, h_halt, rfl, ?_, h_active⟩
  · show (s.pc + UInt256.ofNat 1).toNat = pc_n + 1
    rw [pc_add _ _ (by rw [h_pc]; omega), h_pc]
  · show s.gasAvailable - 3 = gas_in - 3
    rw [h_g]

/-- `SWAPn` at `pc_n` (1 byte, cost 3). -/
theorem swap_triple {env : ExecutionEnv} {pc_n : Nat} {n : Fin 16}
    {stack stack' : List UInt256} {gas_in : Nat} {active : UInt256}
    (h_pcb : pc_n + 1 < UInt256.size)
    (h_dec : Decode.decodeAt env.code pc_n = some (.Swap ⟨n⟩, none))
    (h_sw : stack.exchange 0 (n.val + 1) = some stack')
    (h_gas : 3 ≤ gas_in) :
    Triple (StateAt env pc_n stack gas_in active)
           (StateAt env (pc_n + 1) stack' (gas_in - 3) active) := by
  intro s ⟨h_env, h_pc, h_halt, h_stack, h_g, h_active⟩
  have h_op : s.decodedOp = some (.Swap ⟨n⟩) :=
    decodedOp_of_decodeAt h_env h_pc h_dec
  have h_gas_bd : Gas.baseCost s.fork (.Swap ⟨n⟩) ≤ s.gasAvailable := by
    show 3 ≤ _; rw [h_g]; omega
  have h_sw_s : s.stack.exchange 0 (n.val + 1) = some stack' := by
    rw [h_stack]; exact h_sw
  refine ⟨_, Steps.refl s |>.snoc (Step.running h_halt
    (StepRunning.swap s n stack' h_op h_gas_bd h_sw_s)), ?_⟩
  refine ⟨h_env, ?_, h_halt, rfl, ?_, h_active⟩
  · show (s.pc + UInt256.ofNat 1).toNat = pc_n + 1
    rw [pc_add _ _ (by rw [h_pc]; omega), h_pc]
  · show s.gasAvailable - 3 = gas_in - 3
    rw [h_g]

/-- `ADD` at `pc_n` (1 byte, cost 3). Pops `a`, `b`; pushes `a + b`. -/
theorem add_triple {env : ExecutionEnv} {pc_n : Nat} {a b : UInt256}
    {rest : List UInt256} {gas_in : Nat} {active : UInt256}
    (h_pcb : pc_n + 1 < UInt256.size)
    (h_dec : Decode.decodeAt env.code pc_n = some (.ADD, none))
    (h_gas : 3 ≤ gas_in) :
    Triple (StateAt env pc_n (a :: b :: rest) gas_in active)
           (StateAt env (pc_n + 1) ((a + b) :: rest) (gas_in - 3) active) := by
  intro s ⟨h_env, h_pc, h_halt, h_stack, h_g, h_active⟩
  have h_op : s.decodedOp = some .ADD :=
    decodedOp_of_decodeAt h_env h_pc h_dec
  have h_gas_bd : Gas.baseCost s.fork .ADD ≤ s.gasAvailable := by
    show 3 ≤ _; rw [h_g]; omega
  refine ⟨_, Steps.refl s |>.snoc (Step.running h_halt
    (StepRunning.add s a b rest h_op h_gas_bd h_stack)), ?_⟩
  refine ⟨h_env, ?_, h_halt, rfl, ?_, h_active⟩
  · show (s.pc + UInt256.ofNat 1).toNat = pc_n + 1
    rw [pc_add _ _ (by rw [h_pc]; omega), h_pc]
  · show s.gasAvailable - 3 = gas_in - 3
    rw [h_g]

/-- `SUB` at `pc_n` (1 byte, cost 3). Pops `a`, `b`; pushes `a - b`. -/
theorem sub_triple {env : ExecutionEnv} {pc_n : Nat} {a b : UInt256}
    {rest : List UInt256} {gas_in : Nat} {active : UInt256}
    (h_pcb : pc_n + 1 < UInt256.size)
    (h_dec : Decode.decodeAt env.code pc_n = some (.SUB, none))
    (h_gas : 3 ≤ gas_in) :
    Triple (StateAt env pc_n (a :: b :: rest) gas_in active)
           (StateAt env (pc_n + 1) ((a - b) :: rest) (gas_in - 3) active) := by
  intro s ⟨h_env, h_pc, h_halt, h_stack, h_g, h_active⟩
  have h_op : s.decodedOp = some .SUB :=
    decodedOp_of_decodeAt h_env h_pc h_dec
  have h_gas_bd : Gas.baseCost s.fork .SUB ≤ s.gasAvailable := by
    show 3 ≤ _; rw [h_g]; omega
  refine ⟨_, Steps.refl s |>.snoc (Step.running h_halt
    (StepRunning.sub s a b rest h_op h_gas_bd h_stack)), ?_⟩
  refine ⟨h_env, ?_, h_halt, rfl, ?_, h_active⟩
  · show (s.pc + UInt256.ofNat 1).toNat = pc_n + 1
    rw [pc_add _ _ (by rw [h_pc]; omega), h_pc]
  · show s.gasAvailable - 3 = gas_in - 3
    rw [h_g]

/-- `POP` at `pc_n` (1 byte, cost 2). Discards top of stack. -/
theorem pop_triple {env : ExecutionEnv} {pc_n : Nat} {a : UInt256}
    {rest : List UInt256} {gas_in : Nat} {active : UInt256}
    (h_pcb : pc_n + 1 < UInt256.size)
    (h_dec : Decode.decodeAt env.code pc_n = some (.POP, none))
    (h_gas : 2 ≤ gas_in) :
    Triple (StateAt env pc_n (a :: rest) gas_in active)
           (StateAt env (pc_n + 1) rest (gas_in - 2) active) := by
  intro s ⟨h_env, h_pc, h_halt, h_stack, h_g, h_active⟩
  have h_op : s.decodedOp = some .POP :=
    decodedOp_of_decodeAt h_env h_pc h_dec
  have h_gas_bd : Gas.baseCost s.fork .POP ≤ s.gasAvailable := by
    show 2 ≤ _; rw [h_g]; omega
  refine ⟨_, Steps.refl s |>.snoc (Step.running h_halt
    (StepRunning.pop s a rest h_op h_gas_bd h_stack)), ?_⟩
  refine ⟨h_env, ?_, h_halt, rfl, ?_, h_active⟩
  · show (s.pc + UInt256.ofNat 1).toNat = pc_n + 1
    rw [pc_add _ _ (by rw [h_pc]; omega), h_pc]
  · show s.gasAvailable - 2 = gas_in - 2
    rw [h_g]

/-- `JUMP` at `pc_n` (1 byte, cost 8). Pops `dest` and jumps. -/
theorem jump_triple {env : ExecutionEnv} {pc_n : Nat} {dest : UInt256}
    {rest : List UInt256} {gas_in : Nat} {active : UInt256}
    (h_dec : Decode.decodeAt env.code pc_n = some (.JUMP, none))
    (h_valid : Decode.isValidJumpDest env.code dest.toNat = true)
    (h_gas : 8 ≤ gas_in) :
    Triple (StateAt env pc_n (dest :: rest) gas_in active)
           (StateAt env dest.toNat rest (gas_in - 8) active) := by
  intro s ⟨h_env, h_pc, h_halt, h_stack, h_g, h_active⟩
  have h_op : s.decodedOp = some .JUMP :=
    decodedOp_of_decodeAt h_env h_pc h_dec
  have h_gas_bd : Gas.baseCost s.fork .JUMP ≤ s.gasAvailable := by
    show 8 ≤ _; rw [h_g]; omega
  have h_valid_s : Decode.isValidJumpDest s.executionEnv.code dest.toNat = true := by
    rw [h_env]; exact h_valid
  refine ⟨_, Steps.refl s |>.snoc (Step.running h_halt
    (StepRunning.jump s dest rest h_op h_gas_bd h_stack h_valid_s)), ?_⟩
  exact ⟨h_env, rfl, h_halt, rfl,
         by show s.gasAvailable - 8 = gas_in - 8; rw [h_g], h_active⟩

/-- `JUMPI` (taken branch) at `pc_n` (1 byte, cost 10). -/
theorem jumpi_taken_triple {env : ExecutionEnv} {pc_n : Nat} {dest cond : UInt256}
    {rest : List UInt256} {gas_in : Nat} {active : UInt256}
    (h_dec : Decode.decodeAt env.code pc_n = some (.JUMPI, none))
    (h_cond : UInt256.isTrue cond)
    (h_valid : Decode.isValidJumpDest env.code dest.toNat = true)
    (h_gas : 10 ≤ gas_in) :
    Triple (StateAt env pc_n (dest :: cond :: rest) gas_in active)
           (StateAt env dest.toNat rest (gas_in - 10) active) := by
  intro s ⟨h_env, h_pc, h_halt, h_stack, h_g, h_active⟩
  have h_op : s.decodedOp = some .JUMPI :=
    decodedOp_of_decodeAt h_env h_pc h_dec
  have h_gas_bd : Gas.baseCost s.fork .JUMPI ≤ s.gasAvailable := by
    show 10 ≤ _; rw [h_g]; omega
  have h_valid_s : Decode.isValidJumpDest s.executionEnv.code dest.toNat = true := by
    rw [h_env]; exact h_valid
  refine ⟨_, Steps.refl s |>.snoc (Step.running h_halt
    (StepRunning.jumpi_taken s dest cond rest h_op h_gas_bd h_stack h_cond h_valid_s)), ?_⟩
  exact ⟨h_env, rfl, h_halt, rfl,
         by show s.gasAvailable - 10 = gas_in - 10; rw [h_g], h_active⟩

/-- `JUMPI` (not-taken branch) at `pc_n` (1 byte, cost 10). Falls through. -/
theorem jumpi_notTaken_triple {env : ExecutionEnv} {pc_n : Nat} {dest cond : UInt256}
    {rest : List UInt256} {gas_in : Nat} {active : UInt256}
    (h_pcb : pc_n + 1 < UInt256.size)
    (h_dec : Decode.decodeAt env.code pc_n = some (.JUMPI, none))
    (h_cond : ¬ UInt256.isTrue cond)
    (h_gas : 10 ≤ gas_in) :
    Triple (StateAt env pc_n (dest :: cond :: rest) gas_in active)
           (StateAt env (pc_n + 1) rest (gas_in - 10) active) := by
  intro s ⟨h_env, h_pc, h_halt, h_stack, h_g, h_active⟩
  have h_op : s.decodedOp = some .JUMPI :=
    decodedOp_of_decodeAt h_env h_pc h_dec
  have h_gas_bd : Gas.baseCost s.fork .JUMPI ≤ s.gasAvailable := by
    show 10 ≤ _; rw [h_g]; omega
  refine ⟨_, Steps.refl s |>.snoc (Step.running h_halt
    (StepRunning.jumpi_notTaken s dest cond rest h_op h_gas_bd h_stack h_cond)), ?_⟩
  refine ⟨h_env, ?_, h_halt, rfl, ?_, h_active⟩
  · show (s.pc + UInt256.ofNat 1).toNat = pc_n + 1
    rw [pc_add _ _ (by rw [h_pc]; omega), h_pc]
  · show s.gasAvailable - 10 = gas_in - 10
    rw [h_g]

/-- `MSTORE` at `pc_n` (1 byte). Specialized to `offset = 0`, `size = 32`,
    `activeWords = 0` — i.e. the first write into a fresh memory area.
    Gas delta is 6 (3 base + 3 expansion); `activeWords` goes 0 → 1. -/
theorem mstore_triple {env : ExecutionEnv} {pc_n : Nat} {value : UInt256}
    {rest : List UInt256} {gas_in : Nat}
    (h_pcb : pc_n + 1 < UInt256.size)
    (h_dec : Decode.decodeAt env.code pc_n = some (.MSTORE, none))
    (h_gas : 6 ≤ gas_in) :
    Triple
      (StateAt env pc_n (UInt256.ofNat 0 :: value :: rest) gas_in (UInt256.ofNat 0))
      (StateAt env (pc_n + 1) rest (gas_in - 6) (UInt256.ofNat 1)) := by
  intro s ⟨h_env, h_pc, h_halt, h_stack, h_g, h_active⟩
  have h_op : s.decodedOp = some .MSTORE :=
    decodedOp_of_decodeAt h_env h_pc h_dec
  have h_active_nat : s.activeWords.toNat = 0 := by rw [h_active]; rfl
  have h_total : Gas.mstoreTotal s (UInt256.ofNat 0) ≤ s.gasAvailable := by
    show Gas.baseCost s.fork .MSTORE +
         MachineState.memExpansionDelta _ _ _ ≤ _
    rw [h_active_nat, h_g]
    show 3 + 3 ≤ gas_in
    omega
  refine ⟨_, Steps.refl s |>.snoc (Step.running h_halt
    (StepRunning.mstore s (UInt256.ofNat 0) value rest h_op h_stack h_total)), ?_⟩
  refine ⟨h_env, ?_, h_halt, rfl, ?_, ?_⟩
  · show (s.pc + UInt256.ofNat 1).toNat = pc_n + 1
    rw [pc_add _ _ (by rw [h_pc]; omega), h_pc]
  · show s.gasAvailable - Gas.mstoreTotal s (UInt256.ofNat 0) = gas_in - 6
    show s.gasAvailable - (Gas.baseCost s.fork .MSTORE +
         MachineState.memExpansionDelta _ _ _) = gas_in - 6
    rw [h_active_nat, h_g]
    show gas_in - (3 + 3) = gas_in - 6
    rfl
  · show s.activeWordsAfterUInt256 (UInt256.ofNat 0).toNat 32 = UInt256.ofNat 1
    show UInt256.ofNat (MachineState.activeWordsAfter _ _ _) = UInt256.ofNat 1
    rw [h_active_nat]; rfl

/-- `RETURN` at `pc_n` (1 byte, base cost 0). Specialized to `offset = 0`,
    `size = 32` with `activeWords ≥ 1`, so the memory expansion is free.
    The post-condition is just `halt = .Returned`, since RETURN halts. -/
theorem return_triple {env : ExecutionEnv} {pc_n : Nat}
    {rest : List UInt256} {gas_in : Nat}
    (h_dec : Decode.decodeAt env.code pc_n = some (.RETURN, none)) :
    Triple
      (StateAt env pc_n (UInt256.ofNat 0 :: UInt256.ofNat 0x20 :: rest) gas_in
        (UInt256.ofNat 1))
      (fun sf => sf.halt = .Returned) := by
  intro s ⟨h_env, h_pc, h_halt, h_stack, _h_g, h_active⟩
  have h_op : s.decodedOp = some .RETURN :=
    decodedOp_of_decodeAt h_env h_pc h_dec
  have h_active_nat : s.activeWords.toNat = 1 := by rw [h_active]; rfl
  have h_total : Gas.returnTotal s (UInt256.ofNat 0) (UInt256.ofNat 0x20)
                 ≤ s.gasAvailable := by
    show Gas.baseCost s.fork .RETURN + MachineState.memExpansionDelta _ _ _ ≤ _
    rw [h_active_nat]
    show 0 + MachineState.memExpansionDelta 1 0 32 ≤ _
    show 0 ≤ _
    omega
  refine ⟨_, Steps.refl s |>.snoc (Step.running h_halt
    (StepRunning.return_ s (UInt256.ofNat 0) (UInt256.ofNat 0x20) rest
      h_op h_stack h_total)), rfl⟩

----------------------------------------------------------------------------
-- Memory-tracking triples.
--
-- A few demos (e.g. proving a program returns a specific byte sequence)
-- need to track the `memory` field through the chain so the final
-- `RETURN`'s `hReturn = readPadded memory 0 32` can be related to a
-- known byte string. The five triples below carry an extra
-- `s.memory = m` conjunct in both pre- and post-condition. JUMPDEST,
-- POP, and PUSH1 leave `m` unchanged; MSTORE writes `wordBytes value`
-- at offset 0 (specialised to the case `activeWords = 0`, the most
-- common shape in demos that compute one 32-byte result);
-- RETURN-with-memory exposes the final `hReturn` as a readPadded of
-- the carried memory.
----------------------------------------------------------------------------

/-- `CALLDATALOAD` with memory tracking. -/
theorem calldataload_triple_mem {env : ExecutionEnv} {pc_n : Nat} {i : UInt256}
    {rest : List UInt256} {gas_in : Nat} {active : UInt256} {m : ByteArray}
    (h_pcb : pc_n + 1 < UInt256.size)
    (h_dec : Decode.decodeAt env.code pc_n = some (.CALLDATALOAD, none))
    (h_gas : 3 ≤ gas_in) :
    Triple
      (fun s => StateAt env pc_n (i :: rest) gas_in active s ∧ s.memory = m)
      (fun s => StateAt env (pc_n + 1)
                  (MachineState.readWord env.calldata i.toNat :: rest)
                  (gas_in - 3) active s ∧ s.memory = m) := by
  intro s ⟨⟨h_env, h_pc, h_halt, h_stack, h_g, h_active⟩, h_mem⟩
  have h_op : s.decodedOp = some .CALLDATALOAD :=
    decodedOp_of_decodeAt h_env h_pc h_dec
  have h_gas_bd : Gas.baseCost s.fork .CALLDATALOAD ≤ s.gasAvailable := by
    show 3 ≤ _; rw [h_g]; omega
  refine ⟨_, Steps.refl s |>.snoc (Step.running h_halt
    (StepRunning.calldataload s i rest h_op h_gas_bd h_stack)),
    ⟨h_env, ?_, h_halt, ?_, ?_, h_active⟩, h_mem⟩
  · show (s.pc + UInt256.ofNat 1).toNat = pc_n + 1
    rw [pc_add _ _ (by rw [h_pc]; omega), h_pc]
  · show MachineState.readWord s.executionEnv.calldata _ :: rest = _
    rw [h_env]
  · show s.gasAvailable - 3 = gas_in - 3
    rw [h_g]

/-- `JUMPDEST` with memory tracking. -/
theorem jumpdest_triple_mem {env : ExecutionEnv} {pc_n : Nat}
    {stack : List UInt256} {gas_in : Nat} {active : UInt256} {m : ByteArray}
    (h_pcb : pc_n + 1 < UInt256.size)
    (h_dec : Decode.decodeAt env.code pc_n = some (.JUMPDEST, none))
    (h_gas : 1 ≤ gas_in) :
    Triple
      (fun s => StateAt env pc_n stack gas_in active s ∧ s.memory = m)
      (fun s => StateAt env (pc_n + 1) stack (gas_in - 1) active s ∧ s.memory = m) := by
  intro s ⟨⟨h_env, h_pc, h_halt, h_stack, h_g, h_active⟩, h_mem⟩
  have h_op : s.decodedOp = some .JUMPDEST :=
    decodedOp_of_decodeAt h_env h_pc h_dec
  have h_gas_bd : Gas.baseCost s.fork .JUMPDEST ≤ s.gasAvailable := by
    show 1 ≤ _; rw [h_g]; omega
  refine ⟨_, Steps.refl s |>.snoc (Step.running h_halt
    (StepRunning.jumpdest s h_op h_gas_bd)), ⟨h_env, ?_, h_halt, h_stack, ?_, h_active⟩, h_mem⟩
  · show (s.pc + UInt256.ofNat 1).toNat = pc_n + 1
    rw [pc_add _ _ (by rw [h_pc]; omega), h_pc]
  · show s.gasAvailable - 1 = gas_in - 1
    rw [h_g]

/-- `POP` with memory tracking. -/
theorem pop_triple_mem {env : ExecutionEnv} {pc_n : Nat} {a : UInt256}
    {rest : List UInt256} {gas_in : Nat} {active : UInt256} {m : ByteArray}
    (h_pcb : pc_n + 1 < UInt256.size)
    (h_dec : Decode.decodeAt env.code pc_n = some (.POP, none))
    (h_gas : 2 ≤ gas_in) :
    Triple
      (fun s => StateAt env pc_n (a :: rest) gas_in active s ∧ s.memory = m)
      (fun s => StateAt env (pc_n + 1) rest (gas_in - 2) active s ∧ s.memory = m) := by
  intro s ⟨⟨h_env, h_pc, h_halt, h_stack, h_g, h_active⟩, h_mem⟩
  have h_op : s.decodedOp = some .POP :=
    decodedOp_of_decodeAt h_env h_pc h_dec
  have h_gas_bd : Gas.baseCost s.fork .POP ≤ s.gasAvailable := by
    show 2 ≤ _; rw [h_g]; omega
  refine ⟨_, Steps.refl s |>.snoc (Step.running h_halt
    (StepRunning.pop s a rest h_op h_gas_bd h_stack)),
    ⟨h_env, ?_, h_halt, rfl, ?_, h_active⟩, h_mem⟩
  · show (s.pc + UInt256.ofNat 1).toNat = pc_n + 1
    rw [pc_add _ _ (by rw [h_pc]; omega), h_pc]
  · show s.gasAvailable - 2 = gas_in - 2
    rw [h_g]

/-- `PUSH1` with memory tracking. -/
theorem push1_triple_mem {env : ExecutionEnv} {pc_n : Nat} {data : UInt256}
    {rest : List UInt256} {gas_in : Nat} {active : UInt256} {m : ByteArray}
    (h_pcb : pc_n + 2 < UInt256.size)
    (h_dec : Decode.decodeAt env.code pc_n =
              some (.Push ⟨1, by decide⟩, some (data, 1)))
    (h_gas : 3 ≤ gas_in) :
    Triple
      (fun s => StateAt env pc_n rest gas_in active s ∧ s.memory = m)
      (fun s => StateAt env (pc_n + 2) (data :: rest) (gas_in - 3) active s
                ∧ s.memory = m) := by
  intro s ⟨⟨h_env, h_pc, h_halt, h_stack, h_g, h_active⟩, h_mem⟩
  have hd : s.decoded = some (.Push ⟨1, by decide⟩, some (data, 1)) :=
    decoded_of_decodeAt h_env h_pc h_dec
  have h_gas_bd : Gas.baseCost s.fork (.Push ⟨1, by decide⟩) ≤ s.gasAvailable := by
    show 3 ≤ _; rw [h_g]; omega
  refine ⟨_, Steps.refl s |>.snoc (Step.running h_halt
    (StepRunning.pushN s ⟨1, by decide⟩ data 1 (by decide) hd h_gas_bd)),
    ⟨h_env, ?_, h_halt, ?_, ?_, h_active⟩, h_mem⟩
  · show (s.pc + UInt256.ofNat 2).toNat = pc_n + 2
    rw [pc_add _ _ (by rw [h_pc]; omega), h_pc]
  · show data :: s.stack = data :: rest
    rw [h_stack]
  · show s.gasAvailable - 3 = gas_in - 3
    rw [h_g]

/-- `MSTORE` with memory tracking, specialised to `offset = 0` and
    `activeWords = 0` (the demo's only MSTORE shape). The carried memory
    is updated from `m` to `writeBytes m (wordBytes value) 0`. -/
theorem mstore_triple_mem {env : ExecutionEnv} {pc_n : Nat} {value : UInt256}
    {rest : List UInt256} {gas_in : Nat} {m : ByteArray}
    (h_pcb : pc_n + 1 < UInt256.size)
    (h_dec : Decode.decodeAt env.code pc_n = some (.MSTORE, none))
    (h_gas : 6 ≤ gas_in) :
    Triple
      (fun s => StateAt env pc_n (UInt256.ofNat 0 :: value :: rest) gas_in
                  (UInt256.ofNat 0) s ∧ s.memory = m)
      (fun s => StateAt env (pc_n + 1) rest (gas_in - 6) (UInt256.ofNat 1) s
                ∧ s.memory =
                  MachineState.writeBytes m (MachineState.wordBytes value) 0) := by
  intro s ⟨⟨h_env, h_pc, h_halt, h_stack, h_g, h_active⟩, h_mem⟩
  have h_op : s.decodedOp = some .MSTORE :=
    decodedOp_of_decodeAt h_env h_pc h_dec
  have h_active_nat : s.activeWords.toNat = 0 := by rw [h_active]; rfl
  have h_total : Gas.mstoreTotal s (UInt256.ofNat 0) ≤ s.gasAvailable := by
    show Gas.baseCost s.fork .MSTORE + MachineState.memExpansionDelta _ _ _ ≤ _
    rw [h_active_nat, h_g]
    show 3 + 3 ≤ gas_in
    omega
  refine ⟨_, Steps.refl s |>.snoc (Step.running h_halt
    (StepRunning.mstore s (UInt256.ofNat 0) value rest h_op h_stack h_total)),
    ⟨h_env, ?_, h_halt, rfl, ?_, ?_⟩, ?_⟩
  · show (s.pc + UInt256.ofNat 1).toNat = pc_n + 1
    rw [pc_add _ _ (by rw [h_pc]; omega), h_pc]
  · show s.gasAvailable - Gas.mstoreTotal s (UInt256.ofNat 0) = gas_in - 6
    show s.gasAvailable - (Gas.baseCost s.fork .MSTORE +
         MachineState.memExpansionDelta _ _ _) = gas_in - 6
    rw [h_active_nat, h_g]
    show gas_in - (3 + 3) = gas_in - 6
    rfl
  · show s.activeWordsAfterUInt256 (UInt256.ofNat 0).toNat 32 = UInt256.ofNat 1
    show UInt256.ofNat (MachineState.activeWordsAfter _ _ _) = UInt256.ofNat 1
    rw [h_active_nat]; rfl
  · show MachineState.writeBytes s.memory (MachineState.wordBytes value) 0
       = MachineState.writeBytes m (MachineState.wordBytes value) 0
    rw [h_mem]

/-- `DUPn` with memory tracking. -/
theorem dup_triple_mem {env : ExecutionEnv} {pc_n : Nat} {n : Fin 16} {v : UInt256}
    {stack : List UInt256} {gas_in : Nat} {active : UInt256} {m : ByteArray}
    (h_pcb : pc_n + 1 < UInt256.size)
    (h_dec : Decode.decodeAt env.code pc_n = some (.Dup ⟨n⟩, none))
    (h_get : stack[n.val]? = some v)
    (h_gas : 3 ≤ gas_in) :
    Triple
      (fun s => StateAt env pc_n stack gas_in active s ∧ s.memory = m)
      (fun s => StateAt env (pc_n + 1) (v :: stack) (gas_in - 3) active s ∧ s.memory = m) := by
  intro s ⟨⟨h_env, h_pc, h_halt, h_stack, h_g, h_active⟩, h_mem⟩
  have h_op : s.decodedOp = some (.Dup ⟨n⟩) :=
    decodedOp_of_decodeAt h_env h_pc h_dec
  have h_gas_bd : Gas.baseCost s.fork (.Dup ⟨n⟩) ≤ s.gasAvailable := by
    show 3 ≤ _; rw [h_g]; omega
  have h_get_s : s.stack[n.val]? = some v := by rw [h_stack]; exact h_get
  refine ⟨_, Steps.refl s |>.snoc (Step.running h_halt
    (StepRunning.dup s n v h_op h_gas_bd h_get_s)),
    ⟨h_env, ?_, h_halt, ?_, ?_, h_active⟩, h_mem⟩
  · show (s.pc + UInt256.ofNat 1).toNat = pc_n + 1
    rw [pc_add _ _ (by rw [h_pc]; omega), h_pc]
  · show v :: s.stack = v :: stack
    rw [h_stack]
  · show s.gasAvailable - 3 = gas_in - 3
    rw [h_g]

/-- `ISZERO` with memory tracking. -/
theorem iszero_triple_mem {env : ExecutionEnv} {pc_n : Nat} {a : UInt256}
    {rest : List UInt256} {gas_in : Nat} {active : UInt256} {m : ByteArray}
    (h_pcb : pc_n + 1 < UInt256.size)
    (h_dec : Decode.decodeAt env.code pc_n = some (.ISZERO, none))
    (h_gas : 3 ≤ gas_in) :
    Triple
      (fun s => StateAt env pc_n (a :: rest) gas_in active s ∧ s.memory = m)
      (fun s => StateAt env (pc_n + 1) (UInt256.isZero a :: rest) (gas_in - 3) active s
                ∧ s.memory = m) := by
  intro s ⟨⟨h_env, h_pc, h_halt, h_stack, h_g, h_active⟩, h_mem⟩
  have h_op : s.decodedOp = some .ISZERO :=
    decodedOp_of_decodeAt h_env h_pc h_dec
  have h_gas_bd : Gas.baseCost s.fork .ISZERO ≤ s.gasAvailable := by
    show 3 ≤ _; rw [h_g]; omega
  refine ⟨_, Steps.refl s |>.snoc (Step.running h_halt
    (StepRunning.iszero s a rest h_op h_gas_bd h_stack)),
    ⟨h_env, ?_, h_halt, rfl, ?_, h_active⟩, h_mem⟩
  · show (s.pc + UInt256.ofNat 1).toNat = pc_n + 1
    rw [pc_add _ _ (by rw [h_pc]; omega), h_pc]
  · show s.gasAvailable - 3 = gas_in - 3
    rw [h_g]

/-- `SWAPn` with memory tracking. -/
theorem swap_triple_mem {env : ExecutionEnv} {pc_n : Nat} {n : Fin 16}
    {stack stack' : List UInt256} {gas_in : Nat} {active : UInt256} {m : ByteArray}
    (h_pcb : pc_n + 1 < UInt256.size)
    (h_dec : Decode.decodeAt env.code pc_n = some (.Swap ⟨n⟩, none))
    (h_sw : stack.exchange 0 (n.val + 1) = some stack')
    (h_gas : 3 ≤ gas_in) :
    Triple
      (fun s => StateAt env pc_n stack gas_in active s ∧ s.memory = m)
      (fun s => StateAt env (pc_n + 1) stack' (gas_in - 3) active s ∧ s.memory = m) := by
  intro s ⟨⟨h_env, h_pc, h_halt, h_stack, h_g, h_active⟩, h_mem⟩
  have h_op : s.decodedOp = some (.Swap ⟨n⟩) :=
    decodedOp_of_decodeAt h_env h_pc h_dec
  have h_gas_bd : Gas.baseCost s.fork (.Swap ⟨n⟩) ≤ s.gasAvailable := by
    show 3 ≤ _; rw [h_g]; omega
  have h_sw_s : s.stack.exchange 0 (n.val + 1) = some stack' := by
    rw [h_stack]; exact h_sw
  refine ⟨_, Steps.refl s |>.snoc (Step.running h_halt
    (StepRunning.swap s n stack' h_op h_gas_bd h_sw_s)),
    ⟨h_env, ?_, h_halt, rfl, ?_, h_active⟩, h_mem⟩
  · show (s.pc + UInt256.ofNat 1).toNat = pc_n + 1
    rw [pc_add _ _ (by rw [h_pc]; omega), h_pc]
  · show s.gasAvailable - 3 = gas_in - 3
    rw [h_g]

/-- `ADD` with memory tracking. -/
theorem add_triple_mem {env : ExecutionEnv} {pc_n : Nat} {a b : UInt256}
    {rest : List UInt256} {gas_in : Nat} {active : UInt256} {m : ByteArray}
    (h_pcb : pc_n + 1 < UInt256.size)
    (h_dec : Decode.decodeAt env.code pc_n = some (.ADD, none))
    (h_gas : 3 ≤ gas_in) :
    Triple
      (fun s => StateAt env pc_n (a :: b :: rest) gas_in active s ∧ s.memory = m)
      (fun s => StateAt env (pc_n + 1) ((a + b) :: rest) (gas_in - 3) active s
                ∧ s.memory = m) := by
  intro s ⟨⟨h_env, h_pc, h_halt, h_stack, h_g, h_active⟩, h_mem⟩
  have h_op : s.decodedOp = some .ADD :=
    decodedOp_of_decodeAt h_env h_pc h_dec
  have h_gas_bd : Gas.baseCost s.fork .ADD ≤ s.gasAvailable := by
    show 3 ≤ _; rw [h_g]; omega
  refine ⟨_, Steps.refl s |>.snoc (Step.running h_halt
    (StepRunning.add s a b rest h_op h_gas_bd h_stack)),
    ⟨h_env, ?_, h_halt, rfl, ?_, h_active⟩, h_mem⟩
  · show (s.pc + UInt256.ofNat 1).toNat = pc_n + 1
    rw [pc_add _ _ (by rw [h_pc]; omega), h_pc]
  · show s.gasAvailable - 3 = gas_in - 3
    rw [h_g]

/-- `SUB` with memory tracking. -/
theorem sub_triple_mem {env : ExecutionEnv} {pc_n : Nat} {a b : UInt256}
    {rest : List UInt256} {gas_in : Nat} {active : UInt256} {m : ByteArray}
    (h_pcb : pc_n + 1 < UInt256.size)
    (h_dec : Decode.decodeAt env.code pc_n = some (.SUB, none))
    (h_gas : 3 ≤ gas_in) :
    Triple
      (fun s => StateAt env pc_n (a :: b :: rest) gas_in active s ∧ s.memory = m)
      (fun s => StateAt env (pc_n + 1) ((a - b) :: rest) (gas_in - 3) active s
                ∧ s.memory = m) := by
  intro s ⟨⟨h_env, h_pc, h_halt, h_stack, h_g, h_active⟩, h_mem⟩
  have h_op : s.decodedOp = some .SUB :=
    decodedOp_of_decodeAt h_env h_pc h_dec
  have h_gas_bd : Gas.baseCost s.fork .SUB ≤ s.gasAvailable := by
    show 3 ≤ _; rw [h_g]; omega
  refine ⟨_, Steps.refl s |>.snoc (Step.running h_halt
    (StepRunning.sub s a b rest h_op h_gas_bd h_stack)),
    ⟨h_env, ?_, h_halt, rfl, ?_, h_active⟩, h_mem⟩
  · show (s.pc + UInt256.ofNat 1).toNat = pc_n + 1
    rw [pc_add _ _ (by rw [h_pc]; omega), h_pc]
  · show s.gasAvailable - 3 = gas_in - 3
    rw [h_g]

/-- `JUMP` with memory tracking. -/
theorem jump_triple_mem {env : ExecutionEnv} {pc_n : Nat} {dest : UInt256}
    {rest : List UInt256} {gas_in : Nat} {active : UInt256} {m : ByteArray}
    (h_dec : Decode.decodeAt env.code pc_n = some (.JUMP, none))
    (h_valid : Decode.isValidJumpDest env.code dest.toNat = true)
    (h_gas : 8 ≤ gas_in) :
    Triple
      (fun s => StateAt env pc_n (dest :: rest) gas_in active s ∧ s.memory = m)
      (fun s => StateAt env dest.toNat rest (gas_in - 8) active s ∧ s.memory = m) := by
  intro s ⟨⟨h_env, h_pc, h_halt, h_stack, h_g, h_active⟩, h_mem⟩
  have h_op : s.decodedOp = some .JUMP :=
    decodedOp_of_decodeAt h_env h_pc h_dec
  have h_gas_bd : Gas.baseCost s.fork .JUMP ≤ s.gasAvailable := by
    show 8 ≤ _; rw [h_g]; omega
  have h_valid_s : Decode.isValidJumpDest s.executionEnv.code dest.toNat = true := by
    rw [h_env]; exact h_valid
  refine ⟨_, Steps.refl s |>.snoc (Step.running h_halt
    (StepRunning.jump s dest rest h_op h_gas_bd h_stack h_valid_s)),
    ⟨h_env, rfl, h_halt, rfl,
     by show s.gasAvailable - 8 = gas_in - 8; rw [h_g], h_active⟩, h_mem⟩

/-- `JUMPI` (taken) with memory tracking. -/
theorem jumpi_taken_triple_mem {env : ExecutionEnv} {pc_n : Nat} {dest cond : UInt256}
    {rest : List UInt256} {gas_in : Nat} {active : UInt256} {m : ByteArray}
    (h_dec : Decode.decodeAt env.code pc_n = some (.JUMPI, none))
    (h_cond : UInt256.isTrue cond)
    (h_valid : Decode.isValidJumpDest env.code dest.toNat = true)
    (h_gas : 10 ≤ gas_in) :
    Triple
      (fun s => StateAt env pc_n (dest :: cond :: rest) gas_in active s ∧ s.memory = m)
      (fun s => StateAt env dest.toNat rest (gas_in - 10) active s ∧ s.memory = m) := by
  intro s ⟨⟨h_env, h_pc, h_halt, h_stack, h_g, h_active⟩, h_mem⟩
  have h_op : s.decodedOp = some .JUMPI :=
    decodedOp_of_decodeAt h_env h_pc h_dec
  have h_gas_bd : Gas.baseCost s.fork .JUMPI ≤ s.gasAvailable := by
    show 10 ≤ _; rw [h_g]; omega
  have h_valid_s : Decode.isValidJumpDest s.executionEnv.code dest.toNat = true := by
    rw [h_env]; exact h_valid
  refine ⟨_, Steps.refl s |>.snoc (Step.running h_halt
    (StepRunning.jumpi_taken s dest cond rest h_op h_gas_bd h_stack h_cond h_valid_s)),
    ⟨h_env, rfl, h_halt, rfl,
     by show s.gasAvailable - 10 = gas_in - 10; rw [h_g], h_active⟩, h_mem⟩

/-- `JUMPI` (not-taken) with memory tracking. -/
theorem jumpi_notTaken_triple_mem {env : ExecutionEnv} {pc_n : Nat} {dest cond : UInt256}
    {rest : List UInt256} {gas_in : Nat} {active : UInt256} {m : ByteArray}
    (h_pcb : pc_n + 1 < UInt256.size)
    (h_dec : Decode.decodeAt env.code pc_n = some (.JUMPI, none))
    (h_cond : ¬ UInt256.isTrue cond)
    (h_gas : 10 ≤ gas_in) :
    Triple
      (fun s => StateAt env pc_n (dest :: cond :: rest) gas_in active s ∧ s.memory = m)
      (fun s => StateAt env (pc_n + 1) rest (gas_in - 10) active s ∧ s.memory = m) := by
  intro s ⟨⟨h_env, h_pc, h_halt, h_stack, h_g, h_active⟩, h_mem⟩
  have h_op : s.decodedOp = some .JUMPI :=
    decodedOp_of_decodeAt h_env h_pc h_dec
  have h_gas_bd : Gas.baseCost s.fork .JUMPI ≤ s.gasAvailable := by
    show 10 ≤ _; rw [h_g]; omega
  refine ⟨_, Steps.refl s |>.snoc (Step.running h_halt
    (StepRunning.jumpi_notTaken s dest cond rest h_op h_gas_bd h_stack h_cond)),
    ⟨h_env, ?_, h_halt, rfl, ?_, h_active⟩, h_mem⟩
  · show (s.pc + UInt256.ofNat 1).toNat = pc_n + 1
    rw [pc_add _ _ (by rw [h_pc]; omega), h_pc]
  · show s.gasAvailable - 10 = gas_in - 10
    rw [h_g]

/-- `RETURN` with memory tracking — exposes the final `hReturn` as a
    `readPadded` of the carried memory. -/
theorem return_triple_mem {env : ExecutionEnv} {pc_n : Nat}
    {rest : List UInt256} {gas_in : Nat} {m : ByteArray}
    (h_dec : Decode.decodeAt env.code pc_n = some (.RETURN, none)) :
    Triple
      (fun s => StateAt env pc_n (UInt256.ofNat 0 :: UInt256.ofNat 0x20 :: rest)
                  gas_in (UInt256.ofNat 1) s ∧ s.memory = m)
      (fun sf => sf.halt = .Returned ∧
        sf.hReturn = MachineState.readPadded m 0 32) := by
  intro s ⟨⟨h_env, h_pc, h_halt, h_stack, _h_g, h_active⟩, h_mem⟩
  have h_op : s.decodedOp = some .RETURN :=
    decodedOp_of_decodeAt h_env h_pc h_dec
  have h_active_nat : s.activeWords.toNat = 1 := by rw [h_active]; rfl
  have h_total : Gas.returnTotal s (UInt256.ofNat 0) (UInt256.ofNat 0x20)
                 ≤ s.gasAvailable := by
    show Gas.baseCost s.fork .RETURN + MachineState.memExpansionDelta _ _ _ ≤ _
    rw [h_active_nat]
    show 0 + MachineState.memExpansionDelta 1 0 32 ≤ _
    show 0 ≤ _
    omega
  refine ⟨_, Steps.refl s |>.snoc (Step.running h_halt
    (StepRunning.return_ s (UInt256.ofNat 0) (UInt256.ofNat 0x20) rest
      h_op h_stack h_total)), rfl, ?_⟩
  show MachineState.readPadded s.memory 0 32 = MachineState.readPadded m 0 32
  rw [h_mem]

end Hoare
end EvmSemantics
