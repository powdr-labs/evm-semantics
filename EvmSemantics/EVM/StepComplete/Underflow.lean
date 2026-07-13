module

public import EvmSemantics.EVM.StepComplete.Dispatch

/-!
`StepComplete.Underflow` — completeness for the generic `stackUnderflow` exception rule of
`StepRunning`: its priority premises pin `stepF`'s path to exactly this
error kind. Proven by case analysis over the decoded operation.
-/

@[expose] public section

namespace EvmSemantics
namespace EVM
namespace StepComplete

/-- If either index is out of range, `List.exchange` returns `none`
    (the direction of `Equiv.lean`'s private `exchange_eq_none_iff`
    needed here). -/
private theorem exchange_eq_none_of_le {α : Type _} {l : List α} {i j : Nat}
    (h : l.length ≤ i ∨ l.length ≤ j) : l.exchange i j = none := by
  unfold List.exchange
  rcases h with h | h
  · rw [List.getElem?_eq_none_iff.mpr h]
    rfl
  · rw [List.getElem?_eq_none_iff.mpr h]
    cases l[i]? <;> rfl

/-- `stepF.popN.go` returns `none` whenever the stack is shorter than
    the requested pop count. -/
private theorem popN_go_eq_none_of_len_lt :
    ∀ (k : Nat) (stk acc : List UInt256), stk.length < k →
      stepF.popN.go stk k acc = none := by
  intro k
  induction k with
  | zero => intro stk acc h; omega
  | succ k' ih =>
    intro stk acc h
    match stk with
    | [] => rfl
    | top :: rest =>
      unfold stepF.popN.go
      exact ih rest (top :: acc) (by simp at h; omega)

/-- `stepF.popN stk k = none` whenever `stk.length < k` (converse of the
    length invariant certified by `popN_correct`). -/
private theorem popN_eq_none_of_len_lt {stk : List UInt256} {k : Nat}
    (h : stk.length < k) : stepF.popN stk k = none := by
  unfold stepF.popN
  exact popN_go_eq_none_of_len_lt k stk [] h

/-- Reduce `Gas.totalCost` for a LOG on a two-deep stack (local copy of
    `Equiv.lean`'s private `totalCost_log`). -/
private theorem totalCost_log {s : State} (l : Operation.LogOp) {offset size : UInt256}
    {rest : List UInt256} (h : s.stack = offset :: size :: rest) :
    Gas.totalCost s (.Log l)
      = Gas.baseCost s.fork (.Log l)
        + MachineState.memExpansionDelta s.activeWords.toNat offset.toNat size.toNat
        + Gas.logDataCost size := by
  unfold Gas.totalCost; rw [h]

/-- Completeness for `StepRunning.stackUnderflow`. -/
theorem complete_stackUnderflow (s : State) (op : Operation)
        (h_op      : s.decodedOp = some op)
        (h_cap     : s.stack.length + op.pushArity ≤ 1024 + op.popArity)
        (h_gas     : Gas.baseCost s.fork op ≤ s.gasAvailable)
        (h_reach   : s.underflowReach op)
        (h_under   : s.stack.length < op.popArity)
        (h_run : s.halt = .Running)
        (h_np : Precompile.isPrecompile s.executionEnv.fork
                  s.executionEnv.codeAddr = false) :
    stepF s = ({ s with halt := .Exception .StackUnderflow })
    := by
  obtain ⟨argOpt, h_dec⟩ := State.decodedOp_some h_op
  refine stepF_eq_error ?_
  rw [stepFE_dispatch h_run h_np h_dec h_cap h_gas]
  cases op with
  | StopArith o =>
    cases o <;> simp only [stepF.stopArith] <;>
      (rcases hs : s.stack with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;>
        rw [hs] at h_under <;>
        first
          | (simp only [Operation.popArity, List.length_cons, List.length_nil] at h_under;
             omega)
          | rfl)
  | CompBit o =>
    cases o <;> simp only [stepF.compBit] <;>
      (rcases hs : s.stack with _ | ⟨_, _ | ⟨_, _⟩⟩ <;>
        rw [hs] at h_under <;>
        first
          | (simp only [Operation.popArity, List.length_cons, List.length_nil] at h_under;
             omega)
          | rfl)
  | Keccak o =>
    cases o
    simp only [stepF.keccak]
    rcases hs : s.stack with _ | ⟨_, _ | ⟨_, _⟩⟩ <;>
      rw [hs] at h_under <;>
      first
        | (simp only [Operation.popArity, List.length_cons, List.length_nil] at h_under;
           omega)
        | rfl
  | Env o =>
    cases o <;> simp only [stepF.env] <;>
      (rcases hs : s.stack with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩ <;>
        rw [hs] at h_under <;>
        first
          | (simp only [Operation.popArity, List.length_cons, List.length_nil] at h_under;
             omega)
          | rfl)
  | Block o =>
    cases o <;> simp only [stepF.block] <;>
      (rcases hs : s.stack with _ | ⟨_, _⟩ <;>
        rw [hs] at h_under <;>
        first
          | (simp only [Operation.popArity, List.length_cons, List.length_nil] at h_under;
             omega)
          | rfl)
  | StackMemFlow o =>
    cases o
    case SSTORE =>
      unfold State.underflowReach at h_reach
      obtain ⟨h_perm, h_sentry⟩ := h_reach
      have h_sentry' : Gas.sstoreSentry s.fork
          (s.consumeGas (Gas.baseCost s.fork (.StackMemFlow .SSTORE)) h_gas).gasAvailable
          = false := by
        simp only [State.consumeGas, State.fork]
        exact h_sentry
      simp only [stepF.stackMemFlow]
      rw [if_neg (by simp [h_perm]), if_neg (by simp [h_sentry'])]
      rcases hs : s.stack with _ | ⟨_, _ | ⟨_, _⟩⟩ <;>
        rw [hs] at h_under <;>
        first
          | (simp only [Operation.popArity, List.length_cons] at h_under; omega)
          | rfl
    case TSTORE =>
      unfold State.underflowReach at h_reach
      simp only [stepF.stackMemFlow]
      rw [if_neg (by simp [h_reach])]
      rcases hs : s.stack with _ | ⟨_, _ | ⟨_, _⟩⟩ <;>
        rw [hs] at h_under <;>
        first
          | (simp only [Operation.popArity, List.length_cons] at h_under; omega)
          | rfl
    all_goals
      (simp only [stepF.stackMemFlow]
       rcases hs : s.stack with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;>
         rw [hs] at h_under <;>
         first
           | (simp only [Operation.popArity, List.length_cons, List.length_nil] at h_under;
              omega)
           | rfl)
  | Push o =>
    simp only [Operation.popArity] at h_under
    omega
  | Dup o =>
    simp only [Operation.popArity] at h_under
    have h_none : s.stack[o.idx.val]? = none :=
      List.getElem?_eq_none_iff.mpr (by omega)
    simp only [stepF.dup, h_none]
    rfl
  | Swap o =>
    simp only [Operation.popArity] at h_under
    have h_ex : s.stack.exchange 0 (o.idx.val + 1) = none :=
      exchange_eq_none_of_le (Or.inr (by omega))
    simp only [stepF.swap, h_ex]
    rfl
  | DupN o =>
    simp only [Operation.popArity] at h_under
    have h_none : s.stack[o.n.val]? = none :=
      List.getElem?_eq_none_iff.mpr (by omega)
    simp only [stepF.dupN, h_none]
    rfl
  | SwapN o =>
    simp only [Operation.popArity] at h_under
    have h_ex : s.stack.exchange 0 (o.n.val + 1) = none :=
      exchange_eq_none_of_le (Or.inr (by omega))
    simp only [stepF.swapN, h_ex]
    rfl
  | Exchange o =>
    simp only [Operation.popArity] at h_under
    have h_ex : s.stack.exchange (o.n + 1) (o.m + 1) = none := by
      refine exchange_eq_none_of_le ?_
      rcases Nat.le_total (o.n + 1) (o.m + 1) with hnm | hnm
      · right
        have h_max : Nat.max (o.n + 1) (o.m + 1) = o.m + 1 := Nat.max_eq_right hnm
        omega
      · left
        have h_max : Nat.max (o.n + 1) (o.m + 1) = o.n + 1 := Nat.max_eq_left hnm
        omega
    simp only [stepF.exchange, h_ex]
    rfl
  | Log l =>
    unfold State.underflowReach at h_reach
    obtain ⟨h_perm, h_alt⟩ := h_reach
    simp only [Operation.popArity] at h_under
    simp only [stepF.log]
    rw [if_neg (by simp [h_perm])]
    rcases hs : s.stack with _ | ⟨offset, _ | ⟨size, rest⟩⟩
    · rw [hs] at h_under; rfl
    · rw [hs] at h_under; rfl
    · have h_total : Gas.totalCost s (.Log l) ≤ s.gasAvailable := by
        rcases h_alt with h2 | h2
        · rw [hs] at h2; simp only [List.length_cons] at h2; omega
        · exact h2
      rw [totalCost_log l hs] at h_total
      have h_mem : (s.consumeGas (Gas.baseCost s.fork (.Log l)) h_gas).canExpandMemory
          offset.toNat size.toNat := by
        simp only [State.canExpandMemory, State.consumeGas]
        omega
      have h_dyn : Gas.logDataCost size ≤
          ((s.consumeGas (Gas.baseCost s.fork (.Log l)) h_gas).consumeMemExp
            offset.toNat size.toNat h_mem).gasAvailable := by
        simp only [MachineState.memExpansionDelta] at h_total
        simp only [State.consumeMemExp, State.consumeGas]
        omega
      have h_pop : stepF.popN rest l.topics.val = none := by
        refine popN_eq_none_of_len_lt ?_
        rw [hs] at h_under
        simp only [List.length_cons] at h_under
        omega
      unfold chargeMem
      simp only [dif_pos h_mem, dif_pos h_dyn, h_pop]
      rfl
  | System o =>
    cases o <;> simp only [stepF.system] <;>
      (rcases hs : s.stack with
          _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩ <;>
        rw [hs] at h_under <;>
        first
          | (simp only [Operation.popArity, List.length_cons, List.length_nil] at h_under;
             omega)
          | rfl)

end StepComplete
end EVM
end EvmSemantics
