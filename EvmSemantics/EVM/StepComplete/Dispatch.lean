module

public import EvmSemantics.EVM.StepF

/-!
`StepComplete.Dispatch` — shared evaluation lemmas for the completeness
direction (`Step s s' → stepF s = s'`, assembled in `StepDeterminism.lean`).

Where `Equiv.lean` *inverts* `stepFE`'s control flow (given the result,
recover a `Step` derivation), the completeness proofs *evaluate* it: each
`StepRunning` constructor's premises pin every branch `stepFE` takes, so
`stepFE s` reduces to a concrete outcome. The lemmas here discharge the
shared prefix of that evaluation once — the halt/precompile gates, the
decode, the stack-overflow check, and the base-fee check — so the
per-constructor proofs start directly at the per-group helper (or at the
generic error outcome for the top-level checks).
-/

@[expose] public section

namespace EvmSemantics
namespace EVM

/-- Recover the full `decoded` pair from a `decodedOp` premise: the
    op-only projection is `some op` iff `decoded` is `some (op, argOpt)`
    for some immediate slot. -/
theorem State.decodedOp_some {s : State} {op : Operation}
    (h : s.decodedOp = some op) :
    ∃ argOpt, s.decoded = some (op, argOpt) := by
  simp only [State.decodedOp, Option.map_eq_some_iff] at h
  obtain ⟨⟨op', argOpt⟩, hd, hop⟩ := h
  exact ⟨argOpt, by rw [hd]; simp at hop; rw [hop]⟩

/-- Fold a `stepFE` success into the total `stepF`. -/
theorem stepF_eq_ok {s t : State} (h : stepFE s = .ok t) : stepF s = t := by
  simp [stepF, h]

/-- Fold a `stepFE` in-frame exception into the total `stepF` (which
    reports it as `halt := .Exception e`). -/
theorem stepF_eq_error {s : State} {e : ExecutionException}
    (h : stepFE s = .error e) :
    stepF s = { s with halt := .Exception e } := by
  simp [stepF, h]

/-- Evaluate `stepFE` through its shared prefix — running frame, not a
    precompile, decode succeeded, no stack overflow, base fee affordable —
    down to the per-group helper dispatch on the base-fee-charged state. -/
theorem stepFE_dispatch {s : State} {op : Operation}
    {argOpt : Option (UInt256 × Nat)}
    (h_run : s.halt = .Running)
    (h_np : Precompile.isPrecompile s.executionEnv.fork
              s.executionEnv.codeAddr = false)
    (h_dec : s.decoded = some (op, argOpt))
    (h_cap : s.stack.length + op.pushArity ≤ 1024 + op.popArity)
    (h_g : Gas.baseCost s.fork op ≤ s.gasAvailable) :
    stepFE s =
      match op with
      | .StopArith o    => stepF.stopArith s
                             (s.consumeGas (Gas.baseCost s.fork (.StopArith o)) h_g) o
      | .CompBit o      => stepF.compBit s
                             (s.consumeGas (Gas.baseCost s.fork (.CompBit o)) h_g) o
      | .Keccak o       => stepF.keccak s
                             (s.consumeGas (Gas.baseCost s.fork (.Keccak o)) h_g) o
      | .Env o          => stepF.env s
                             (s.consumeGas (Gas.baseCost s.fork (.Env o)) h_g) o
      | .Block o        => stepF.block s
                             (s.consumeGas (Gas.baseCost s.fork (.Block o)) h_g) o
      | .StackMemFlow o => stepF.stackMemFlow s
                             (s.consumeGas (Gas.baseCost s.fork (.StackMemFlow o)) h_g) o
      | .Push o         => stepF.push s
                             (s.consumeGas (Gas.baseCost s.fork (.Push o)) h_g) o argOpt
      | .Dup o          => stepF.dup s
                             (s.consumeGas (Gas.baseCost s.fork (.Dup o)) h_g) o
      | .Swap o         => stepF.swap s
                             (s.consumeGas (Gas.baseCost s.fork (.Swap o)) h_g) o
      | .DupN o         => stepF.dupN s
                             (s.consumeGas (Gas.baseCost s.fork (.DupN o)) h_g) o
      | .SwapN o        => stepF.swapN s
                             (s.consumeGas (Gas.baseCost s.fork (.SwapN o)) h_g) o
      | .Exchange o     => stepF.exchange s
                             (s.consumeGas (Gas.baseCost s.fork (.Exchange o)) h_g) o
      | .Log o          => stepF.log s
                             (s.consumeGas (Gas.baseCost s.fork (.Log o)) h_g) o
      | .System o       => stepF.system s
                             (s.consumeGas (Gas.baseCost s.fork (.System o)) h_g) o := by
  unfold stepFE
  simp only [Id.run, h_run]
  split
  · rename_i h; rw [h_np] at h; cases h
  · simp only [h_dec]
    rw [if_neg (by omega), dif_pos h_g]
    cases op <;> rfl

/-- `stepFE` on a running, non-precompile frame whose byte fails to
    decode: `InvalidInstruction`. -/
theorem stepFE_decodeNone {s : State}
    (h_run : s.halt = .Running)
    (h_np : Precompile.isPrecompile s.executionEnv.fork
              s.executionEnv.codeAddr = false)
    (h_none : s.decoded = none) :
    stepFE s = .error .InvalidInstruction := by
  unfold stepFE
  simp only [Id.run, h_run]
  split
  · rename_i h; rw [h_np] at h; cases h
  · simp only [h_none]

/-- `stepFE` when the decoded operation trips the stack-overflow guard
    (checked before anything else): `StackOverflow`. -/
theorem stepFE_overflow {s : State} {op : Operation}
    {argOpt : Option (UInt256 × Nat)}
    (h_run : s.halt = .Running)
    (h_np : Precompile.isPrecompile s.executionEnv.fork
              s.executionEnv.codeAddr = false)
    (h_dec : s.decoded = some (op, argOpt))
    (h_over : s.stack.length + op.pushArity > 1024 + op.popArity) :
    stepFE s = .error .StackOverflow := by
  unfold stepFE
  simp only [Id.run, h_run]
  split
  · rename_i h; rw [h_np] at h; cases h
  · simp only [h_dec]
    rw [if_pos h_over]

/-- `stepFE` when the base fee itself is unaffordable (checked right
    after the overflow guard): `OutOfGas`. -/
theorem stepFE_baseOog {s : State} {op : Operation}
    {argOpt : Option (UInt256 × Nat)}
    (h_run : s.halt = .Running)
    (h_np : Precompile.isPrecompile s.executionEnv.fork
              s.executionEnv.codeAddr = false)
    (h_dec : s.decoded = some (op, argOpt))
    (h_cap : s.stack.length + op.pushArity ≤ 1024 + op.popArity)
    (h_ngas : s.gasAvailable < Gas.baseCost s.fork op) :
    stepFE s = .error .OutOfGas := by
  unfold stepFE
  simp only [Id.run, h_run]
  split
  · rename_i h; rw [h_np] at h; cases h
  · simp only [h_dec]
    rw [if_neg (by omega), dif_neg (by omega)]

end EVM
end EvmSemantics
