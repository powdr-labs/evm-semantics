import EvmSemantics.EVM.Operation

/-!
`Gas` — the gas-cost function used by the step relation.

For v1 we model uniform cost: every opcode costs exactly 1 unit. This is
not faithful to the Yellow Paper fee schedule, but it preserves the
*shape* of the relation: the `OutOfGas` rule still fires when gas is
exhausted, and proofs that quantify over gas consumption still type-check.
Swapping in the real Yellow Paper schedule later is local to this file.
-/

namespace EvmSemantics
namespace EVM

/-- Gas cost of executing one instance of `op`. The operand is
    intentionally ignored in v1 — every opcode costs `1` uniformly.
    (The `unusedArguments` linter is silenced via `scripts/nolints.json`.) -/
def Gas.cost (_op : Operation) : Nat := 1

end EVM
end EvmSemantics
