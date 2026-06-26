module

/-!
`Fork` — the EVM hard-fork version against which gas costs (and any
fork-conditional semantics) are computed. Threaded through the
`ExecutionEnv` so the `Step` relation and `stepF` are both parameterised
by a fork.

For now we support exactly two values:

* `Constantinople` — matches the gas accounting of the legacy
  ethereum/tests `Constantinople/VMTests` corpus (pre-EIP-1283 SSTORE,
  SLOAD = 50 — i.e. the Frontier value the legacy corpus actually uses
  rather than the Tangerine-Whistle 200).
* `Cancun` — modern EVM gas accounting (EIP-2929 cold/warm not yet
  modelled — we use warm prices everywhere).

The set is intentionally minimal; add intermediate forks as needed.
-/

@[expose] public section

namespace EvmSemantics

/-- The EVM hard-fork version. -/
inductive Fork where
  | Constantinople
  | Cancun
  deriving DecidableEq, Repr, Inhabited

end EvmSemantics
