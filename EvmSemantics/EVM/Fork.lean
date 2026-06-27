module

/-!
`Fork` — the EVM hard-fork version against which gas costs (and any
fork-conditional semantics) are computed. Threaded through the
`ExecutionEnv` so the `Step` relation and `stepF` are both parameterised
by a fork.

We cover the forks present in the legacy ethereum/tests
GeneralStateTests corpus's `network` field — `Frontier`, `Homestead`,
`EIP150` (Tangerine Whistle), `EIP158` (Spurious Dragon), `Byzantium`,
`Constantinople` (with EIP-1283 net-metered SSTORE), and `Petersburg`
(= `ConstantinopleFix`, EIP-1283 reverted) — plus `Cancun` for modern
gas accounting (EIP-2929 cold/warm is *not* yet modelled — Cancun uses
warm-priced placeholders).

`Fork.atLeast a b` is the convenient `a ≥ b` ordering on the activation
sequence; gas helpers branch on this instead of writing eight `match`
arms each. The ordering is the canonical activation order on mainnet.
-/

@[expose] public section

namespace EvmSemantics

/-- The EVM hard-fork version. Listed in canonical activation order. -/
inductive Fork where
  | Frontier
  | Homestead
  | EIP150        -- Tangerine Whistle: EIP-150 gas re-pricing.
  | EIP158        -- Spurious Dragon: EIP-160 / -161 (EXP per-byte 50, empty-account semantics).
  | Byzantium     -- REVERT, RETURNDATA*, STATICCALL, etc.
  | Constantinople -- EIP-145 (SHL/SHR/SAR), EIP-1014 (CREATE2), EIP-1052 (EXTCODEHASH), EIP-1283 (net-metered SSTORE).
  | Petersburg    -- = ConstantinopleFix; reverts EIP-1283.
  | Cancun        -- Modern fork (EIP-2200 SSTORE, etc.).
  deriving DecidableEq, Repr, Inhabited

namespace Fork

/-- Ordinal position of `f` on the activation timeline (`Frontier = 0`,
    `Cancun = 7`). Used by `atLeast` for compact `fork ≥ X` checks in
    the gas helpers. -/
def toOrd : Fork → Nat
  | .Frontier        => 0
  | .Homestead       => 1
  | .EIP150          => 2
  | .EIP158          => 3
  | .Byzantium       => 4
  | .Constantinople  => 5
  | .Petersburg      => 6
  | .Cancun          => 7

/-- `a.atLeast b` iff `a` is at or after `b` on the activation timeline.
    Lets `Gas.baseCost`-style helpers say `fork.atLeast .EIP150` instead
    of pattern-matching every variant. -/
def atLeast (a b : Fork) : Bool := decide (a.toOrd ≥ b.toOrd)

end Fork

end EvmSemantics

