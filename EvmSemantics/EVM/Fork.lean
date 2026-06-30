module

/-!
`Fork` — the EVM hard-fork version against which gas costs (and any
fork-conditional semantics) are computed. Threaded through the
`ExecutionEnv` so the `Step` relation and `stepF` are both parameterised
by a fork.

We cover the forks present in the legacy ethereum/tests
GeneralStateTests corpus's `network` field — `Frontier`, `Homestead`,
`TangerineWhistle` (Tangerine Whistle), `SpuriousDragon` (Spurious Dragon), `Byzantium`,
`Constantinople` (with EIP-1283 net-metered SSTORE), and `Petersburg`
(= `ConstantinopleFix`, EIP-1283 reverted) — through `Cancun`. EIP-2929
cold/warm access lists are *not* yet modelled — Cancun uses warm-priced
placeholders.

`Fork.atLeast a b` is the convenient `a ≥ b` ordering on the activation
sequence; gas helpers branch on this instead of writing many `match`
arms each. The ordering is the canonical activation order on mainnet.
-/

@[expose] public section

namespace EvmSemantics

/-- The EVM hard-fork version. Listed in canonical activation order.

    Per-constructor EIPs of note:
    * `TangerineWhistle`: EIP-150 (gas re-pricing).
    * `SpuriousDragon`: EIP-160 (`EXP` per-byte 50), EIP-161 (empty-account
      semantics).
    * `Byzantium`: `REVERT`, `RETURNDATA*`, `STATICCALL`, …
    * `Constantinople`: EIP-145 (`SHL`/`SHR`/`SAR`), EIP-1014 (`CREATE2`),
      EIP-1052 (`EXTCODEHASH`), EIP-1283 (net-metered SSTORE).
    * `Petersburg` (= `ConstantinopleFix`): reverts EIP-1283.
    * `Istanbul`: EIP-1344 (`CHAINID`), EIP-1884 (re-pricing +
      `SELFBALANCE`), EIP-2028 (calldata 16), EIP-2200 (net-metered
      SSTORE).
    * `MuirGlacier`: difficulty-bomb delay only — semantically identical
      to `Istanbul` for the EVM.
    * `Berlin`: EIP-2929 (cold/warm access lists), EIP-2718 (typed-tx
      envelope).
    * `London`: EIP-1559 (base fee), EIP-3198 (`BASEFEE`), EIP-3529
      (reduced refunds, no `SELFDESTRUCT` refund), EIP-3541 (reject
      `0xEF` code).
    * `ArrowGlacier` / `GrayGlacier`: difficulty-bomb delays only.
    * `Paris` (The Merge): EIP-3675 (PoS finality), EIP-4399
      (`PREVRANDAO` replaces `DIFFICULTY`); block reward = 0.
    * `Shanghai`: EIP-3651 (warm coinbase), EIP-3855 (`PUSH0`),
      EIP-3860 (init-code limit), EIP-4895 (withdrawals).
    * `Cancun`: EIP-1153 (transient storage), EIP-4844 (blob tx +
      `BLOBHASH`), EIP-5656 (`MCOPY`), EIP-6780 (`SELFDESTRUCT`-same-tx),
      EIP-7516 (`BLOBBASEFEE`).
    * `Prague` (Pectra, mainnet 2025-05-07): EIP-7702 (EOA delegation),
      EIP-2537 (BLS12-381 precompiles), EIP-2935 (`BLOCKHASH` history),
      EIP-6110 (deposit log), EIP-7251 (effective-balance cap raised),
      EIP-7549 (committee dedup), EIP-7691 (blob count up to 6/9).
    * `Osaka` (Fusaka, post-Prague): EIP-7594 (PeerDAS), EIP-7825 (per-tx
      gas cap), EIP-7823 (modexp upper bound), EIP-7883 (modexp
      re-pricing), EIP-7918 (blob base-fee floor), EIP-7935 (gas-limit
      raise). -/
inductive Fork where
  | Frontier | Homestead | TangerineWhistle | SpuriousDragon
  | Byzantium | Constantinople | Petersburg
  | Istanbul | MuirGlacier | Berlin | London
  | ArrowGlacier | GrayGlacier | Paris | Shanghai | Cancun
  | Prague | Osaka
  deriving DecidableEq, Repr, Inhabited

namespace Fork

/-- Ordinal position of `f` on the activation timeline. Used by
    `atLeast` for compact `fork ≥ X` checks in the gas helpers. -/
def toOrd : Fork → Nat
  | .Frontier        => 0
  | .Homestead       => 1
  | .TangerineWhistle          => 2
  | .SpuriousDragon          => 3
  | .Byzantium       => 4
  | .Constantinople  => 5
  | .Petersburg      => 6
  | .Istanbul        => 7
  | .MuirGlacier     => 8
  | .Berlin          => 9
  | .London          => 10
  | .ArrowGlacier    => 11
  | .GrayGlacier     => 12
  | .Paris           => 13
  | .Shanghai        => 14
  | .Cancun          => 15
  | .Prague          => 16
  | .Osaka           => 17

/-- `a.atLeast b` iff `a` is at or after `b` on the activation timeline.
    Lets `Gas.baseCost`-style helpers say `fork.atLeast .TangerineWhistle` instead
    of pattern-matching every variant. -/
def atLeast (a b : Fork) : Bool := decide (a.toOrd ≥ b.toOrd)

end Fork

end EvmSemantics
