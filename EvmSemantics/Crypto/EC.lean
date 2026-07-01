module

/-!
`EvmSemantics.Crypto.EC` — the curve-agnostic `Point` type used by
both secp256k1 (via `Crypto.Secp256k1`) and BN254 (via `Crypto.Bn254`).

`Point F` is polymorphic in the coordinate type: `F` is instantiated
to `FF Secp256k1.p` for secp256k1's `G₁`, to `FF Bn254.p` for BN254's
`G₁`, and to `Fp2` for BN254's `G₂`. Field arithmetic lives in
`Crypto.FF`, curve operations (`doublePoint`, `addPoint`, `scalarMul`,
…) also live in `Crypto.FF` — they consume `FF p` coordinates via a
`Curve p` value.

This file used to host the modular-arithmetic helpers and the
Weierstrass operations. They all moved to `Crypto.FF` when we baked
the modulus into the coordinate type; `Point` is the sole survivor
because it doesn't care about the underlying field.
-/

@[expose] public section

namespace EvmSemantics.Crypto.EC

/-- A short-Weierstrass point in affine coordinates, or infinity.

    Parametric in the coordinate type so the same inductive can hold
    a G₁ point over `F_p` (`F = FF p`) or a G₂ point over `F_p²`
    (`F = Fp2`). -/
inductive Point (F : Type) where
  | infinity
  | affine (x y : F)
  deriving Inhabited

end EvmSemantics.Crypto.EC
