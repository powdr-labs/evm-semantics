module

/-!
`EvmSemantics.Crypto.EC` — the curve-agnostic `Point` type used by
both secp256k1 (via `Crypto.Secp256k1`) and BN254 (via `Crypto.Bn254`).

`Point F` is polymorphic in the coordinate type: `F` is instantiated
to `Fin Secp256k1.p` for secp256k1's `G₁`, to `Fin Bn254.p` for
BN254's `G₁`. (BN254's `G₂` points live in `Crypto.G2` with `Fp2`
coordinates and their own inductive — the two curves' points don't
currently share this container.)

Field-arithmetic extensions to `Fin p` (`Inv` / `HPow` / `sqrt`) live
in `Crypto.FF`. The curve operations that consume them — `Curve p`,
`doublePoint`, `addPoint`, `scalarMul`, `decompress`, … — live in
`Crypto.Weierstrass`.
-/

@[expose] public section

namespace EvmSemantics.Crypto.EC

/-- A short-Weierstrass point in affine coordinates, or infinity.

    Parametric in the coordinate type so the same inductive can hold
    a G₁ point over `F_p` (`F = Fin p`) or a G₂ point over `F_p²`
    (`F = Fp2`). -/
inductive Point (F : Type) where
  | infinity
  | affine (x y : F)
  deriving Inhabited

end EvmSemantics.Crypto.EC
