module

public import EvmSemantics.Crypto.Bls12381.Curve
public import EvmSemantics.Crypto.Bls12381.Codec
public import EvmSemantics.Crypto.Bls12381.G2Add
public import EvmSemantics.Crypto.Fp2

/-!
`EvmSemantics.Crypto.Bls12381MapFp2ToG2` — EIP-2537 `0x11
BLS12_MAP_FP2_TO_G2`: map an `Fp2` element to a point on
BLS12-381 G₂ (E': `y² = x³ + 4·(1+u)`).

Algorithm (RFC 9380 §F.2 + §8.8.2):

1. **Simplified SSWU** on the 3-isogenous curve
   `E'': y² = x³ + A'·x + B'` with the RFC 9380 §8.8.2 parameters.
2. **3-isogeny map** from `E''` to G₂ — a pair of degree-3 rational
   functions with fixed coefficient tables from RFC 9380 §J.9.2.

The `Fp2` square root is subtle because `p ≡ 3 mod 4` gives us
`sqrt_fp` easily but `sqrt_fp2` requires either a Tonelli–Shanks or
the RFC's precomputed-roots-of-unity dance. We follow py_ecc's
`sqrt_division_FQ2`: compute `γ = (uv⁷)·(uv¹⁵)^((p²−9)/16)`, then
try each of the four `ETA` roots to find the one for which
`(η·γ)²·v = u`. If none works, `u/v` isn't a square.

No cofactor clearing (EIP-2537 spec).

Gas: 23800 (EIP-2537).

All constants transcribed from
`ethereum/py_ecc/optimized_bls12_381/constants.py`.
-/

@[expose] public section

namespace EvmSemantics.Crypto.Bls12381MapFp2ToG2

open EvmSemantics.Crypto.Bls12381 (p Fp Fp2 G2Point)
open EvmSemantics.Crypto.Bls12381Codec (fp2Bytes decodeFp2)
open EvmSemantics.Crypto.Bls12381G2Add (encodePoint)

/-! ## SSWU parameters. -/

/-- `A' = 0 + 240·u` — 3-isogenous curve's `a` coefficient. -/
def isoA : Fp2 := { c0 := 0, c1 := Fin.ofNat _ 240 }

/-- `B' = 1012 + 1012·u`. -/
def isoB : Fp2 := { c0 := Fin.ofNat _ 1012, c1 := Fin.ofNat _ 1012 }

/-- `Z = −2 − u`. -/
def isoZ : Fp2 := { c0 := -Fin.ofNat _ 2, c1 := -Fin.ofNat _ 1 }

/-- `(p² − 9) / 16` — exponent for the Fp2 square-root dance. -/
def pSqMinus9Div16 : Nat :=
  1001205140483106588246484290269935788605945006208159541241399033561623546780709821462541004956387089373434649096260670658193992783731681621012512651314777238193313314641988297376025498093520728838658813979860931248214124593092835

/-! ## Eighth roots of unity and ETAS (RFC 9380 §8.8.2 auxiliaries). -/

/-- Fp component of the `(rv1, ±rv1)` positive eighth roots. -/
def rv1 : Fp := Fin.ofNat _
  1028732146235106349975324479215795277384839936929757896155643118032610843298655225875571310552543014690878354869257

/-- Fp component of the ETAS array (RFC 9380 §J.9.2). -/
def ev1 : Fp := Fin.ofNat _
  1015919005498129635886032702454337503112659152043614931979881174103627376789972962005013361970813319613593700736144
/-- Fp component of the ETAS array. -/
def ev2 : Fp := Fin.ofNat _
  1244231661155348484223428017511856347821538750986231559855759541903146219579071812422210818684355842447591283616181
/-- Fp component of the ETAS array. -/
def ev3 : Fp := Fin.ofNat _
  1646015993121829755895883253076789309308090876275172350194834453434199515639474951814226234213676147507404483718679
/-- Fp component of the ETAS array. -/
def ev4 : Fp := Fin.ofNat _
  1637752706019426886789797193293828301565549384974986623510918743054325021588194075665960171838131772227885159387073

/-- Four ETAS from RFC 9380 §J.9.2 / py_ecc constants. -/
def etas : List Fp2 :=
  [ { c0 := ev1,  c1 := ev2  },
    { c0 := -ev2, c1 := ev1  },
    { c0 := ev3,  c1 := ev4  },
    { c0 := -ev4, c1 := ev3  } ]

/-- Positive eighth roots of unity in Fp2. -/
def positiveEighthRoots : List Fp2 :=
  [ { c0 := 1,     c1 := 0    },   -- 1
    { c0 := 0,     c1 := 1    },   -- u
    { c0 := rv1,   c1 := rv1  },   -- (rv1, rv1)
    { c0 := rv1,   c1 := -rv1 } ]  -- (rv1, -rv1)

/-! ## 3-isogeny coefficients (E' → G₂). -/

/-- Common `K_1_0_VAL` value used in isoXNum[0] as `(v, v)`. -/
def k10Val : Fp := Fin.ofNat _
  889424345604814976315064405719089812568196182208668418962679585805340366775741747653930584250892369786198727235542
/-- Value for isoYNum[0] as `(v, v)`. -/
def k30Val : Fp := Fin.ofNat _
  3261222600550988246488569487636662646083386001431784202863158481286248011511053074731078808919938689216061999863558
/-- Value for isoYDen[0] as `(v, v)`. -/
def k40Val : Fp := Fin.ofNat _
  4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559355

/-- x-numerator (4 Fp2 coefficients). -/
def kXNum : List Fp2 :=
  [ { c0 := k10Val, c1 := k10Val },
    { c0 := 0
    , c1 := Fin.ofNat _
        2668273036814444928945193217157269437704588546626005256888038757416021100327225242961791752752677109358596181706522 },
    { c0 := Fin.ofNat _
        2668273036814444928945193217157269437704588546626005256888038757416021100327225242961791752752677109358596181706526
    , c1 := Fin.ofNat _
        1334136518407222464472596608578634718852294273313002628444019378708010550163612621480895876376338554679298090853261 },
    { c0 := Fin.ofNat _
        3557697382419259905260257622876359250272784728834673675850718343221361467102966990615722337003569479144794908942033
    , c1 := 0 } ]

/-- x-denominator (4 Fp2 coefficients). -/
def kXDen : List Fp2 :=
  [ { c0 := 0
    , c1 := Fin.ofNat _
        4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559715 },
    { c0 := Fin.ofNat _ 12
    , c1 := Fin.ofNat _
        4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559775 },
    { c0 := 1, c1 := 0 },
    { c0 := 0, c1 := 0 } ]

/-- y-numerator (4 Fp2 coefficients). -/
def kYNum : List Fp2 :=
  [ { c0 := k30Val, c1 := k30Val },
    { c0 := 0
    , c1 := Fin.ofNat _
        889424345604814976315064405719089812568196182208668418962679585805340366775741747653930584250892369786198727235518 },
    { c0 := Fin.ofNat _
        2668273036814444928945193217157269437704588546626005256888038757416021100327225242961791752752677109358596181706524
    , c1 := Fin.ofNat _
        1334136518407222464472596608578634718852294273313002628444019378708010550163612621480895876376338554679298090853263 },
    { c0 := Fin.ofNat _
        2816510427748580758331037284777117739799287910327449993381818688383577828123182200904113516794492504322962636245776
    , c1 := 0 } ]

/-- y-denominator (4 Fp2 coefficients). -/
def kYDen : List Fp2 :=
  [ { c0 := k40Val, c1 := k40Val },
    { c0 := 0
    , c1 := Fin.ofNat _
        4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559571 },
    { c0 := Fin.ofNat _ 18
    , c1 := Fin.ofNat _
        4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559769 },
    { c0 := 1, c1 := 0 } ]

/-! ## Algorithm. -/

/-- Horner evaluation of a polynomial over Fp2. -/
def hornerEval (coeffs : List Fp2) (x : Fp2) : Fp2 :=
  coeffs.foldr (fun c acc => acc * x + c) 0

/-- `sgn0(a)` for `Fp2`: `sgn0(c0) OR (c0 == 0 AND sgn0(c1))`. Per
    RFC 9380 §4.1. Result is 0 or 1. -/
def sgn0Fp2 (a : Fp2) : Nat :=
  let s0 := a.c0.val % 2
  let z0 := if a.c0 = 0 then 1 else 0
  let s1 := a.c1.val % 2
  Nat.max s0 (Nat.min z0 s1)  -- = s0 OR (z0 AND s1) since all are 0/1

/-- SSWU + isogeny map from Fp2 to G₂. Follows py_ecc's
    `optimized_swu_G2 + iso_map_G2` structure but affinely. -/
def sswuG2 (t : Fp2) : Fp2 × Fp2 := Id.run do
  let t2 := t^2
  let ztsq := isoZ * t2
  let ztsq2 := ztsq^2
  let tv2 := ztsq + ztsq2
  let xDen0 := -isoA * tv2
  let xDen := if xDen0 = 0 then isoZ * isoA else xDen0
  let xNum := isoB * (tv2 + 1)
  let x1 := xNum * xDen⁻¹
  let gx1 := x1^2 * x1 + isoA * x1 + isoB
  -- Compute γ = gx1 · (gx1)^((p²−9)/16). Fp2 has no simple `sqrt`
  -- like Fp does (need ETAS mechanism); brute-force scan over
  -- η · γ for η in POSITIVE_EIGHTH_ROOTS_OF_UNITY (case 1) or ETAS
  -- (case 2, when gx1 wasn't a square and we retry with x2).
  let candidate := Fp2.pow gx1 pSqMinus9Div16 * gx1
  let mut y : Fp2 := candidate
  let mut found : Bool := false
  for eta in positiveEighthRoots do
    if ! found then
      let y' := eta * candidate
      if y'^2 = gx1 then
        y := y'
        found := true
  if found then
    let yFinal := if sgn0Fp2 t = sgn0Fp2 y then y else -y
    return (x1, yFinal)
  -- Second candidate x2 = Z·t² · x1; sqrt-of-that = candidate · t³.
  let x2 := ztsq * x1
  let candidate2 := candidate * t^2 * t
  let gx2 := x2^2 * x2 + isoA * x2 + isoB
  let mut y2 : Fp2 := candidate2
  let mut found2 : Bool := false
  for eta in etas do
    if ! found2 then
      let y' := eta * candidate2
      if y'^2 = gx2 then
        y2 := y'
        found2 := true
  let yFinal := if sgn0Fp2 t = sgn0Fp2 y2 then y2 else -y2
  return (x2, yFinal)

/-- 3-isogeny map from E'' to G₂. -/
def isoMapG2 (x' y' : Fp2) : G2Point :=
  let xn := hornerEval kXNum x'
  let xd := hornerEval kXDen x'
  let yn := hornerEval kYNum x'
  let yd := hornerEval kYDen x'
  let x := xn * xd⁻¹
  let y := y' * yn * yd⁻¹
  .affine x y

/-- Full MAP_FP2_TO_G2: SSWU + 3-isogeny, then cofactor clearing `[h_eff]·P`
    (RFC 9380 §8.8.2) so the result lands in the prime-order subgroup, as
    EIP-2537's `BLS12_MAP_FP2_TO_G2` requires. -/
def mapFp2ToG2 (u : Fp2) : G2Point :=
  let (x', y') := sswuG2 u
  EvmSemantics.Crypto.G2.scalarMul
    0xbc69f08f2ee75b3584c6a0ea91b352888e2a8e9145ad7689986ff031508ffe1329c2f178731db956d82bf015d1212b02ec0ec69d7477c1ae954cbc06689f6a359894c0adebbf6b4e8020005aaa95551
    (isoMapG2 x' y')

/-- Run `0x11 BLS12_MAP_FP2_TO_G2`. -/
def run? (input : ByteArray) : Option ByteArray := do
  if input.size ≠ fp2Bytes then none
  else
    let u ← decodeFp2 input 0
    some (encodePoint (mapFp2ToG2 u))

end EvmSemantics.Crypto.Bls12381MapFp2ToG2
