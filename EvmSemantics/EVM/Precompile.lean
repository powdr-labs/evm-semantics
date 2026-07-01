module

public import EvmSemantics.Data.UInt256
public import EvmSemantics.Data.Bytes
public import EvmSemantics.Data.Rlp
public import EvmSemantics.State.Account
public import EvmSemantics.Machine.MachineState
public import EvmSemantics.EVM.Fork
public import EvmSemantics.Crypto.Sha256
public import EvmSemantics.Crypto.Ripemd160
public import EvmSemantics.Crypto.Ecrecover
public import EvmSemantics.Crypto.Ecadd
public import EvmSemantics.Crypto.Ecmul
public import EvmSemantics.Crypto.Ecpairing
public import EvmSemantics.Crypto.Blake2f
public import EvmSemantics.Crypto.Bls12381G1Add
public import EvmSemantics.Crypto.Bls12381G1Msm
public import EvmSemantics.Crypto.Bls12381G2Add
public import EvmSemantics.Crypto.Bls12381G2Msm
public import EvmSemantics.Crypto.Bls12381PairingCheck

/-!
`EvmSemantics.EVM.Precompile` — the YP §9 precompiled contracts at
addresses `0x01..0x09` (and beyond, fork-dependent).

When a CALL-family opcode targets one of these addresses, the EVM does
*not* execute bytecode (there is no code stored at the address);
instead, it invokes the corresponding native operation. From the
caller's view, the call returns either successfully (with an output
byte string and a known gas cost) or out-of-gas (no output, all
forwarded gas consumed).

This module is a closed pair:

* **`isPrecompile fork addr`** — decides, per fork, whether `addr` is
  a precompile we model. The set is fork-dependent in YP terms
  (Byzantium added ECADD/ECMUL/ECPAIRING/MODEXP; Istanbul added
  BLAKE2F; Cancun added KZG point evaluation; Prague added the
  BLS12-381 set) and is the gate `Step.running` uses to decide
  bytecode-vs-precompile dispatch.

* **`run fork addr input childGas h`** — total on the subset
  `isPrecompile fork addr = true`. The proof `h` discharges
  totality: the body's branches must cover every address for which
  `isPrecompile` returns `true`, and we hold both definitions in
  lockstep. Result is either `.success output gasUsed` (with
  `gasUsed ≤ childGas`) or `.outOfGas` (precompile cost exceeded
  `childGas`). There is **no** `.notAPrecompile` arm — the precondition
  has ruled it out.

Extending with a new precompile is a synchronized three-line edit:

1. Add a `runFoo : ByteArray → Nat → Result` implementing the
   operation's behaviour and gas cost.
2. Add `addr = fooAddress` (gated by `fork.atLeast …` if the
   precompile is fork-conditional) to `isPrecompile`.
3. Add a `if addr = fooAddress then runFoo …` branch in `run`.

This file currently implements `0x01 ECRECOVER`, `0x02 SHA-256`,
`0x03 RIPEMD-160`, and `0x04 IDENTITY` (all available from Frontier
onwards), the Byzantium+ set (`0x05 MODEXP` from EIP-198, `0x06 ECADD`
/ `0x07 ECMUL` from EIP-196, `0x08 ECPAIRING` from EIP-197 — the
alt_bn128 three re-priced by EIP-1108 at Istanbul), and `0x09
BLAKE2F` (Istanbul+, EIP-152).
-/

@[expose] public section

namespace EvmSemantics
namespace EVM
namespace Precompile

/-- Outcome of a precompile invocation. -/
inductive Result where
  /-- The precompile ran successfully. `output` is the return bytes;
      `gasUsed ≤ childGas` is the amount consumed (the caller refunds
      `childGas - gasUsed` to itself). -/
  | success (output : ByteArray) (gasUsed : Nat)
  /-- The precompile's gas requirement exceeded `childGas`. The
      CALL-family op behaves like an exceptional callee halt: push
      `0`, empty `returnData`, lose the entire `childGas`, value
      transfer (if any) is rolled back via the resume-time snapshot. -/
  | outOfGas
  deriving Inhabited

----------------------------------------------------------------------------
-- 0x01 ECRECOVER — secp256k1 ECDSA public-key recovery.
----------------------------------------------------------------------------

/-- The ECRECOVER precompile's address `0x01`. -/
def ecrecoverAddress : AccountAddress :=
  AccountAddress.ofUInt256 (UInt256.ofNat 1)

/-- ECRECOVER gas (YP §9.4.1): flat `G_ecrecover = 3000`. Unlike the
    other Frontier precompiles, the cost does *not* scale with input
    length — the input is always parsed as a 128-byte tuple, longer
    inputs are truncated and shorter ones zero-padded. -/
@[inline] def ecrecoverGas : Nat := 3000

/-- Run the `0x01 ECRECOVER` precompile. On success returns the
    32-byte padded address (12 zero bytes + 20-byte account). On any
    validation failure returns the empty byte-string but *still*
    charges the full 3000 gas — this matches the YP: the precompile
    "succeeded" in the sense that the caller doesn't OOG, it just
    returned empty. -/
def runEcrecover (input : ByteArray) (childGas : Nat) : Result :=
  if ecrecoverGas ≤ childGas then
    .success (Crypto.Ecrecover.run input) ecrecoverGas
  else .outOfGas

----------------------------------------------------------------------------
-- 0x02 SHA-256.
----------------------------------------------------------------------------

/-- The SHA-256 precompile's address `0x02`. -/
def sha256Address : AccountAddress :=
  AccountAddress.ofUInt256 (UInt256.ofNat 2)

/-- SHA-256 gas (YP §9.4.2): `G_sha256 + G_sha256word · ⌈|input|/32⌉
    = 60 + 12 · ⌈|input|/32⌉`. -/
@[inline] def sha256Gas (input : ByteArray) : Nat :=
  60 + 12 * ((input.size + 31) / 32)

/-- Run the `0x02 SHA-256` precompile: returns `SHA-256(input)` as a
    32-byte big-endian digest, consuming `sha256Gas input` gas. -/
def runSha256 (input : ByteArray) (childGas : Nat) : Result :=
  let cost := sha256Gas input
  if cost ≤ childGas then .success (Crypto.Sha256.hash input) cost
  else .outOfGas

----------------------------------------------------------------------------
-- 0x03 RIPEMD-160.
----------------------------------------------------------------------------

/-- The RIPEMD-160 precompile's address `0x03`. -/
def ripemd160Address : AccountAddress :=
  AccountAddress.ofUInt256 (UInt256.ofNat 3)

/-- RIPEMD-160 gas (YP §9.4.3): `G_ripemd + G_ripemdword · ⌈|input|/32⌉
    = 600 + 120 · ⌈|input|/32⌉`. -/
@[inline] def ripemd160Gas (input : ByteArray) : Nat :=
  600 + 120 * ((input.size + 31) / 32)

/-- Run the `0x03 RIPEMD-160` precompile: returns `RIPEMD-160(input)`
    as a 20-byte little-endian digest, zero-padded on the *left* to
    32 bytes (12 leading zeros + digest), consuming `ripemd160Gas
    input` gas. -/
def runRipemd160 (input : ByteArray) (childGas : Nat) : Result :=
  let cost := ripemd160Gas input
  if cost ≤ childGas then
    let digest := Crypto.Ripemd160.hash input
    -- Pad 12 leading zero bytes to fill the 32-byte precompile output.
    let padded : ByteArray := Id.run do
      let mut acc : ByteArray := ByteArray.empty
      for _ in [0:12] do acc := acc.push 0
      acc ++ digest
    .success padded cost
  else .outOfGas

----------------------------------------------------------------------------
-- 0x04 IDENTITY — return calldata unchanged.
----------------------------------------------------------------------------

/-- The IDENTITY precompile's address `0x04`. -/
def identityAddress : AccountAddress :=
  AccountAddress.ofUInt256 (UInt256.ofNat 4)

/-- IDENTITY gas (YP §9.4.4): `G_identity + G_identityword · ⌈|input|/32⌉
    = 15 + 3 · ⌈|input|/32⌉`. -/
@[inline] def identityGas (input : ByteArray) : Nat :=
  15 + 3 * ((input.size + 31) / 32)

/-- Run the `0x04 IDENTITY` precompile: returns `input` unchanged,
    consuming `identityGas input` gas. -/
def runIdentity (input : ByteArray) (childGas : Nat) : Result :=
  let cost := identityGas input
  if cost ≤ childGas then .success input cost else .outOfGas

----------------------------------------------------------------------------
-- 0x05 MODEXP — modular exponentiation `B^E mod M` (EIP-198, Byzantium+).
--
-- Input layout (each length field is a 32-byte big-endian integer):
--
--   [0..32)   Bsize        length of `B` in bytes
--   [32..64)  Esize        length of `E` in bytes
--   [64..96)  Msize        length of `M` in bytes
--   [96..96+Bsize)         B (base)
--   [.. +Esize)            E (exponent)
--   [.. +Msize)            M (modulus)
--
-- Missing input bytes are treated as trailing zeros (per EIP-198's
-- input-normalisation rule); this is what our `bytesToNatPadded`
-- helper does implicitly via `ByteArray.extract`.
--
-- Output: `M`-byte big-endian encoding of `B^E mod M`, or all zeros
-- of length `Msize` if `M == 0`.
--
-- Gas (Byzantium pricing, EIP-198):
--   gas = mult_complexity(max(Bsize, Msize)) * max(ADJ, 1) / 20
-- where `mult_complexity(x)` and `ADJ` follow the spec's piecewise
-- definitions (below). EIP-2565 (Berlin) reduces the divisor from
-- 20 to 3 with a different `mult_complexity`; EIP-7883 (Osaka)
-- tweaks it again. We only implement the Byzantium schedule — the
-- current corpus is Constantinople-era so nothing else fires.
----------------------------------------------------------------------------

/-- The MODEXP precompile's address `0x05`. -/
def modexpAddress : AccountAddress :=
  AccountAddress.ofUInt256 (UInt256.ofNat 5)

/-- Read `width` bytes from `bs` starting at `offset`, zero-padding
    with trailing zeros if the input is short (per EIP-198's
    input-normalisation rule), and interpret them big-endian as a
    `Nat`. Composition of `MachineState.readPadded` (which already
    zero-pads at the tail) and `Data.Bytes.bytesToBigEndianNat`. -/
def bytesToNatPadded (bs : ByteArray) (offset width : Nat) : Nat :=
  Data.Bytes.bytesToBigEndianNat (MachineState.readPadded bs offset width)

/-- Square-and-multiply modular exponentiation for arbitrary-precision
    `Nat`. `modPow b e 0 = 0` (matches YP/EIP-198's `M = 0 → zero
    output` convention when the caller propagates the modulus). -/
def modPowAux (base acc modulus e : Nat) : Nat :=
  if h : e = 0 then acc
  else
    let acc' := if e % 2 = 1 then (acc * base) % modulus else acc
    modPowAux ((base * base) % modulus) acc' modulus (e / 2)
  termination_by e
  decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

/-- `modPow b e m = b^e mod m`. Fast (square-and-multiply) exponent.
    `m = 0` returns `0` (matches EIP-198's `M = 0 → zero output`); `m
    = 1` returns `0` (every residue mod 1 is 0). Wraps `modPowAux`
    with the initial reduction `b % modulus` so the recursion never
    sees intermediate values larger than `modulus^2`. -/
def modPow (b e modulus : Nat) : Nat :=
  if modulus = 0 then 0
  else if modulus = 1 then 0
  else modPowAux (b % modulus) 1 modulus e

/-- Big-endian encoding of `n` into `width` bytes (leading zeros).
    Truncates bits above `width * 8` (unreachable for `n < 256^width`,
    which the caller guarantees). Delegates to
    `Data.Bytes.natToBytesPadded`. -/
@[inline] def natToBytes (n width : Nat) : ByteArray :=
  Data.Bytes.natToBytesPadded n width

/-- EIP-198 `mult_complexity` piecewise definition. `x` is the max of
    Bsize and Msize (in bytes). -/
def multComplexity (x : Nat) : Nat :=
  if x ≤ 64 then x * x
  else if x ≤ 1024 then x * x / 4 + 96 * x - 3072
  else x * x / 16 + 480 * x - 199680

/-- EIP-198 adjusted-exponent-length. `esize` is the exponent's byte
    length; `expHead` is the big-endian numeric value of the *first
    32 bytes* of the exponent (zero-padded at the tail if the
    exponent is shorter than 32 bytes).

    * `esize ≤ 32 ∧ expHead == 0`: `0`.
    * `esize ≤ 32`: `⌊log₂ expHead⌋` (highest set bit, 0-indexed).
    * `esize > 32 ∧ expHead == 0`: `8 * (esize - 32)`.
    * `esize > 32`: `8 * (esize - 32) + ⌊log₂ expHead⌋`. -/
def adjustedExpLen (esize expHead : Nat) : Nat :=
  if esize ≤ 32 then
    if expHead = 0 then 0 else Nat.log2 expHead
  else
    let base := 8 * (esize - 32)
    if expHead = 0 then base else base + Nat.log2 expHead

/-- Byzantium MODEXP gas cost per EIP-198: `mult_complexity(max
    Bsize Msize) * max(adjustedExpLen, 1) / 20`. -/
def modexpGas (bsize esize msize expHead : Nat) : Nat :=
  let adj := Nat.max (adjustedExpLen esize expHead) 1
  multComplexity (Nat.max bsize msize) * adj / 20

/-- Run the `0x05 MODEXP` precompile. Parses `(Bsize, Esize, Msize,
    B, E, M)` out of `input` (with EIP-198's trailing-zero
    normalisation), computes the gas cost, and — if it fits in
    `childGas` — returns `B^E mod M` as a `Msize`-byte big-endian
    output. -/
def runModexp (input : ByteArray) (childGas : Nat) : Result :=
  let bsize := bytesToNatPadded input 0 32
  let esize := bytesToNatPadded input 32 32
  let msize := bytesToNatPadded input 64 32
  -- First 32 bytes of the exponent (or fewer if `esize < 32`), used
  -- only to derive the gas cost via `adjustedExpLen`. Zero-padded at
  -- the tail if `esize < 32`.
  let expHead :=
    let n := Nat.min esize 32
    bytesToNatPadded input (96 + bsize) n
  let cost := modexpGas bsize esize msize expHead
  if cost ≤ childGas then
    -- Special YP §4.1 edge case: `Msize = 0` returns the empty byte
    -- string (no bytes to encode). This is the natural output of
    -- `modPow _ _ 0 = 0` restricted to 0 bytes.
    if msize = 0 then .success ByteArray.empty cost
    else
      let b := bytesToNatPadded input 96 bsize
      let e := bytesToNatPadded input (96 + bsize) esize
      let m := bytesToNatPadded input (96 + bsize + esize) msize
      let r := modPow b e m
      .success (natToBytes r msize) cost
  else .outOfGas

----------------------------------------------------------------------------
-- 0x06 ECADD — alt_bn128 point addition (Byzantium+, EIP-196).
----------------------------------------------------------------------------

/-- The ECADD precompile's address `0x06`. -/
def ecaddAddress : AccountAddress :=
  AccountAddress.ofUInt256 (UInt256.ofNat 6)

/-- ECADD gas: `500` at Byzantium (EIP-196), re-priced to `150` at
    Istanbul (EIP-1108) once the underlying implementations got much
    faster. Flat cost — the input is always 128 bytes after padding /
    truncation. -/
@[inline] def ecaddGas (fork : Fork) : Nat :=
  if fork.atLeast .Istanbul then 150 else 500

/-- Run the `0x06 ECADD` precompile. Invalid input (out-of-field
    coordinate or off-curve point) is treated as an EIP-196 failure:
    all `childGas` is consumed and no output is produced — modelled as
    `.outOfGas` since the caller cannot distinguish. Insufficient gas
    is also `.outOfGas`. -/
def runEcadd (fork : Fork) (input : ByteArray) (childGas : Nat) : Result :=
  let cost := ecaddGas fork
  if cost ≤ childGas then
    match Crypto.Ecadd.run? input with
    | some output => .success output cost
    | none        => .outOfGas
  else .outOfGas

----------------------------------------------------------------------------
-- 0x07 ECMUL — alt_bn128 scalar multiplication (Byzantium+, EIP-196).
----------------------------------------------------------------------------

/-- The ECMUL precompile's address `0x07`. -/
def ecmulAddress : AccountAddress :=
  AccountAddress.ofUInt256 (UInt256.ofNat 7)

/-- ECMUL gas: `40000` at Byzantium (EIP-196), re-priced to `6000` at
    Istanbul (EIP-1108). Flat cost — the input is always 96 bytes and
    the scalar loop dominates but is bounded by the 256-bit word
    width. -/
@[inline] def ecmulGas (fork : Fork) : Nat :=
  if fork.atLeast .Istanbul then 6000 else 40000

/-- Run the `0x07 ECMUL` precompile. Invalid-input handling matches
    `runEcadd`. -/
def runEcmul (fork : Fork) (input : ByteArray) (childGas : Nat) : Result :=
  let cost := ecmulGas fork
  if cost ≤ childGas then
    match Crypto.Ecmul.run? input with
    | some output => .success output cost
    | none        => .outOfGas
  else .outOfGas

----------------------------------------------------------------------------
-- 0x08 ECPAIRING — alt_bn128 optimal ate pairing check (Byzantium+, EIP-197).
----------------------------------------------------------------------------

/-- The ECPAIRING precompile's address `0x08`. -/
def ecpairingAddress : AccountAddress :=
  AccountAddress.ofUInt256 (UInt256.ofNat 8)

/-- ECPAIRING gas (EIP-197): `Base + PerPair · k` where `k` is the
    number of `(G₁, G₂)` pairs (`|input| / 192`). Byzantium:
    `Base=100000, PerPair=80000`; Istanbul re-prices via EIP-1108 to
    `Base=45000, PerPair=34000`. -/
@[inline] def ecpairingGas (fork : Fork) (input : ByteArray) : Nat :=
  let k := input.size / 192
  if fork.atLeast .Istanbul then 45000 + 34000 * k else 100000 + 80000 * k

/-- Run the `0x08 ECPAIRING` precompile. -/
def runEcpairing (fork : Fork) (input : ByteArray) (childGas : Nat) : Result :=
  let cost := ecpairingGas fork input
  if cost ≤ childGas then
    match Crypto.Ecpairing.run? input with
    | some output => .success output cost
    | none        => .outOfGas
  else .outOfGas

----------------------------------------------------------------------------
-- 0x09 BLAKE2F — BLAKE2b compression-function `F` (EIP-152, Istanbul+).
--
-- Input layout (exactly 213 bytes; any other length is a hard failure):
--
--   [0..4)      rounds   4-byte big-endian round count
--   [4..68)     h        8 little-endian 64-bit state words
--   [68..196)   m        16 little-endian 64-bit message words
--   [196..212)  t        2 little-endian 64-bit offset-counter words
--   [212]       f        1-byte final-block flag (must be 0 or 1)
--
-- Output: the 64-byte little-endian encoding of the 8 output state
-- words (the empty byte-string never occurs — the call either
-- succeeds with 64 bytes or fails).
--
-- Gas (EIP-152): `G_fround · rounds = 1 · rounds` — one gas per
-- mixing round, no base cost.
--
-- Unlike ECRECOVER/SHA-256 (which "succeed" with empty output on
-- malformed input), BLAKE2F *fails the whole call* when the input
-- length is not exactly 213 or the final-flag byte is neither 0 nor
-- 1 — the CALL returns `0` and the callee consumes all forwarded gas.
-- That observable outcome is exactly `Result.outOfGas`, so we reuse
-- it for both the genuine-OOG and the invalid-input cases.
----------------------------------------------------------------------------

/-- The BLAKE2F precompile's address `0x09`. -/
def blake2fAddress : AccountAddress :=
  AccountAddress.ofUInt256 (UInt256.ofNat 9)

/-- Exact byte length of a valid BLAKE2F input (EIP-152). -/
@[inline] def blake2fInputLength : Nat := 213

/-- Run the `0x09 BLAKE2F` precompile. Validates the fixed 213-byte
    input layout and the 0/1 final-flag byte (a violation of either
    fails the call, modelled as `.outOfGas`), charges `rounds` gas,
    and returns the 64-byte compression output. -/
def runBlake2f (input : ByteArray) (childGas : Nat) : Result :=
  if input.size ≠ blake2fInputLength then .outOfGas
  else
    let fFlag := input[212]!
    if fFlag != 0 && fFlag != 1 then .outOfGas
    else
      -- Round count = big-endian `input[0..4)`; gas = 1 · rounds.
      let rounds := Data.Bytes.bytesToBigEndianNat (input.extract 0 4)
      let cost := rounds
      if cost ≤ childGas then
        .success (Crypto.Blake2f.compressBytes input rounds) cost
      else .outOfGas

----------------------------------------------------------------------------
-- 0x0B BLS12_G1ADD — BLS12-381 G₁ point addition (Prague+, EIP-2537).
----------------------------------------------------------------------------

/-- Address `0x0B`. -/
def blsG1AddAddress : AccountAddress := AccountAddress.ofUInt256 (UInt256.ofNat 0x0b)

/-- Gas cost: flat 375 (EIP-2537). -/
@[inline] def blsG1AddGas : Nat := 375

/-- Run BLS12_G1ADD. Invalid input → all-gas-consumed. -/
def runBlsG1Add (input : ByteArray) (childGas : Nat) : Result :=
  if blsG1AddGas ≤ childGas then
    match Crypto.Bls12381G1Add.run? input with
    | some output => .success output blsG1AddGas
    | none        => .outOfGas
  else .outOfGas

----------------------------------------------------------------------------
-- 0x0D BLS12_G2ADD — BLS12-381 G₂ point addition (Prague+, EIP-2537).
----------------------------------------------------------------------------

----------------------------------------------------------------------------
-- 0x0C BLS12_G1MSM — G₁ multi-scalar multiplication (Prague+, EIP-2537).
----------------------------------------------------------------------------

/-- Address `0x0C`. -/
def blsG1MsmAddress : AccountAddress := AccountAddress.ofUInt256 (UInt256.ofNat 0x0c)

/-- Gas: `12000 · k` where `k = |input| / 160` (conservative
    flat-per-pair rate; EIP-2537 defines a discount table that
    lowers the price for larger `k`). Invalid empty input (`k = 0`)
    is rejected by the driver. -/
@[inline] def blsG1MsmGas (input : ByteArray) : Nat := 12000 * (input.size / 160)

/-- Run BLS12_G1MSM. -/
def runBlsG1Msm (input : ByteArray) (childGas : Nat) : Result :=
  let cost := blsG1MsmGas input
  if cost ≤ childGas then
    match Crypto.Bls12381G1Msm.run? input with
    | some output => .success output cost
    | none        => .outOfGas
  else .outOfGas

----------------------------------------------------------------------------
-- 0x0D BLS12_G2ADD — BLS12-381 G₂ point addition (Prague+, EIP-2537).
----------------------------------------------------------------------------

/-- Address `0x0D`. -/
def blsG2AddAddress : AccountAddress := AccountAddress.ofUInt256 (UInt256.ofNat 0x0d)

/-- Gas cost: flat 600 (EIP-2537). -/
@[inline] def blsG2AddGas : Nat := 600

/-- Run BLS12_G2ADD. -/
def runBlsG2Add (input : ByteArray) (childGas : Nat) : Result :=
  if blsG2AddGas ≤ childGas then
    match Crypto.Bls12381G2Add.run? input with
    | some output => .success output blsG2AddGas
    | none        => .outOfGas
  else .outOfGas

----------------------------------------------------------------------------
-- 0x0E BLS12_G2MSM — G₂ multi-scalar multiplication (Prague+, EIP-2537).
----------------------------------------------------------------------------

/-- Address `0x0E`. -/
def blsG2MsmAddress : AccountAddress := AccountAddress.ofUInt256 (UInt256.ofNat 0x0e)

/-- Gas: `22500 · k` where `k = |input| / 288`. Same flat-rate
    caveat as G1MSM. -/
@[inline] def blsG2MsmGas (input : ByteArray) : Nat := 22500 * (input.size / 288)

/-- Run BLS12_G2MSM. -/
def runBlsG2Msm (input : ByteArray) (childGas : Nat) : Result :=
  let cost := blsG2MsmGas input
  if cost ≤ childGas then
    match Crypto.Bls12381G2Msm.run? input with
    | some output => .success output cost
    | none        => .outOfGas
  else .outOfGas

----------------------------------------------------------------------------
-- 0x0F BLS12_PAIRING_CHECK — BLS12-381 multi-pairing (Prague+, EIP-2537).
----------------------------------------------------------------------------

/-- Address `0x0F`. -/
def blsPairingAddress : AccountAddress := AccountAddress.ofUInt256 (UInt256.ofNat 0x0f)

/-- Gas cost per EIP-2537: `32600 + 43000 · k` where `k` is the
    number of `(G₁, G₂)` pairs (`|input| / 384`). -/
@[inline] def blsPairingGas (input : ByteArray) : Nat :=
  32600 + 43000 * (input.size / 384)

/-- Run BLS12_PAIRING_CHECK. -/
def runBlsPairing (input : ByteArray) (childGas : Nat) : Result :=
  let cost := blsPairingGas input
  if cost ≤ childGas then
    match Crypto.Bls12381PairingCheck.run? input with
    | some output => .success output cost
    | none        => .outOfGas
  else .outOfGas

----------------------------------------------------------------------------
-- Membership predicate + dispatch.
----------------------------------------------------------------------------

/-- True iff `addr` is one of the precompile addresses *we model* in
    `fork`. Currently: ECRECOVER (`0x01`), SHA-256 (`0x02`),
    RIPEMD-160 (`0x03`), and IDENTITY (`0x04`) since Frontier, plus
    MODEXP (`0x05`, EIP-198), ECADD (`0x06`) / ECMUL (`0x07`)
    (EIP-196), and ECPAIRING (`0x08`, EIP-197) since Byzantium, plus
    BLAKE2F (`0x09`) since Istanbul (EIP-152). As we add precompiles,
    this function grows in lockstep with `run`'s branches; `run`'s
    totality proof tracks that they stay aligned.

    The `fork` argument is part of the signature because the YP set
    is fork-dependent — MODEXP/ECADD/ECMUL/ECPAIRING from Byzantium,
    BLAKE2F from Istanbul, KZG from Cancun, BLS12-381 from Prague. -/
def isPrecompile (fork : Fork) (addr : AccountAddress) : Bool :=
  addr = ecrecoverAddress || addr = sha256Address ||
    addr = ripemd160Address || addr = identityAddress ||
    (fork.atLeast .Byzantium &&
      (addr = modexpAddress ||
       addr = ecaddAddress || addr = ecmulAddress || addr = ecpairingAddress)) ||
    (fork.atLeast .Istanbul && addr = blake2fAddress) ||
    (fork.atLeast .Prague &&
      (addr = blsG1AddAddress || addr = blsG1MsmAddress ||
       addr = blsG2AddAddress || addr = blsG2MsmAddress ||
       addr = blsPairingAddress))

/-- Run a precompile. Total only on the subset
    `isPrecompile fork addr = true`; the hypothesis `h` discharges
    totality by guaranteeing one of the branches below matches.

    The body's branch coverage must stay in lockstep with
    `isPrecompile` — if you add a precompile in one, add it in the
    other (and the `else` discharge will keep working). -/
def run (fork : Fork) (addr : AccountAddress)
        (input : ByteArray) (childGas : Nat)
        (h : isPrecompile fork addr = true) : Result :=
  if h_ec : addr = ecrecoverAddress then
    runEcrecover input childGas
  else if h_sha : addr = sha256Address then
    runSha256 input childGas
  else if h_rmd : addr = ripemd160Address then
    runRipemd160 input childGas
  else if h_id : addr = identityAddress then
    runIdentity input childGas
  else if h_mx : fork.atLeast .Byzantium ∧ addr = modexpAddress then
    runModexp input childGas
  else if h_add : addr = ecaddAddress then
    runEcadd fork input childGas
  else if h_mul : addr = ecmulAddress then
    runEcmul fork input childGas
  else if h_pair : addr = ecpairingAddress then
    runEcpairing fork input childGas
  else if h_bl : fork.atLeast .Istanbul ∧ addr = blake2fAddress then
    runBlake2f input childGas
  else if h_bg1 : addr = blsG1AddAddress then
    runBlsG1Add input childGas
  else if h_bm1 : addr = blsG1MsmAddress then
    runBlsG1Msm input childGas
  else if h_bg2 : addr = blsG2AddAddress then
    runBlsG2Add input childGas
  else if h_bm2 : addr = blsG2MsmAddress then
    runBlsG2Msm input childGas
  else if h_bp : addr = blsPairingAddress then
    runBlsPairing input childGas
  -- Add new precompiles here as further branches.
  else
    -- Unreachable: every `addr` for which `isPrecompile fork addr =
    -- true` is matched by a branch above. `absurd h …` discharges
    -- this case from `h` plus the negated branch guards.
    absurd h (by simp [isPrecompile, h_ec, h_sha, h_rmd, h_id, h_mx,
                                     h_add, h_mul, h_pair, h_bl,
                                     h_bg1, h_bm1, h_bg2, h_bm2, h_bp])

end Precompile
end EVM
end EvmSemantics
