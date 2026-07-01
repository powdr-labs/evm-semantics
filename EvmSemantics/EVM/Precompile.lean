module

public import EvmSemantics.Data.UInt256
public import EvmSemantics.Data.Rlp
public import EvmSemantics.State.Account
public import EvmSemantics.Machine.MachineState
public import EvmSemantics.EVM.Fork
public import EvmSemantics.Crypto.Sha256

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

This file currently implements `0x02 SHA-256` and `0x04 IDENTITY`
(both available from Frontier onwards).
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
    zero-pads at the tail) and `MachineState.bytesToBigEndianNat`. -/
def bytesToNatPadded (bs : ByteArray) (offset width : Nat) : Nat :=
  MachineState.bytesToBigEndianNat (MachineState.readPadded bs offset width)

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
    which the caller guarantees). Delegates to `Rlp.natToBytesPadded`. -/
@[inline] def natToBytes (n width : Nat) : ByteArray :=
  Rlp.natToBytesPadded n width

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
-- Membership predicate + dispatch.
----------------------------------------------------------------------------

/-- True iff `addr` is one of the precompile addresses *we model* in
    `fork`. Currently: SHA-256 (`0x02`) and IDENTITY (`0x04`) since
    Frontier, MODEXP (`0x05`) since Byzantium (EIP-198). As we add
    precompiles, this function grows in lockstep with `run`'s
    branches; `run`'s totality proof tracks that they stay aligned. -/
def isPrecompile (fork : Fork) (addr : AccountAddress) : Bool :=
  addr = sha256Address || addr = identityAddress ||
    (fork.atLeast .Byzantium && addr = modexpAddress)

/-- Run a precompile. Total only on the subset
    `isPrecompile fork addr = true`; the hypothesis `h` discharges
    totality by guaranteeing one of the branches below matches.

    The body's branch coverage must stay in lockstep with
    `isPrecompile` — if you add a precompile in one, add it in the
    other (and the `else` discharge will keep working). -/
def run (fork : Fork) (addr : AccountAddress)
        (input : ByteArray) (childGas : Nat)
        (h : isPrecompile fork addr = true) : Result :=
  if h_sha : addr = sha256Address then
    runSha256 input childGas
  else if h_id : addr = identityAddress then
    runIdentity input childGas
  else if h_mx : fork.atLeast .Byzantium ∧ addr = modexpAddress then
    runModexp input childGas
  -- Add new precompiles here as further branches.
  else
    -- Unreachable: every `addr` for which `isPrecompile fork addr =
    -- true` is matched by a branch above. `absurd h …` discharges
    -- this case from `h` plus the negated branch guards.
    absurd h (by simp [isPrecompile, h_sha, h_id, h_mx])

end Precompile
end EVM
end EvmSemantics
