module

public import EvmSemantics.Data.UInt256
public import EvmSemantics.State.Account
public import EvmSemantics.EVM.Fork
public import EvmSemantics.Crypto.Sha256
public import EvmSemantics.Crypto.Ripemd160
public import EvmSemantics.Crypto.Ecrecover
public import EvmSemantics.Crypto.Ecadd
public import EvmSemantics.Crypto.Ecmul
public import EvmSemantics.Crypto.Ecpairing

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
onwards), plus `0x06 ECADD` and `0x07 ECMUL` (alt_bn128 point
addition / scalar multiplication, available from Byzantium onwards,
EIP-196; re-priced by EIP-1108 at Istanbul).
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
-- Membership predicate + dispatch.
----------------------------------------------------------------------------

/-- True iff `addr` is one of the precompile addresses *we model* in
    `fork`. Currently: ECRECOVER (`0x01`), SHA-256 (`0x02`),
    RIPEMD-160 (`0x03`), and IDENTITY (`0x04`), all available since
    Frontier. As we add precompiles, this function grows in lockstep
    with `run`'s branches; `run`'s totality proof tracks that they
    stay aligned.

    The `fork` argument is part of the signature because the YP set
    is fork-dependent — ECADD/ECMUL/ECPAIRING/MODEXP from Byzantium,
    BLAKE2F from Istanbul, KZG from Cancun, BLS12-381 from Prague. -/
def isPrecompile (fork : Fork) (addr : AccountAddress) : Bool :=
  addr = ecrecoverAddress || addr = sha256Address ||
    addr = ripemd160Address || addr = identityAddress ||
    (fork.atLeast .Byzantium &&
      (addr = ecaddAddress || addr = ecmulAddress || addr = ecpairingAddress))

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
  else if h_add : addr = ecaddAddress then
    runEcadd fork input childGas
  else if h_mul : addr = ecmulAddress then
    runEcmul fork input childGas
  else if h_pair : addr = ecpairingAddress then
    runEcpairing fork input childGas
  -- Add new precompiles here as further branches.
  else
    -- Unreachable: every `addr` for which `isPrecompile fork addr =
    -- true` is matched by a branch above. `absurd h …` discharges
    -- this case from `h` plus the negated branch guards.
    absurd h (by simp [isPrecompile, h_ec, h_sha, h_rmd, h_id, h_add, h_mul, h_pair])

end Precompile
end EVM
end EvmSemantics
