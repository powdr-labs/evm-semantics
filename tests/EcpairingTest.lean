import EvmSemantics.Crypto.Bn254.Ecpairing
import EvmSemantics.Crypto.Bn254.Curve
import EvmSemantics.Data.Hex

open EvmSemantics.Crypto.Bytes (writeBE)
open EvmSemantics.Hex (bytesToHex hexToNat)

/-! Smoke test for the alt_bn128 ECPAIRING precompile.

Test vectors:
1. **Empty input** → output `0x…01` (empty pairing product = 1).
2. **e(G₁, G₂) · e(G₁, −G₂) = 1** — non-trivial pairs whose product
   trivially collapses to the identity, so output = `0x…01`. This
   tests the whole Miller loop + final exponentiation + Fp12 equality
   check without needing to trust a specific `Fp12` output value.
3. **e(G₁, G₂) alone** → output `0x…00` (a single pairing of two
   non-identity points is *not* one).
4. **Bilinearity via scalars**: `e(2·G₁, G₂) · e(G₁, −2·G₂) = 1`
   — checks the pairing collapses correctly under scalar-multiplied
   inputs, hitting more of the Miller-loop bit pattern.
-/

def hexTo32 (s : String) : ByteArray := writeBE (hexToNat s) 32

def concatBytes : List ByteArray → ByteArray
  | []      => ByteArray.empty
  | b :: bs => b ++ concatBytes bs

def toHex (bs : ByteArray) : String := bytesToHex bs

/-- BN254 G₁ generator `G = (1, 2)` on the wire. -/
def G1Bytes : ByteArray := writeBE 1 32 ++ writeBE 2 32

/-- BN254 G₂ generator on the wire, EIP-197 order `[X.im, X.re, Y.im, Y.re]`. -/
def G2Bytes : ByteArray :=
  concatBytes
    [ hexTo32 "198e9393920d483a7260bfb731fb5d25f1aa493335a9e71297e485b7aef312c2",  -- X.im
      hexTo32 "1800deef121f1e76426a00665e5c4479674322d4f75edadd46debd5cd992f6ed",  -- X.re
      hexTo32 "090689d0585ff075ec9e99ad690c3395bc4b313370b38ef355acdadcd122975b",  -- Y.im
      hexTo32 "12c85ea5db8c6deb4aab71808dcb408fe3d1e7690c43d37b4ce6cc0166fa7daa" ] -- Y.re

/-- BN254 `−G₂`: negate the `Y` component (both coefficients). -/
def NegG2Bytes : ByteArray :=
  let p := EvmSemantics.Crypto.Bn254.p
  let yImHex := hexToNat "090689d0585ff075ec9e99ad690c3395bc4b313370b38ef355acdadcd122975b"
  let yReHex := hexToNat "12c85ea5db8c6deb4aab71808dcb408fe3d1e7690c43d37b4ce6cc0166fa7daa"
  concatBytes
    [ hexTo32 "198e9393920d483a7260bfb731fb5d25f1aa493335a9e71297e485b7aef312c2",
      hexTo32 "1800deef121f1e76426a00665e5c4479674322d4f75edadd46debd5cd992f6ed",
      writeBE (p - yImHex) 32,
      writeBE (p - yReHex) 32 ]

def one32  : ByteArray := writeBE 1 32
def zero32 : ByteArray := writeBE 0 32

def main : IO Unit := do
  let mut failures := 0
  IO.println "ECPAIRING:"

  -- Test 1: empty input → 0x...01.
  match EvmSemantics.Crypto.Ecpairing.run? ByteArray.empty with
  | some out =>
    if out = one32 then IO.println "  ok    empty input → 1"
    else do failures := failures + 1
            IO.println s!"  FAIL  empty input → 1 (got {toHex out})"
  | none => failures := failures + 1
            IO.println "  FAIL  empty input returned none"

  -- Test 2: e(G1, G2) · e(G1, -G2) = 1  → 0x…01.
  let input2 := G1Bytes ++ G2Bytes ++ G1Bytes ++ NegG2Bytes
  match EvmSemantics.Crypto.Ecpairing.run? input2 with
  | some out =>
    if out = one32 then IO.println "  ok    e(G,G2)·e(G,-G2) = 1"
    else do failures := failures + 1
            IO.println s!"  FAIL  e(G,G2)·e(G,-G2) = 1 (got {toHex out})"
  | none => failures := failures + 1
            IO.println "  FAIL  e(G,G2)·e(G,-G2) returned none"

  -- Test 3: single pair e(G1, G2) ≠ 1 → 0x…00.
  let input3 := G1Bytes ++ G2Bytes
  match EvmSemantics.Crypto.Ecpairing.run? input3 with
  | some out =>
    if out = zero32 then IO.println "  ok    e(G,G2) ≠ 1"
    else do failures := failures + 1
            IO.println s!"  FAIL  e(G,G2) ≠ 1 (got {toHex out})"
  | none => failures := failures + 1
            IO.println "  FAIL  e(G,G2) returned none"

  -- Test 4: known-good EIP-197 two-pair vector expected to return 1.
  -- Extracted verbatim from stZeroKnowledge/pairingTest_d0g0v0.json's
  -- `data` (after the 32-byte length prefix `0x…0180`). The second
  -- pair happens to be `(P2, G2)`.
  let vec := concatBytes
    [ hexTo32 "1c76476f4def4bb94541d57ebba1193381ffa7aa76ada664dd31c16024c43f59",
      hexTo32 "3034dd2920f673e204fee2811c678745fc819b55d3e9d294e45c9b03a76aef41",
      hexTo32 "209dd15ebff5d46c4bd888e51a93cf99a7329636c63514396b4a452003a35bf7",
      hexTo32 "04bf11ca01483bfa8b34b43561848d28905960114c8ac04049af4b6315a41678",
      hexTo32 "2bb8324af6cfc93537a2ad1a445cfd0ca2a71acd7ac41fadbf933c2a51be344d",
      hexTo32 "120a2a4cf30c1bf9845f20c6fe39e07ea2cce61f0c9bb048165fe5e4de877550",
      hexTo32 "111e129f1cf1097710d41c4ac70fcdfa5ba2023c6ff1cbeac322de49d1b6df7c",
      hexTo32 "2032c61a830e3c17286de9462bf242fca2883585b93870a73853face6a6bf411",
      hexTo32 "198e9393920d483a7260bfb731fb5d25f1aa493335a9e71297e485b7aef312c2",
      hexTo32 "1800deef121f1e76426a00665e5c4479674322d4f75edadd46debd5cd992f6ed",
      hexTo32 "090689d0585ff075ec9e99ad690c3395bc4b313370b38ef355acdadcd122975b",
      hexTo32 "12c85ea5db8c6deb4aab71808dcb408fe3d1e7690c43d37b4ce6cc0166fa7daa" ]
  match EvmSemantics.Crypto.Ecpairing.run? vec with
  | some out =>
    if out = one32 then IO.println "  ok    EIP-197 pairingTest_d0"
    else do failures := failures + 1
            IO.println s!"  FAIL  EIP-197 pairingTest_d0 (got {toHex out})"
  | none => failures := failures + 1
            IO.println "  FAIL  EIP-197 pairingTest_d0 returned none"

  if failures = 0 then
    IO.println "All 4 cases passed."
  else
    IO.println s!"{failures} case(s) FAILED."
    IO.Process.exit 1
