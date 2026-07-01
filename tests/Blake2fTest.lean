import EvmSemantics.EVM.Precompile
import EvmSemantics.Data.Hex

open EvmSemantics.Crypto.Blake2f (compressBytes)
open EvmSemantics.EVM.Precompile (runBlake2f Result)
open EvmSemantics.Hex (hexToBytes bytesToHex)

/-! Differential test for the BLAKE2b compression function `F`
(`EvmSemantics.Crypto.Blake2f`) and the `0x09` precompile wrapper
(`EvmSemantics.EVM.Precompile.runBlake2f`), against the EIP-152 test
vectors. The flagship vector (rounds=12, "abc", f=1) reproduces the
published BLAKE2b-512("abc") digest. -/

/-- The BLAKE2b chaining state used by every EIP-152 vector: `IV`
    pre-XORed with the parameter block for a 64-byte, unkeyed digest. -/
def hHex : String :=
  "48c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5" ++
  "d182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e1319cde05b"

/-- Assemble a 213-byte BLAKE2F precompile input from its fields:
    `rounds` (4-byte big-endian), the 64-byte chaining state `hHex`,
    the message `msg` (zero-padded to 128 bytes), the two 64-bit
    little-endian counter words `t0`/`t1`, and the final-flag byte. -/
def build (rounds : Nat) (msg : ByteArray) (t0 t1 : Nat) (fFlag : UInt8) :
    ByteArray := Id.run do
  let mut out : ByteArray := .empty
  for i in [0:4] do out := out.push (UInt8.ofNat ((rounds >>> (8 * (3 - i))) &&& 0xff))
  out := out ++ hexToBytes hHex
  out := out ++ msg
  for _ in [0:128 - msg.size] do out := out.push 0
  for i in [0:8] do out := out.push (UInt8.ofNat ((t0 >>> (8 * i)) &&& 0xff))
  for i in [0:8] do out := out.push (UInt8.ofNat ((t1 >>> (8 * i)) &&& 0xff))
  out := out.push fFlag
  return out

/-- The "abc" message block used by the standard BLAKE2b test vector,
    with counter `t = 3` (three bytes absorbed). -/
def abcInput (rounds : Nat) (fFlag : UInt8) : ByteArray :=
  build rounds "abc".toUTF8 3 0 fFlag

def compressVectors : List (String × ByteArray × Nat × String) :=
  -- (label, 213-byte input, rounds, expected 64-byte output hex)
  [ -- EIP-152 vector: rounds=12, f=1 — the BLAKE2b-512("abc") digest.
    ( "rounds=12 f=1 (abc)", abcInput 12 1, 12
    , "ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d1" ++
      "7d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923" )
    -- EIP-152 vector: rounds=12, f=0.
  , ( "rounds=12 f=0", abcInput 12 0, 12
    , "75ab69d3190a562c51aef8d88f1c2775876944407270c42c9844252c26d28752" ++
      "98743e7f6d5ea2f2d3e8d226039cd31b4e426ac4f2d3d666a610c2116fde4735" )
    -- EIP-152 vector: rounds=0, f=1 — no mixing, just h ⊕ IV folding.
  , ( "rounds=0 f=1", abcInput 0 1, 0
    , "08c9bcf367e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5" ++
      "d282e6ad7f520e511f6c3e2b8c68059b9442be0454267ce079217e1319cde05b" )
    -- EIP-152 vector: rounds=1, f=1.
  , ( "rounds=1 f=1", abcInput 1 1, 1
    , "b63a380cb2897d521994a85234ee2c181b5f844d2c624c002677e9703449d2fb" ++
      "a551b3a8333bcdf5f2f7e08993d53923de3d64fcc68c034e717b9293fed7a421" ) ]

/-- Extract `(outputHex, gasUsed)` from a `.success`, or `none` on
    `.outOfGas`. -/
def resultHex : Result → Option (String × Nat)
  | .success out gas => some (bytesToHex out, gas)
  | .outOfGas => none

def main : IO UInt32 := do
  IO.println "== BLAKE2F (EIP-152) differential test =="
  let mut failed := 0
  -- Compression-function correctness (via the crypto driver directly).
  for (label, input, rounds, expected) in compressVectors do
    let got := bytesToHex (compressBytes input rounds)
    let ok := got == expected
    if !ok then failed := failed + 1
    IO.println s!"  [{if ok then "OK  " else "FAIL"}] F({label})"
    if !ok then
      IO.println s!"       got      0x{got}"
      IO.println s!"       expected 0x{expected}"
  -- Precompile wrapper: gas = rounds, success returns 64 bytes.
  let v4 := abcInput 12 1
  match resultHex (runBlake2f v4 1000) with
  | some (_, gas) =>
    let ok := gas == 12
    if !ok then failed := failed + 1
    let tag := if ok then "OK  " else "FAIL"
    IO.println s!"  [{tag}] runBlake2f charges rounds gas (got {gas}, want 12)"
  | none => failed := failed + 1; IO.println "  [FAIL] runBlake2f rounds=12 unexpectedly failed"
  -- Insufficient gas (childGas < rounds) → outOfGas.
  match resultHex (runBlake2f v4 11) with
  | none => IO.println "  [OK  ] runBlake2f OOG when childGas < rounds"
  | some _ =>
    failed := failed + 1
    IO.println "  [FAIL] runBlake2f should OOG when childGas < rounds"
  -- Malformed input: wrong length (212 bytes) → failure.
  match resultHex (runBlake2f (v4.extract 0 212) 1000) with
  | none => IO.println "  [OK  ] runBlake2f fails on wrong input length (212)"
  | some _ => failed := failed + 1; IO.println "  [FAIL] runBlake2f accepted a 212-byte input"
  -- Malformed input: final-flag byte = 2 → failure.
  match resultHex (runBlake2f (abcInput 12 2) 1000) with
  | none => IO.println "  [OK  ] runBlake2f fails on invalid final-flag byte (2)"
  | some _ => failed := failed + 1; IO.println "  [FAIL] runBlake2f accepted final-flag byte 2"
  if failed == 0 then IO.println "All BLAKE2F vectors passed."
  return if failed == 0 then 0 else 1
