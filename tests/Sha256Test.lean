import EvmSemantics.Crypto.Sha256
import EvmSemantics.Data.Hex

open EvmSemantics.Crypto.Sha256 (hash)
open EvmSemantics.Hex (bytesToHex)

/-! Differential test for the from-scratch SHA-256 implementation in
`EvmSemantics.Crypto.Sha256`. Confirms we match the FIPS 180-4
published test vectors as well as a couple of longer-input cases that
exercise the multi-block path. -/

/-- A million-byte `"aaaa…"` input, using `ByteArray.mk` on a `Nat.repeat`
    accumulator so the test is self-contained (no I/O). -/
def millionAs : ByteArray :=
  ByteArray.mk (Nat.repeat (fun acc => acc.push 0x61) 1000000 #[])

def vectors : List (String × ByteArray × String) :=
  -- (label, input-bytes, expected-hex)
  [ -- FIPS 180-4 §B.1 "abc"
    ( "\"abc\"", "abc".toUTF8
    , "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" )
    -- Empty input — precompile edge case: single sentinel + length in
    -- one block.
  , ( "empty", ByteArray.empty
    , "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855" )
    -- FIPS 180-4 §B.2: 56-byte input — exercises the two-final-block
    -- padding path (the sentinel spills into a second block).
  , ( "56-byte multi-block",
      "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq".toUTF8
    , "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1" )
    -- FIPS 180-4 §B.3: 1,000,000 × 'a'.
  , ( "1M a's", millionAs
    , "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0" ) ]

def main : IO UInt32 := do
  IO.println "== SHA-256 differential test =="
  let mut failed := 0
  for (label, input, expected) in vectors do
    let got := bytesToHex (hash input)
    let ok := got == expected
    if !ok then failed := failed + 1
    IO.println s!"  [{if ok then "OK  " else "FAIL"}] sha256({label})"
    IO.println s!"       got      0x{got}"
    IO.println s!"       expected 0x{expected}"
  return if failed == 0 then 0 else 1
