import EvmSemantics.Crypto.Ripemd160
import EvmSemantics.Data.Hex

open EvmSemantics.Crypto.Ripemd160 (hash)
open EvmSemantics.Hex (bytesToHex)

/-! Differential test for the from-scratch RIPEMD-160 implementation
in `EvmSemantics.Crypto.Ripemd160`. Confirms we match the six
published Dobbertin/Bosselaers/Preneel test vectors and one longer
multi-block case. -/

/-- A million-byte `"aaaa…"` input, exercising the multi-block driver
    over ~15,625 compression rounds. -/
def millionAs : ByteArray :=
  ByteArray.mk (Nat.repeat (fun acc => acc.push 0x61) 1000000 #[])

def vectors : List (String × ByteArray × String) :=
  -- (label, input-bytes, expected-hex)
  [ ( "empty", ByteArray.empty
    , "9c1185a5c5e9fc54612808977ee8f548b2258d31" )
  , ( "\"a\"", "a".toUTF8
    , "0bdc9d2d256b3ee9daae347be6f4dc835a467ffe" )
  , ( "\"abc\"", "abc".toUTF8
    , "8eb208f7e05d987a9b044a8e98c6b087f15a0bfc" )
  , ( "\"message digest\"", "message digest".toUTF8
    , "5d0689ef49d2fae572b881b123a85ffa21595f36" )
  , ( "a–z", "abcdefghijklmnopqrstuvwxyz".toUTF8
    , "f71c27109c692c1b56bbdceb5b9d2865b3708dbc" )
  , ( "A–Z + a–z + 0–9",
      "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789".toUTF8
    , "b0e20b6e3116640286ed3a87a5713079b21f5189" )
  , ( "1M a's", millionAs
    , "52783243c1697bdbe16d37f97f68f08325dc1528" ) ]

def main : IO UInt32 := do
  IO.println "== RIPEMD-160 differential test =="
  let mut failed := 0
  for (label, input, expected) in vectors do
    let got := bytesToHex (hash input)
    let ok := got == expected
    if !ok then failed := failed + 1
    IO.println s!"  [{if ok then "OK  " else "FAIL"}] ripemd160({label})"
    IO.println s!"       got      0x{got}"
    IO.println s!"       expected 0x{expected}"
  return if failed == 0 then 0 else 1
