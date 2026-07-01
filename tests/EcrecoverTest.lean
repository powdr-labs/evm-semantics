import EvmSemantics.Crypto.Ecrecover
import EvmSemantics.Data.Hex

open EvmSemantics.Crypto.Ecrecover (run)
open EvmSemantics.Hex (bytesToHex hexToNat)

/-! Differential test for the from-scratch ECRECOVER implementation in
`EvmSemantics.Crypto.Ecrecover`. Runs the precompile against known
signature vectors and confirms the recovered address matches. -/

/-- Convert a 64-hex-char string to a 32-byte big-endian ByteArray. -/
def hexTo32 (s : String) : ByteArray := Id.run do
  let n := hexToNat s
  let mut acc : ByteArray := ByteArray.empty
  for i in [0:32] do
    let shift : Nat := 8 * (31 - i)
    acc := acc.push ((n >>> shift) &&& 0xff).toUInt8
  return acc

/-- Pack `(h, v, r, s)` into the 128-byte precompile call format. -/
def mkInput (h : String) (v : Nat) (r s : String) : ByteArray :=
  let hBytes := hexTo32 h
  -- 32-byte big-endian v: 31 zero bytes + one byte.
  let vBytes : ByteArray := Id.run do
    let mut acc : ByteArray := ByteArray.empty
    for _ in [0:31] do acc := acc.push 0
    acc.push v.toUInt8
  hBytes ++ vBytes ++ hexTo32 r ++ hexTo32 s

def vectors : List (String × ByteArray × String) :=
  -- (label, packed-input, expected-20-byte-hex)
  [ -- go-ethereum test vector. Signature over an arbitrary 32-byte hash.
    ( "go-ethereum vector A",
      mkInput
        "456e9aea5e197a1f1af7a3e85a3212fa4049a3ba34c2289b4c860fc0b0c64ef3"
        28
        "9242685bf161793cc25603c231bc2f568eb630ea16aa137d2664ac8038825608"
        "4f8ae3bd7535248d0bd448298cc2e2071e56992d0774dc340c368ae950852ada",
      "7156526fbd7a3c72969b54f64e42c10fbb768c8a" )
    -- v = 27 branch (even-y R).
  , ( "even-y (v=27)",
      mkInput
        "38d18acb67d25c8bb9942764b62f18e17054f66a817bd4295423adf9ed98873e"
        27
        "38d18acb67d25c8bb9942764b62f18e17054f66a817bd4295423adf9ed98873e"
        "789d1dd423d25f0772d2748d60f7e4b81bb14d086eba8e8e8efb6dcff8a4ae02",
      "ceaccac640adf55b2028469bd36ba501f28b699d" )
    -- Malformed v — precompile returns empty on validation failure.
    -- (32-byte hash of "abc", v = 26 which is invalid.)
  , ( "invalid v (= 26)",
      mkInput
        "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        26
        "9242685bf161793cc25603c231bc2f568eb630ea16aa137d2664ac8038825608"
        "4f8ae3bd7535248d0bd448298cc2e2071e56992d0774dc340c368ae950852ada",
      "" ) ]

def main : IO UInt32 := do
  IO.println "== ECRECOVER differential test =="
  let mut failed := 0
  for (label, input, expected) in vectors do
    let out := run input
    let got := bytesToHex out
    -- Expected is the 20-byte address; the precompile pads with 12
    -- leading zeros on success, empty on failure.
    let expectedPadded := if expected == "" then "" else
      String.mk (List.replicate 24 '0') ++ expected
    let ok := got == expectedPadded
    if !ok then failed := failed + 1
    IO.println s!"  [{if ok then "OK  " else "FAIL"}] ecrecover({label})"
    IO.println s!"       got      0x{got}"
    IO.println s!"       expected 0x{expectedPadded}"
  return if failed == 0 then 0 else 1
