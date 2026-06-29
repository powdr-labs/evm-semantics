import EvmSemantics.Crypto.Keccak256
import EvmSemantics.Data.Hex

open EvmSemantics.Crypto.Keccak (hash)
open EvmSemantics.Hex (bytesToHex)

/-! Differential test for the from-scratch Keccak-256 implementation in
`EvmSemantics.Crypto.Keccak256`. Confirms we match well-known Ethereum
`keccak256` vectors. -/

def vectors : List (String × String × String) :=
  -- (label, input-as-utf8, expected-hex)
  [ -- Empty input — the canonical Ethereum `keccak256("")` constant.
    ( "empty", ""
    , "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470" )
    -- "abc"
  , ( "\"abc\"", "abc"
    , "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45" )
    -- Solidity selector seed for `transfer(address,uint256)`: the full
    -- 32-byte hash; the first four bytes (`a9059cbb`) form the selector.
  , ( "transfer(address,uint256)", "transfer(address,uint256)"
    , "a9059cbb2ab09eb219583f4a59a5d0623ade346d962bcd4e46b11da047c9049b" ) ]

def main : IO UInt32 := do
  IO.println "== Keccak256 differential test =="
  let mut failed := 0
  for (label, input, expected) in vectors do
    let bs := input.toUTF8
    let got := bytesToHex (hash bs)
    let ok := got == expected
    if !ok then failed := failed + 1
    IO.println s!"  [{if ok then "OK  " else "FAIL"}] keccak256({label})"
    IO.println s!"       got      0x{got}"
    IO.println s!"       expected 0x{expected}"
  return if failed == 0 then 0 else 1
