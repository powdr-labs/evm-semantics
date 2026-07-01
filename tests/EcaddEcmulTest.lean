import EvmSemantics.Crypto.Bn254.Ecadd
import EvmSemantics.Crypto.Bn254.Ecmul
import EvmSemantics.Crypto.Bn254.Curve
import EvmSemantics.Data.Hex

open EvmSemantics.Crypto.Bytes (writeBE)
open EvmSemantics.Crypto.Bn254 (p)
open EvmSemantics.Hex (bytesToHex hexToNat)

/-! Differential smoke test for the alt_bn128 precompiles
`0x06 ECADD` and `0x07 ECMUL`.

Runs a handful of known-good EIP-196 vectors (well-formed inputs from
geth's test suite) plus internal self-consistency checks:

* `ECADD(∞, P) = P` and `ECADD(P, −P) = ∞`.
* `ECMUL(P, 0) = ∞`, `ECMUL(P, 1) = P`.
* `ECMUL(P, 2) = ECADD(P, P)`.

Each check either succeeds silently or `IO.println`s a mismatch, and
the process exits non-zero on any failure. -/

/-- Convert a 64-hex-char string to a 32-byte big-endian ByteArray. -/
def hexTo32 (s : String) : ByteArray := writeBE (hexToNat s) 32

/-- Concatenate a variadic list of `ByteArray`s left-to-right. -/
def concatBytes : List ByteArray → ByteArray
  | []      => ByteArray.empty
  | b :: bs => b ++ concatBytes bs

/-- Pretty-hex of a `ByteArray`. -/
def toHex (bs : ByteArray) : String := bytesToHex bs

/-- The BN254 generator `G = (1, 2)` encoded as 64 wire bytes. -/
def Gbytes : ByteArray := writeBE 1 32 ++ writeBE 2 32

structure Case where
  label    : String
  input    : ByteArray
  expected : ByteArray

/-- Test framework: run `runF input`; compare to `expected`; return
    number of failures. -/
def runCases (runF : ByteArray → Option ByteArray) (cases : List Case) : IO Nat := do
  let mut failures := 0
  for c in cases do
    match runF c.input with
    | some got =>
      if got == c.expected then
        IO.println s!"  ok    {c.label}"
      else
        failures := failures + 1
        IO.println s!"  FAIL  {c.label}"
        IO.println s!"        expected {toHex c.expected}"
        IO.println s!"        got      {toHex got}"
    | none =>
      failures := failures + 1
      IO.println s!"  FAIL  {c.label} (returned none)"
  return failures

/-- ECADD vectors. -/
def ecaddCases : List Case :=
  let G     := Gbytes
  let infty := writeBE 0 32 ++ writeBE 0 32
  let negG  := writeBE 1 32 ++ writeBE (p - 2) 32
  [ -- EIP-196 / geth vector: two non-trivial curve points added.
    { label := "geth chfast_add",
      input := concatBytes
        [ hexTo32 "18b18acfb4c2c30276db5411368e7185b311dd124691610c5d3b74034e093dc9",
          hexTo32 "063c909c4720840cb5134cb9f59fa749755796819658d32efc0d288198f37266",
          hexTo32 "07c2b7f58a84bd6145f00c9c2bc0bb1a187f20ff2c92963a88019e7c6a014eed",
          hexTo32 "06614e20c147e940f2d70da3f74c9a17df361706a4485c742bd6788478fa17d7" ],
      expected := concatBytes
        [ hexTo32 "2243525c5efd4b9c3d3c45ac0ca3fe4dd85e830a4ce6b65fa1eeaee202839703",
          hexTo32 "301d1d33be6da8e509df21cc35964723180eed7532537db9ae5e7d48f195c915" ] },
    -- Identity: ∞ + G = G.
    { label := "infinity + G = G", input := infty ++ G, expected := G },
    -- Identity: G + ∞ = G.
    { label := "G + infinity = G", input := G ++ infty, expected := G },
    -- Inverse: G + (−G) = ∞.
    { label := "G + (-G) = infinity",
      input := G ++ negG,
      expected := writeBE 0 32 ++ writeBE 0 32 } ]

/-- ECMUL vectors. -/
def ecmulCases : List Case :=
  let G   := Gbytes
  let inf := writeBE 0 32 ++ writeBE 0 32
  [ -- EIP-196 / geth vector: scalar multiplication of a non-trivial point.
    { label := "geth chfast_mul",
      input := concatBytes
        [ hexTo32 "2bd3e6d0f3b142924f5ca7b49ce5b9d54c4703d7ae5648e61d02268b1a0a9fb7",
          hexTo32 "21611ce0a6af85915e2f1d70300909ce2e49dfad4a4619c8390cae66cefdb204",
          hexTo32 "00000000000000000000000000000000000000000000000011138ce750fa15c2" ],
      expected := concatBytes
        [ hexTo32 "070a8d6a982153cae4be29d434e8faef8a47b274a053f5a4ee2a6c9c13c31e5c",
          hexTo32 "031b8ce914eba3a9ffb989f9cdd5b0f01943074bf4f0f315690ec3cec6981afc" ] },
    { label := "G * 0 = infinity", input := G ++ writeBE 0 32, expected := inf },
    { label := "G * 1 = G", input := G ++ writeBE 1 32, expected := G } ]

def main : IO Unit := do
  IO.println "ECADD:"
  let f1 ← runCases EvmSemantics.Crypto.Ecadd.run? ecaddCases
  IO.println "ECMUL:"
  let f2 ← runCases EvmSemantics.Crypto.Ecmul.run? ecmulCases
  -- Cross-check: ECMUL(G, 2) = ECADD(G, G).
  IO.println "Cross-check:"
  let m := EvmSemantics.Crypto.Ecmul.run? (Gbytes ++ writeBE 2 32)
  let a := EvmSemantics.Crypto.Ecadd.run? (Gbytes ++ Gbytes)
  let cross ← if m = a then do IO.println "  ok    ECMUL(G,2) = ECADD(G,G)"; pure 0
              else do IO.println "  FAIL  ECMUL(G,2) ≠ ECADD(G,G)"; pure 1
  let total := f1 + f2 + cross
  if total = 0 then
    IO.println s!"All {ecaddCases.length + ecmulCases.length + 1} cases passed."
  else
    IO.println s!"{total} case(s) FAILED."
    IO.Process.exit 1
