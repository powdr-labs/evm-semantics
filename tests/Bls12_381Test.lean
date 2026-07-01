import EvmSemantics.Crypto.Bls12_381_Pairing

open EvmSemantics.Crypto.Bls12_381 (G G2 addPoint)
open EvmSemantics.Crypto.G2 (negate)
open EvmSemantics.Crypto.Bls12_381_Pairing (pairing multiPairing)

/-! Smoke test for the BLS12-381 optimal ate pairing.

We check the two structural identities that any correct pairing
must satisfy — no reliance on a specific `Fp12` hex value:

1. `e(∞, G₂) = 1` and `e(G₁, ∞) = 1` — infinity annihilates.
2. `e(G₁, G₂) · e(G₁, −G₂) = 1` — pairs of inputs cancelling
   under bilinearity.
3. `e(G₁, G₂) ≠ 1` — the pairing is non-degenerate.

Passing (2) with the untwist / Miller loop / final exponentiation
all correct is a strong signal — a Miller loop with a bug in any
of those parts fails this identity. -/

def main : IO Unit := do
  let mut failures := 0

  -- Test 1a: e(∞, G₂) = 1.
  let r1a := pairing .infinity G2
  if r1a == 1 then IO.println "  ok    e(∞, G₂) = 1"
  else do failures := failures + 1
          IO.println "  FAIL  e(∞, G₂) ≠ 1"

  -- Test 1b: e(G₁, ∞) = 1.
  let r1b := pairing G .infinity
  if r1b == 1 then IO.println "  ok    e(G₁, ∞) = 1"
  else do failures := failures + 1
          IO.println "  FAIL  e(G₁, ∞) ≠ 1"

  -- Test 2: e(G, G2)·e(G, -G2) = 1.
  let r2 := multiPairing [(G, G2), (G, negate G2)]
  if r2 == 1 then IO.println "  ok    e(G, G2)·e(G, -G2) = 1"
  else do failures := failures + 1
          IO.println "  FAIL  e(G, G2)·e(G, -G2) = 1"

  -- Test 3: e(G, G2) ≠ 1.
  let r3 := pairing G G2
  if r3 != 1 then IO.println "  ok    e(G, G2) ≠ 1"
  else do failures := failures + 1
          IO.println "  FAIL  e(G, G2) = 1 (should be ≠ 1)"

  if failures = 0 then
    IO.println "All 4 BLS12-381 pairing checks passed."
  else
    IO.println s!"{failures} case(s) FAILED."
    IO.Process.exit 1
