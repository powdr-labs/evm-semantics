module

/-!
Shared EIP-4844 `fake_exponential` for the test runners.

Every runner that derives a blob base fee from `excessBlobGas` imports this
single copy. It used to be duplicated per runner, and the copies drifted:
one stale variant multiplied the accumulator by `numerator` only, without
folding in the `denominator · i` division, and so diverged badly for large
inputs (two separate audits flagged the drift). Keep the algorithm here and
only the fork-specific `BLOB_BASE_FEE_UPDATE_FRACTION` choice in the
runners.
-/

public section

namespace TestSupport

/-- Spec-faithful EIP-4844 `fake_exponential(factor, numerator, denominator)`,
    approximating `factor · e^(numerator / denominator)` via the Taylor series
    with *factorial* denominators (`Σ factor·num^i / (denom^i · i!)`). The
    running term is `numAccum`, seeded at `factor·denominator` and updated
    `numAccum := numAccum · numerator / (denominator · i)` each step (so the
    `i!` accumulates), summed until it underflows to `0`; the total is then
    divided by `denominator`. A plain `num^i` polynomial (without the `/i!`)
    truncates after the first term for any `numerator < denominator`,
    understating the blob base fee (`0x240000` excess must give fee `2`, not
    `1`) and letting an `INSUFFICIENT_MAX_FEE_PER_BLOB_GAS` tx through. -/
partial def fakeExponential (factor numerator denominator : Nat) : Nat :=
  let rec go (i output numAccum : Nat) (fuel : Nat) : Nat :=
    if fuel = 0 ∨ numAccum = 0 then output
    else go (i + 1) (output + numAccum) (numAccum * numerator / (denominator * i)) (fuel - 1)
  (go 1 0 (factor * denominator) 100000) / denominator

-- Compile-time regression pins for the exact drift the audits flagged: the
-- stale variant returned 1 for `0x240000` excess blob gas at the Cancun
-- update fraction; the spec answer is 2. Zero excess must give the
-- `MIN_BLOB_BASE_FEE` of 1.
/-- info: 2 -/
#guard_msgs in
#eval fakeExponential 1 0x240000 3338477

/-- info: 1 -/
#guard_msgs in
#eval fakeExponential 1 0 3338477

end TestSupport
