import EvmSemantics.Crypto.Ecrecover
import EvmSemantics.Data.Hex

open EvmSemantics.Crypto.Ecrecover (run)
open EvmSemantics.Hex (hexToNat)

/-- Pack a 4-tuple into the 128-byte precompile call format. -/
def mkInput (h : String) (v : Nat) (r s : String) : ByteArray :=
  let hexTo32 (t : String) : ByteArray := Id.run do
    let n := hexToNat t
    let mut acc : ByteArray := ByteArray.empty
    for i in [0:32] do
      let shift : Nat := 8 * (31 - i)
      acc := acc.push ((n >>> shift) &&& 0xff).toUInt8
    return acc
  let vBytes : ByteArray := Id.run do
    let mut acc : ByteArray := ByteArray.empty
    for _ in [0:31] do acc := acc.push 0
    acc.push v.toUInt8
  hexTo32 h ++ vBytes ++ hexTo32 r ++ hexTo32 s

/-- Perturb the last byte of `input` so each iteration produces a
    distinct call (defeats any tempting memoisation of `run`). -/
def mkVariant (base : ByteArray) (nonce : Nat) : ByteArray :=
  ByteArray.mk (base.toList.mapIdx (fun i b =>
    if i = 31 then UInt8.ofNat nonce else b)).toArray

def main : IO Unit := do
  let baseInput := mkInput
    "456e9aea5e197a1f1af7a3e85a3212fa4049a3ba34c2289b4c860fc0b0c64ef3"
    28
    "9242685bf161793cc25603c231bc2f568eb630ea16aa137d2664ac8038825608"
    "4f8ae3bd7535248d0bd448298cc2e2071e56992d0774dc340c368ae950852ada"
  IO.println s!"== Ecrecover.run micro-benchmark ({baseInput.size}-byte input) =="
  -- Warm-up (one call to force any lazy init).
  let _ := run (mkVariant baseInput 0)
  for iters in [10, 50, 100] do
    let t0 ← IO.monoNanosNow
    let mut cksum : Nat := 0
    for i in [1:iters+1] do
      let out := run (mkVariant baseInput i)
      cksum := cksum + out.size
    let t1 ← IO.monoNanosNow
    let ns := t1 - t0
    let totalMs := ns / 1000000
    let perUs := ns / (1000 * iters)
    IO.println s!"  iters={iters}  total={totalMs}ms  per-call≈{perUs}µs  cksum={cksum}"
