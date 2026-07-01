import EvmSemantics.Crypto.Sha256

open EvmSemantics.Crypto.Sha256 (hash)

/-- Micro-benchmark for `EvmSemantics.Crypto.Sha256.hash`. Motivation:
the `Call50000_sha256` state-test hits our slow-file report at ~45 s
wall time (par=16), so we want to know whether the raw hash function
is the bottleneck or the surrounding CALL-frame machinery is. This
exe hashes a fixed 32-byte input `iters` times and reports ns/op. -/
def main : IO Unit := do
  let base : ByteArray := ByteArray.mk (Array.replicate 32 0x42)
  -- Warm-up.
  let _ := EvmSemantics.Crypto.Sha256.hash base
  for iters in [1000, 10000, 50000] do
    let t0 ← IO.monoNanosNow
    let mut acc : ByteArray := base
    for _ in [0:iters] do
      acc := EvmSemantics.Crypto.Sha256.hash acc
    let t1 ← IO.monoNanosNow
    let totalNs := t1 - t0
    let perOp   := totalNs / iters
    IO.println s!"{iters} × sha256(32B chained) = {totalNs / 1000000}ms  ({perOp}ns/op)"
    IO.println s!"  final digest[0]={acc.get! 0}"
