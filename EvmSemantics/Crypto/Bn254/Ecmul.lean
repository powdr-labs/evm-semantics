module

public import EvmSemantics.Crypto.EC
public import EvmSemantics.Crypto.Bn254.Curve
public import EvmSemantics.Crypto.Bytes
public import EvmSemantics.Crypto.Bn254.Ecadd

/-!
`EvmSemantics.Crypto.Ecmul` — Ethereum's `0x07 ECMUL` precompile,
alt_bn128 scalar multiplication (EIP-196, Byzantium+).

Wire format (96 bytes in, 64 bytes out):

* `input[0:32]  = x`, `input[32:64] = y` — the point.
* `input[64:96] = k` — the scalar, an unbounded `Nat` (EIP-196
  allows arbitrary 256-bit values; higher-order bits are simply
  interpreted modulo the group order by the double-and-add loop).
* Short input is right-padded with zeros; long input is truncated.
* `(x, y)` validation is identical to `Ecadd`: coordinates `< p`,
  and either `(0, 0)` (infinity) or a curve point.

Output: `writeBE (k·P).x 32 ++ writeBE (k·P).y 32`.

We re-use `Ecadd.decodePoint` / `Ecadd.encodePoint` so the two
precompiles agree bit-for-bit on the wire encoding.
-/

@[expose] public section

namespace EvmSemantics.Crypto.Ecmul

open EvmSemantics.Crypto.EC
open EvmSemantics.Crypto.Bn254
open EvmSemantics.Crypto.Bytes
open EvmSemantics.Crypto.Ecadd (decodePoint encodePoint)

/-- ECMUL core: parse the (padded/truncated) 96-byte input, validate,
    and return `some 64-byte-output` on success or `none` if the input
    was invalid.

    On `none` the caller (the precompile dispatcher) treats the call
    as all-gas-consumed / no output, per EIP-196. -/
def run? (input : ByteArray) : Option ByteArray := do
  let x := readBE input 0  32
  let y := readBE input 32 32
  let k := readBE input 64 32
  let P ← decodePoint x y
  some (encodePoint (scalarMul k P))

end EvmSemantics.Crypto.Ecmul
