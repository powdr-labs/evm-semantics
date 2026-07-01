module

public import Init.Data.ByteArray

/-!
`EvmSemantics.Crypto.Bytes` — small byte-string helpers used by the
precompile drivers (`Ecrecover`, `Ecadd`, `Ecmul`, …).

The precompile wire format is uniformly big-endian: each 32-byte word
in the input is a `Nat` interpreted MSB-first, and each 32-byte word in
the output is likewise `Nat → 32 bytes` MSB-first. These helpers keep
that convention out of the individual drivers.

`readBE` also handles the standard precompile convention that short
input is treated as though virtually zero-padded on the *right*: reads
past the end of `bs` return `0`. `writeBE` produces a fixed-width
output regardless of the numeric value.
-/

@[expose] public section

namespace EvmSemantics.Crypto.Bytes

/-- Read a big-endian `Nat` from `bs[off..off+n)`, zero-padding past
    the end. Matches CALLDATALOAD-style virtual zero-padding of the
    right side, which every precompile inherits per EIP-196 (and by
    convention for the pre-Byzantium precompiles). -/
def readBE (bs : ByteArray) (off n : Nat) : Nat := Id.run do
  let mut w : Nat := 0
  for i in [0:n] do
    let b : Nat := if h : off + i < bs.size then bs[off + i].toNat else 0
    w := w * 256 + b
  return w

/-- Write a `Nat` as a fixed-`width`-byte big-endian `ByteArray`. -/
def writeBE (w width : Nat) : ByteArray := Id.run do
  let mut acc : ByteArray := ByteArray.empty
  for i in [0:width] do
    let shift : Nat := 8 * (width - 1 - i)
    acc := acc.push ((w >>> shift) &&& 0xff).toUInt8
  return acc

end EvmSemantics.Crypto.Bytes
