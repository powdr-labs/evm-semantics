module

public import EvmSemantics.Data.Rlp

/-!
`EvmSemantics.Rlp` decoder — the inverse of the encoder in
`EvmSemantics.Data.Rlp`. Parses a `ByteArray` into the `Rlp.Item` tree
(byte strings and nested lists), enforcing the *canonical* form the
Yellow Paper §B / EIP-RLP mandates:

* A byte `< 0x80` stands for itself (a 1-byte string).
* `0x80 + n` (`n ≤ 55`) introduces an `n`-byte string; a length-1 string
  whose single byte is `< 0x80` is **non-canonical** (should have used
  the self-encoding form) and is rejected.
* `0xb7 + k` introduces a string whose length is the `k`-byte big-endian
  integer that follows; the long form is only canonical when the length
  exceeds 55, and the length bytes must not carry a leading zero.
* `0xc0 + n` / `0xf7 + k` are the list analogues.

Anything that doesn't parse to *exactly* the input bytes — trailing
garbage, a truncated payload, a non-canonical length, or a nested item
that overruns its list payload — decodes to `none`. This strictness is
what the `TransactionTests/ttWrongRLP` conformance cases exercise.

The decoder is written with `partial def` (mutually recursive over the
list payload) rather than the encoder's total style: it consumes bounded
input and every recursive call advances the offset, but proving that to
Lean would need a well-founded measure the callers don't require. This
mirrors `Tx.run` / `fakeExponential`, which are `partial` for the same
reason.
-/

@[expose] public section

namespace EvmSemantics
namespace Rlp

/-- Big-endian value of the `n` bytes of `bs` starting at `off`. Callers
    bounds-check `off + n ≤ bs.size` before calling; out-of-range indices
    read as `0` via `bs[·]!`. -/
def readBEAt (bs : ByteArray) (off n : Nat) : Nat := Id.run do
  let mut acc := 0
  for i in [0:n] do
    acc := acc * 256 + (bs[off + i]!).toNat
  return acc

mutual

/-- Decode one RLP item at byte offset `off`, returning the item and the
    offset just past it. Returns `none` on a truncated payload, a
    non-canonical length prefix, or a non-canonical single-byte string. -/
partial def decodeAt (bs : ByteArray) (off : Nat) : Option (Item × Nat) := do
  if off ≥ bs.size then none
  else
    let b := (bs[off]!).toNat
    if b < 0x80 then
      -- A byte below 0x80 encodes itself as a one-byte string.
      some (.bytes (bs.extract off (off + 1)), off + 1)
    else if b ≤ 0xb7 then
      -- Short string of length `b - 0x80`.
      let len := b - 0x80
      let dataOff := off + 1
      if dataOff + len > bs.size then none
      -- A single byte `< 0x80` must use the self-encoding form above.
      else if len = 1 ∧ (bs[dataOff]!).toNat < 0x80 then none
      else some (.bytes (bs.extract dataOff (dataOff + len)), dataOff + len)
    else if b ≤ 0xbf then
      -- Long string: `b - 0xb7` big-endian length bytes, then the payload.
      let lenOfLen := b - 0xb7
      let lenOff := off + 1
      if lenOff + lenOfLen > bs.size then none
      -- Canonical: no leading zero in the length, and long form only for
      -- payloads that don't fit the short form (`len > 55`).
      else if (bs[lenOff]!).toNat = 0 then none
      else
        let len := readBEAt bs lenOff lenOfLen
        if len ≤ 55 then none
        else
          let dataOff := lenOff + lenOfLen
          if dataOff + len > bs.size then none
          else some (.bytes (bs.extract dataOff (dataOff + len)), dataOff + len)
    else if b ≤ 0xf7 then
      -- Short list: payload of length `b - 0xc0`.
      let len := b - 0xc0
      let payloadOff := off + 1
      if payloadOff + len > bs.size then none
      else
        let items ← decodeListItems bs payloadOff (payloadOff + len)
        some (.list items, payloadOff + len)
    else
      -- Long list: `b - 0xf7` big-endian length bytes, then the payload.
      let lenOfLen := b - 0xf7
      let lenOff := off + 1
      if lenOff + lenOfLen > bs.size then none
      else if (bs[lenOff]!).toNat = 0 then none
      else
        let len := readBEAt bs lenOff lenOfLen
        if len ≤ 55 then none
        else
          let payloadOff := lenOff + lenOfLen
          if payloadOff + len > bs.size then none
          else
            let items ← decodeListItems bs payloadOff (payloadOff + len)
            some (.list items, payloadOff + len)

/-- Decode a run of items filling exactly the byte range `[off, endOff)`.
    Fails if an item overruns `endOff` or the items don't tile the range
    exactly. -/
partial def decodeListItems (bs : ByteArray) (off endOff : Nat) :
    Option (List Item) := do
  if off = endOff then some []
  else if off > endOff then none
  else
    let (item, next) ← decodeAt bs off
    if next > endOff then none
    else
      let rest ← decodeListItems bs next endOff
      some (item :: rest)

end

/-- Decode a complete RLP-encoded byte string into an `Item`. The entire
    input must be consumed — trailing bytes make the decode fail. -/
def decode (bs : ByteArray) : Option Item := do
  let (item, next) ← decodeAt bs 0
  if next = bs.size then some item else none

namespace Item

/-- The byte-string payload of an item, or `none` if it is a list. -/
def asBytes : Item → Option ByteArray
  | .bytes b => some b
  | .list _  => none

/-- The child items of a list item, or `none` if it is a byte string. -/
def asList : Item → Option (List Item)
  | .list xs => some xs
  | .bytes _ => none

/-- Interpret a byte-string item as a big-endian scalar. Lists give
    `none`. Does not enforce canonical (leading-zero-free) form — callers
    that need that check the raw bytes via `asBytes`. -/
def asNat (i : Item) : Option Nat :=
  i.asBytes.map (fun b => Data.Bytes.bytesToBigEndianNat b)

end Item

end Rlp
end EvmSemantics
