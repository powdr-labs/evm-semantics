module

public import EvmSemantics.Data.UInt256
public import EvmSemantics.State.Account

/-!
`EvmSemantics.Hex` — small library of hex string ↔ byte / `Nat` helpers
used by the test runners (`VMRunner`, `StateTestRunner`, `KeccakTest`) to
parse JSON corpora and to format byte arrays for output.

The EVM-specific wrappers (`hexToUInt256`, `hexToAddress`) live here too
so all three runners share a single source of truth; nothing in the
relational `Step` / `stepF` proof side depends on these.
-/

@[expose] public section

namespace EvmSemantics
namespace Hex

/-- The numeric value 0-15 of a hex digit character (case-insensitive).
    Returns `0` on any other character. -/
def hexVal (c : Char) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else if 'A' ≤ c ∧ c ≤ 'F' then c.toNat - 'A'.toNat + 10
  else 0

/-- Strip a leading `0x` or `0X` prefix, if present. -/
def strip0x (s : String) : String :=
  if s.startsWith "0x" ∨ s.startsWith "0X" then String.ofList (s.toList.drop 2) else s

/-- Decode an optionally-`0x`-prefixed hex string into a `Nat` (big-endian).
    Invalid characters contribute `0`, matching the lenient parsing the
    test corpus expects. -/
def hexToNat (s : String) : Nat :=
  (strip0x s).foldl (fun acc c => acc * 16 + hexVal c) 0

/-- Decode an optionally-`0x`-prefixed hex string into a `UInt256`. -/
def hexToUInt256 (s : String) : UInt256 := UInt256.ofNat (hexToNat s)

/-- Decode an optionally-`0x`-prefixed hex string into an `AccountAddress`
    (`Fin (2^160)`), truncating to 160 bits if longer. -/
def hexToAddress (s : String) : AccountAddress := AccountAddress.ofNat (hexToNat s)

/-- Decode an optionally-`0x`-prefixed hex string into a `ByteArray`. An
    odd number of nibbles is interpreted as if a leading `0` had been
    supplied (matching how some legacy corpus fields are written). -/
def hexToBytes (s : String) : ByteArray := Id.run do
  let cs0 := (strip0x s).toList
  let cs := if cs0.length % 2 == 1 then '0' :: cs0 else cs0
  let mut out : ByteArray := .empty
  let mut rest := cs
  while rest.length ≥ 2 do
    match rest with
    | hi :: lo :: tl =>
      out := out.push (UInt8.ofNat (hexVal hi * 16 + hexVal lo))
      rest := tl
    | _ => rest := []
  return out

/-- Lowercase hex encoding of a byte array (no `0x` prefix). Each byte
    expands to exactly two characters. -/
def bytesToHex (bs : ByteArray) : String :=
  let nibble (n : Nat) : Char :=
    if n < 10 then Char.ofNat (n + '0'.toNat)
    else Char.ofNat (n - 10 + 'a'.toNat)
  let chars : Array Char := bs.toList.foldl
    (fun acc b => (acc.push (nibble (b.toNat / 16))).push (nibble (b.toNat % 16)))
    #[]
  String.ofList chars.toList

end Hex
end EvmSemantics
