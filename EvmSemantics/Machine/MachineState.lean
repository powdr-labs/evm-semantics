module

public import EvmSemantics.Data.UInt256
public import Batteries.Tactic.Lint.Misc

/-!
`MachineState` `μ` — the (shallow) machine-level state used by every EVM
operation. Holds the gas counter, the byte-addressed `memory`, and the
`returnData` from the previous nested call. Active-word count `i` tracks
the highest word index that's been touched (for memory expansion cost).

We expose memory helpers used by the small-step rules: `mload`, `mstore`,
`mstore8`, `mcopy`, `readBytes` and `writeBytes`. ByteArray reads past
the current size are zero-padded, which matches Yellow Paper semantics.
-/

@[expose] public section

namespace EvmSemantics

/-- Machine state `μ` (Yellow Paper §9.4.1): gas counter, memory, return-data
    buffer, and the bookkeeping needed for memory expansion costs. -/
structure MachineState where
  /-- `g` — gas remaining in the current frame. We use `Nat` so that statements like
      "starting from some amount of gas, this routine has the following semantics"
      can be made. -/
  gasAvailable : Nat
  /-- # of 32-byte words "active" in memory; used for the memory-expansion
      gas cost. -/
  activeWords  : UInt256
  /-- Byte-addressable working memory `m`. -/
  memory       : ByteArray
  /-- `o` — return data from the most recent sub-call. v1 leaves this empty. -/
  returnData   : ByteArray
  /-- `hReturn` — buffer used to communicate RETURN/REVERT output upward. -/
  hReturn     : ByteArray
  deriving Inhabited

namespace MachineState

/-- Active-word count `i'` after touching the byte range `[offset, offset+sz)`. -/
def activeWordsAfter (curr offset sz : Nat) : Nat :=
  if sz = 0 then curr else
    let lastByte := offset + sz - 1
    let lastWord := lastByte / 32 + 1
    Nat.max curr lastWord

/-- Yellow Paper memory cost `C_mem(a) = G_memory·a + ⌊a²/512⌋` (eq. 326).
    `a` is the number of 32-byte words currently active.  `G_memory = 3`. -/
def memCost (a : Nat) : Nat := 3 * a + a ^ 2 / 512

/-- Gas to charge for the memory expansion that *would result* from touching
    the byte range `[offset, offset+sz)` given that `curr` words are already
    active.  Returns `0` when the access fits inside the already-active
    region.  The reference high-water-mark calculation is `activeWordsAfter`,
    which matches the Yellow Paper's `⌈(offset+sz)/32⌉` rounding.

    This is what protects the runtime from OOM on huge offsets/sizes: the
    quadratic term in `memCost` makes any `offset+sz` past a few MiB cost
    astronomically more gas than any real transaction can hold, so legitimate
    callers will hit `OutOfGas` long before the underlying `ByteArray` is
    asked to allocate something dangerous. -/
def memExpansionDelta (curr offset sz : Nat) : Nat :=
  memCost (activeWordsAfter curr offset sz) - memCost curr

/-- Two-range version of `memExpansionDelta`, used by MCOPY which touches
    both the source-read range `[off1, off1+sz1)` and the destination-write
    range `[off2, off2+sz2)`. The expansion is charged for the union. -/
def memExpansionDelta2 (curr off1 sz1 off2 sz2 : Nat) : Nat :=
  memCost (activeWordsAfter (activeWordsAfter curr off1 sz1) off2 sz2) - memCost curr

/-- Read `n` bytes from `bs` starting at `start`, zero-padding past the end.

    `start` is clamped to `bs.size` before being passed to `ByteArray.extract`.
    This is semantically transparent — bytes at or past the end read as zero
    either way — but it avoids handing a `~2^256` index to the runtime's
    `extract`, which would otherwise OOM/abort even when only a small `n` bytes
    are requested (e.g. CALLDATALOAD/CALLDATACOPY/LOG with a huge offset, which
    the EVM treats as a cheap zero-padded read). The total allocation is exactly
    `n` bytes (`take` real + `pad` zeros), independent of `start`. -/
def readPadded (bs : ByteArray) (start n : Nat) : ByteArray :=
  let start' := Nat.min start bs.size
  let avail := bs.size - start'
  let take  := Nat.min avail n
  let pad   := n - take
  let prefix1 := bs.extract start' (start' + take)
  prefix1 ++ ByteArray.mk (Array.replicate pad 0)

/-- Write `bytes` into `bs` starting at `start`, growing `bs` with zeros if
    needed. -/
partial def writeBytes (bs bytes : ByteArray) (start : Nat) : ByteArray :=
  let needed := start + bytes.size
  let padded :=
    if bs.size < needed then bs ++ ByteArray.mk (Array.replicate (needed - bs.size) 0) else bs
  -- Inner loop: copy `bytes[i..]` into `acc` starting at `start + i`.
  let rec go (i : Nat) (acc : ByteArray) : ByteArray :=
    if i < bytes.size then
      go (i+1) (acc.set! (start + i) bytes[i]!)
    else acc
  go 0 padded

/-- Decode a big-endian byte sequence as a `Nat`. Inverse of `wordBytes`
    (modulo length). Shared by `mload` and `CALLDATALOAD`, which both
    read a window of bytes (memory or calldata) and interpret it as a
    256-bit word. -/
def bytesToBigEndianNat (bs : ByteArray) : Nat :=
  bs.toList.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- Read a 32-byte big-endian word from `bs` at `offset`, zero-padding
    past the end. Used by both `MLOAD` (over memory) and `CALLDATALOAD`
    (over calldata). -/
def readWord (bs : ByteArray) (offset : Nat) : UInt256 :=
  UInt256.ofNat (bytesToBigEndianNat (readPadded bs offset 32))

/-- MLOAD: read 32 bytes at `addr`, returning (word, μ'). -/
def mload (μ : MachineState) (addr : UInt256) : UInt256 × MachineState :=
  let μ' := { μ with
                activeWords := UInt256.ofNat (activeWordsAfter μ.activeWords.toNat addr.toNat 32) }
  (readWord μ.memory addr.toNat, μ')

/-- Decompose a 256-bit word into 32 big-endian bytes. -/
def wordBytes (w : UInt256) : ByteArray :=
  -- Peel off the low byte `i` times, big-endian accumulation.
  let rec go (i : Nat) (n : Nat) (acc : List UInt8) : List UInt8 :=
    if i = 0 then acc else go (i-1) (n / 256) (UInt8.ofNat (n % 256) :: acc)
  ByteArray.mk (go 32 w.toNat []).toArray

/-- MSTORE: write `v` as 32 bytes at `addr`. -/
def mstore (μ : MachineState) (addr v : UInt256) : MachineState :=
  let bs := wordBytes v
  { μ with
      memory := writeBytes μ.memory bs addr.toNat,
      activeWords := UInt256.ofNat (activeWordsAfter μ.activeWords.toNat addr.toNat 32) }

/-- MSTORE8: write the low byte of `v` at `addr`. -/
def mstore8 (μ : MachineState) (addr v : UInt256) : MachineState :=
  let b : UInt8 := UInt8.ofNat (v.toNat % 256)
  { μ with
      memory := writeBytes μ.memory (ByteArray.mk #[b]) addr.toNat,
      activeWords := UInt256.ofNat (activeWordsAfter μ.activeWords.toNat addr.toNat 1) }

/-- MCOPY: copy `sz` bytes from `src` to `dst` within memory. -/
def mcopy (μ : MachineState) (dst src sz : UInt256) : MachineState :=
  let bytes := readPadded μ.memory src.toNat sz.toNat
  { μ with
      memory := writeBytes μ.memory bytes dst.toNat,
      activeWords :=
        UInt256.ofNat (activeWordsAfter
          (activeWordsAfter μ.activeWords.toNat src.toNat sz.toNat)
          dst.toNat sz.toNat) }

/-- MSIZE: number of *bytes* currently considered active (= 32·activeWords). -/
def msize (μ : MachineState) : UInt256 := UInt256.ofNat (32 * μ.activeWords.toNat)

/-- GAS opcode result: remaining gas, packed into a 256-bit stack word. -/
def gas (μ : MachineState) : UInt256 := UInt256.ofNat μ.gasAvailable

/-- RETURNDATASIZE: length of the return-data buffer. -/
def returnDataSize (μ : MachineState) : UInt256 := UInt256.ofNat μ.returnData.size

/-- Replace the return-data buffer. -/
def setReturnData (μ : MachineState) (bs : ByteArray) : MachineState :=
  { μ with returnData := bs }

/-- Replace the `hReturn` (RETURN/REVERT output) buffer. -/
def setHReturn (μ : MachineState) (bs : ByteArray) : MachineState :=
  { μ with hReturn := bs }

-- The `let rec`-generated workers inside `writeBytes` and `wordBytes`
-- are private inner loops, not user-facing API; silence `docBlame`.
attribute [nolint docBlame]
  MachineState.writeBytes.go
  MachineState.wordBytes.go

end MachineState

end EvmSemantics
