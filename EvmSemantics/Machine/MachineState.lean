module

public import EvmSemantics.Data.UInt256
public import EvmSemantics.Data.Bytes
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
  /-- `o` — return data from the most recent sub-call. -/
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
    needed. Writing zero bytes is a no-op — `bs` is returned unchanged
    even if `start` is huge (otherwise `needed = start` would trigger a
    monster zero-fill allocation on e.g. `MCOPY(dst = 2^256-1, sz = 0)`,
    which is a valid EVM no-op).

    Non-`partial`: the copy loop is a plain `Id.run do` `for`-in over
    the fixed range `[0, bytes.size)`, whose termination Lean discharges
    structurally. Kernel-transparent, so downstream proofs can reduce
    calls to `writeBytes` on concrete arguments. -/
def writeBytes (bs bytes : ByteArray) (start : Nat) : ByteArray :=
  if bytes.size = 0 then bs else
  let needed := start + bytes.size
  let padded :=
    if bs.size < needed then bs ++ ByteArray.mk (Array.replicate (needed - bs.size) 0) else bs
  Id.run do
    let mut acc := padded
    for i in [0:bytes.size] do
      acc := acc.set! (start + i) bytes[i]!
    return acc

/-- Read a 32-byte big-endian word from `bs` at `offset`, zero-padding
    past the end. Used by both `MLOAD` (over memory) and `CALLDATALOAD`
    (over calldata). Bytes → Nat conversion lives in
    `EvmSemantics.Data.Bytes` so the machine helpers, the bytecode
    decoder, and the MPT trie can share one definition. -/
def readWord (bs : ByteArray) (offset : Nat) : UInt256 :=
  UInt256.ofNat (Data.Bytes.bytesToBigEndianNat (readPadded bs offset 32))

/-- MLOAD: read 32 bytes at `addr`, returning the word and the unchanged
    machine state. The caller is responsible for charging the
    memory-expansion gas (via `consumeMemExp`), which already advances the
    active-words high-water mark. -/
def mload (μ : MachineState) (addr : UInt256) : UInt256 × MachineState :=
  (readWord μ.memory addr.toNat, μ)

/-- MSTORE: write `v` as 32 bytes at `addr`. The active-words high-water
    mark is updated by the caller's `consumeMemExp`, not here.
    `natToBytesPadded v.toNat 32` is the shared "UInt256 → 32
    big-endian bytes" encoder (also used by `Rlp.uint256ToBytes32`
    downstream). -/
def mstore (μ : MachineState) (addr v : UInt256) : MachineState :=
  { μ with memory := writeBytes μ.memory
                       (Data.Bytes.natToBytesPadded v.toNat 32) addr.toNat }

/-- MSTORE8: write the low byte of `v` at `addr`. Active-words update is
    the caller's responsibility (`consumeMemExp`). -/
def mstore8 (μ : MachineState) (addr v : UInt256) : MachineState :=
  let b : UInt8 := UInt8.ofNat (v.toNat % 256)
  { μ with memory := writeBytes μ.memory (ByteArray.mk #[b]) addr.toNat }

/-- MCOPY: copy `sz` bytes from `src` to `dst` within memory. Active-words
    update is the caller's responsibility (`consumeMemExp2`). -/
def mcopy (μ : MachineState) (dst src sz : UInt256) : MachineState :=
  let bytes := readPadded μ.memory src.toNat sz.toNat
  { μ with memory := writeBytes μ.memory bytes dst.toNat }

/-- MSIZE: number of *bytes* currently considered active (= 32·activeWords). -/
def msize (μ : MachineState) : UInt256 := UInt256.ofNat (32 * μ.activeWords.toNat)

end MachineState

end EvmSemantics
