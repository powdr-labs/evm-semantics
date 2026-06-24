import EvmSemantics.Data.UInt256

/-!
`MachineState` `μ` — the (shallow) machine-level state used by every EVM
operation. Holds the gas counter, the byte-addressed `memory`, and the
`returnData` from the previous nested call. Active-word count `i` tracks
the highest word index that's been touched (for memory expansion cost).

We expose memory helpers used by the small-step rules: `mload`, `mstore`,
`mstore8`, `mcopy`, `readBytes` and `writeBytes`. ByteArray reads past
the current size are zero-padded, which matches Yellow Paper semantics.
-/

namespace EvmSemantics

structure MachineState where
  gasAvailable : UInt256
  /-- # of 32-byte words "active" in memory; used for the memory-expansion
      gas cost. -/
  activeWords  : UInt256
  /-- Byte-addressable working memory `m`. -/
  memory       : ByteArray
  /-- `o` — return data from the most recent sub-call. v1 leaves this empty. -/
  returnData   : ByteArray
  /-- `H_return` — buffer used to communicate RETURN/REVERT output upward. -/
  H_return     : ByteArray
  deriving Inhabited

namespace MachineState

/-- Upper bound (in bytes) on any memory offset+size the evaluator will touch.

    The real EVM has no hard cap, but it prices every byte of memory expansion
    via gas whose cost grows quadratically, so reaching even a few MiB is
    already economically impossible and `~2^256` offsets are unreachable. This
    evaluator does not yet model memory-expansion gas, so without a guard the
    pure helpers `readPadded`/`writeBytes` would try to allocate up to `2^256`
    bytes and OOM/abort the process.

    We pick `2^32` (4 GiB): far larger than anything any real bytecode or test
    reaches, yet small enough that `offset + size` exceeding it is a reliable
    signal of an attacker-supplied `~2^256` value. Out-of-range accesses are
    rejected as an exceptional halt (`InvalidMemoryAccess`) by the callers,
    matching how a real client would fail such a transaction (out of gas). -/
def maxMemSize : Nat := 2 ^ 32

/-- Whether *writing* the byte range `[offset, offset + size)` into memory stays
    within `maxMemSize`. `writeBytes` grows the backing `ByteArray` to
    `offset + size`, so this is the quantity that must be bounded to avoid a
    giant allocation. Used by the step function to reject huge memory writes
    with an exceptional halt. -/
def memBoundsOk (offset size : Nat) : Bool := offset + size ≤ maxMemSize

/-- Whether *reading* `size` bytes (via `readPadded`) stays within `maxMemSize`.

    Unlike a write, a `readPadded` from a huge *offset* is harmless: it
    zero-pads and allocates only `size` bytes regardless of the offset (matching
    the EVM, where out-of-range reads read as zero). So only the requested
    `size` must be bounded — guarding the offset too would wrongly reject the
    legitimate zero-padding behaviour exercised by the `…DataIndexTooHigh` /
    `…BigOffset` tests. -/
def readSizeOk (size : Nat) : Bool := size ≤ maxMemSize

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
  let padded := if bs.size < needed then bs ++ ByteArray.mk (Array.replicate (needed - bs.size) 0) else bs
  let rec go (i : Nat) (acc : ByteArray) : ByteArray :=
    if i < bytes.size then
      go (i+1) (acc.set! (start + i) bytes[i]!)
    else acc
  go 0 padded

/-- Active-word count `i'` after touching the byte range `[offset, offset+sz)`. -/
def activeWordsAfter (curr offset sz : Nat) : Nat :=
  if sz = 0 then curr else
    let lastByte := offset + sz - 1
    let lastWord := lastByte / 32 + 1
    Nat.max curr lastWord

/-- MLOAD: read 32 bytes at `addr`, returning (word, μ'). -/
def mload (μ : MachineState) (addr : UInt256) : UInt256 × MachineState :=
  let bs := readPadded μ.memory addr.toNat 32
  let word : Nat := bs.toList.foldl (fun acc b => acc * 256 + b.toNat) 0
  let μ' := { μ with
                activeWords := UInt256.ofNat (activeWordsAfter μ.activeWords.toNat addr.toNat 32) }
  (UInt256.ofNat word, μ')

/-- Decompose a 256-bit word into 32 big-endian bytes. -/
def wordBytes (w : UInt256) : ByteArray :=
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

/-- GAS: remaining gas. -/
def gas (μ : MachineState) : UInt256 := μ.gasAvailable

/-- RETURNDATASIZE: length of the return-data buffer. -/
def returnDataSize (μ : MachineState) : UInt256 := UInt256.ofNat μ.returnData.size

def setReturnData (μ : MachineState) (bs : ByteArray) : MachineState :=
  { μ with returnData := bs }

def setHReturn (μ : MachineState) (bs : ByteArray) : MachineState :=
  { μ with H_return := bs }

end MachineState

end EvmSemantics
