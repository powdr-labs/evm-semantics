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

/-- Read `n` bytes from `bs` starting at `start`, zero-padding past the end. -/
def readPadded (bs : ByteArray) (start n : Nat) : ByteArray :=
  let avail := if start ≤ bs.size then bs.size - start else 0
  let take  := Nat.min avail n
  let pad   := n - take
  let prefix1 := bs.extract start (start + take)
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
