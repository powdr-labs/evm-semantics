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

/-! ### Read-after-write reasoning for `writeBytes`

The `mstore`/`mcopy` correctness arguments (and the verified-bytecode compiler
downstream) need to know what `writeBytes` does to memory pointwise. Everything
below reduces the `Id.run do … for … acc.set! …` loop to a `List.foldl` over
`List.range'` and reasons about that by induction. -/

/-- Bridge `bs[i]?.getD 0` (the zero-padded read the callers speak) to the
    ambient `bs[i]!`, whose `ByteArray.set!` lemmas are `@[simp]`. -/
private theorem getD0_eq_getElem! (c : ByteArray) (i : Nat) : c[i]?.getD 0 = c[i]! := by
  rw [getElem!_def]; cases c[i]? <;> rfl

/-- Folding `set!` over a list of indices never changes the array size. -/
private theorem foldl_set!_size (l : List Nat) (init : ByteArray)
    (g : Nat → Nat) (h : Nat → UInt8) :
    (l.foldl (fun acc i => acc.set! (g i) (h i)) init).size = init.size := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih => simp only [List.foldl_cons]; rw [ih]; simp

/-- Appending zero padding does not change the zero-padded read: an index that
    lands in (or past) the appended zeros reads `0`, exactly what an
    out-of-range read of the original array yields. -/
private theorem append_replicate_zero_getElem! (bs : ByteArray) (k a : Nat) :
    (bs ++ ByteArray.mk (Array.replicate k 0))[a]! = bs[a]! := by
  by_cases h : a < bs.size
  · rw [getElem!_pos (bs ++ _) a (by rw [ByteArray.size_append]; omega),
        getElem!_pos bs a h, ByteArray.getElem_append_left h]
  · rw [getElem!_neg bs a h]
    by_cases h2 : a < (bs ++ ByteArray.mk (Array.replicate k 0)).size
    · rw [getElem!_pos _ a h2, ByteArray.getElem_append_right (by omega)]
      simp only [ByteArray.getElem_eq_getElem_data, Array.getElem_replicate]; rfl
    · rw [getElem!_neg _ a h2]

/-- Read-after-write for the copy loop as a `List.foldl`: writing
    `bytes[i]!` at `start + i` for `i ∈ [0, n)` (with the destination already
    sized to hold the whole window, `start + n ≤ init.size`) makes index `a`
    read the written byte inside the window and the original byte otherwise. -/
private theorem foldl_set!_read (bytes init : ByteArray) (start : Nat) :
    ∀ (n a : Nat), start + n ≤ init.size →
    ((List.range' 0 n).foldl (fun acc i => acc.set! (start + i) bytes[i]!) init)[a]!
      = if start ≤ a ∧ a < start + n then bytes[a - start]! else init[a]! := by
  intro n
  induction n with
  | zero => intro a _; rw [if_neg (by omega)]; simp
  | succ m ih =>
    intro a hsz
    rw [List.range'_concat, List.foldl_append]
    simp only [Nat.one_mul, Nat.zero_add, List.foldl_cons, List.foldl_nil]
    have hWsize : (List.foldl (fun acc i => acc.set! (start + i) bytes[i]!) init
        (List.range' 0 m)).size = init.size :=
      foldl_set!_size (List.range' 0 m) init (fun i => start + i) (fun i => bytes[i]!)
    rw [ByteArray.getElem!_set! _ (start + m) bytes[m]! a (by rw [hWsize]; omega)]
    by_cases hcase : start + m = a
    · subst hcase
      rw [if_pos rfl, if_pos (by omega), Nat.add_sub_cancel_left]
    · rw [if_neg hcase, ih a (by omega)]
      by_cases hin : start ≤ a ∧ a < start + m
      · rw [if_pos hin, if_pos (by omega)]
      · rw [if_neg hin, if_neg (by omega)]

/-- Read-after-write for `writeBytes`, as a zero-padded pointwise read.
    The byte at index `a` is the written byte when `a` lands in the write
    window `[start, start + bytes.size)`, and otherwise the original byte;
    the `[a]?.getD 0` framing absorbs the zero padding on both the growth
    side (`start + bytes.size > bs.size`) and the out-of-range side. -/
theorem writeBytes_getElem?_getD (bs bytes : ByteArray) (start a : Nat) :
    (writeBytes bs bytes start)[a]?.getD 0
      = if start ≤ a ∧ a < start + bytes.size then bytes[a - start]?.getD 0
        else bs[a]?.getD 0 := by
  simp only [getD0_eq_getElem!]
  unfold writeBytes
  split
  · next hz => rw [if_neg (by omega)]
  · next hne =>
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
      pure_bind, bind_pure, List.forIn_pure_yield_eq_foldl, Id.run_pure]
    have hsz : start + bytes.size ≤ (if bs.size < start + bytes.size then
        bs ++ ByteArray.mk (Array.replicate (start + bytes.size - bs.size) 0) else bs).size := by
      split <;> rename_i hc
      · rw [ByteArray.size_append]
        show start + bytes.size ≤ bs.size + (Array.replicate (start + bytes.size - bs.size) 0).size
        rw [Array.size_replicate]; omega
      · omega
    rw [foldl_set!_read bytes _ start bytes.size a hsz]
    by_cases hcond : start ≤ a ∧ a < start + bytes.size
    · rw [if_pos hcond, if_pos hcond]
    · rw [if_neg hcond, if_neg hcond]
      split <;> rename_i hc
      · exact append_replicate_zero_getElem! bs _ a
      · rfl

/-- `writeBytes` grows the array to cover the write window (and never shrinks). -/
theorem writeBytes_size (bs bytes : ByteArray) (start : Nat) :
    (writeBytes bs bytes start).size
      = if bytes.size = 0 then bs.size else max bs.size (start + bytes.size) := by
  unfold writeBytes
  split
  · rfl
  · next hne =>
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
      pure_bind, bind_pure, List.forIn_pure_yield_eq_foldl, Id.run_pure, foldl_set!_size]
    split <;> rename_i hlt
    · rw [ByteArray.size_append]
      show bs.size + (Array.replicate (start + bytes.size - bs.size) 0).size = _
      rw [Array.size_replicate]; omega
    · omega

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
