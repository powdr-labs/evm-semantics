module

public import EvmSemantics.State.Account

/-!
`EvmSemantics.Rlp` — a full RLP **encoder** (decoder not included).

Yellow Paper §B / EIP-RLP defines the canonical encoding:

* A single byte `< 0x80` encodes as itself.
* A byte string of length `n ≤ 55` encodes as `0x80 + n` prepended.
* A byte string of length `56 ≤ n < 2^64` encodes as
  `0xb7 + |intToBytes n|` followed by the big-endian length and then
  the bytes.
* A list whose concatenated payload has length `n ≤ 55` encodes as
  `0xc0 + n` prepended.
* A list with `56 ≤ n < 2^64` total payload encodes as
  `0xf7 + |intToBytes n|` followed by the big-endian length and then
  the payload.

The length prefix for the long forms is capped at 8 bytes by the spec
(lengths fit in `Nat < 2^64`). The encoders return
`Option ByteArray`, with `none` indicating the input is unencodable
(payload ≥ 2^64 bytes). In practice every EVM payload is bounded
well below this by gas limits, so `none` is unreachable from any
gas-bounded execution path — but the type makes the failure mode
honest, and every definition in this module is **total**: no
`partial def`, no `panic!`. `intToBytesAux` terminates via
`Nat.div_lt_self`, and `Item.encode` recurses structurally over
the `Item` ADT.

This module is encoder-only — decoding would require a parser plus
round-trip / canonical-form proofs and is left to a future extension
when transaction processing / block validation / MPT state proofs land.
-/

@[expose] public section

namespace EvmSemantics
namespace Rlp

----------------------------------------------------------------------------
-- `intToBytes` — big-endian Nat → ByteArray, used by the long-form
-- length prefix. Terminates via `Nat.div_lt_self` on `k / 256 < k`.
----------------------------------------------------------------------------

/-- Inner loop of `intToBytes`: peel off LSB-first into `acc`
    (which is implicitly big-endian when read left-to-right).
    Terminates because `k / 256 < k` whenever `k ≠ 0`. -/
def intToBytesAux (k : Nat) (acc : List UInt8) : List UInt8 :=
  if h : k = 0 then acc
  else intToBytesAux (k / 256) (UInt8.ofNat (k % 256) :: acc)
termination_by k
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

/-- Big-endian byte representation of `n` with leading zeros stripped.
    `intToBytes 0 = ByteArray.empty` — RLP encodes the integer `0` as
    the empty byte string (whose RLP encoding is then the single byte
    `0x80`, via `encodeBytes` below). -/
def intToBytes (n : Nat) : ByteArray := ByteArray.mk (intToBytesAux n []).toArray

/-- Big-endian *padded* representation of `n` into exactly `width`
    bytes. Used for fixed-width fields like `AccountAddress` (20 bytes)
    and 32-byte hash slots, where RLP wants the leading zeros kept.
    Bits above the `width`-byte window are silently truncated. -/
def natToBytesPadded (n width : Nat) : ByteArray := Id.run do
  let mut bs : Array UInt8 := Array.mkEmpty width
  let mut k := n
  let mut le : Array UInt8 := Array.mkEmpty width
  -- Pull off `width` little-endian bytes.
  for _ in [0:width] do
    le := le.push (UInt8.ofNat (k % 256))
    k := k / 256
  -- Reverse into big-endian.
  for i in [0:width] do bs := bs.push le[width - 1 - i]!
  return ByteArray.mk bs

/-- Big-endian 20-byte representation of an `AccountAddress`. -/
def addressBytes (addr : AccountAddress) : ByteArray :=
  natToBytesPadded addr.val 20

/-- Big-endian 32-byte representation of a `UInt256`. -/
def uint256ToBytes32 (v : UInt256) : ByteArray :=
  natToBytesPadded v.toNat 32

----------------------------------------------------------------------------
-- Primitive encoders — return `Option ByteArray`, `none` if too large.
----------------------------------------------------------------------------

/-- Build the RLP length prefix for a string-or-list payload of size `n`.
    Returns `none` if `n ≥ 2^64` (the long-form length-of-length byte
    only has 8 valid slots between `0xb7` / `0xc0` and `0xf7` / `0x100`). -/
def lengthPrefix (tagSmall tagLarge : UInt8) (n : Nat) : Option ByteArray :=
  if n ≤ 55 then some (ByteArray.mk #[tagSmall + UInt8.ofNat n])
  else if n < 2^64 then
    let lenBytes := intToBytes n
    some (ByteArray.mk #[tagLarge + UInt8.ofNat lenBytes.size] ++ lenBytes)
  else none

/-- RLP-encode a byte string. Returns `none` if `bs.size ≥ 2^64`. -/
def encodeBytes (bs : ByteArray) : Option ByteArray :=
  if bs.size = 1 && bs[0]! < 0x80 then some bs
  else (lengthPrefix 0x80 0xb7 bs.size).map (· ++ bs)

/-- RLP-encode a list whose items are already individually RLP-encoded.
    Returns `none` if the concatenated payload is `≥ 2^64` bytes. -/
def encodeRawList (encodedItems : List ByteArray) : Option ByteArray :=
  let payload := encodedItems.foldl (· ++ ·) ByteArray.empty
  (lengthPrefix 0xc0 0xf7 payload.size).map (· ++ payload)

----------------------------------------------------------------------------
-- Typed RLP items.
----------------------------------------------------------------------------

/-- An RLP item: either a byte string or a list of items. -/
inductive Item where
  | bytes : ByteArray → Item
  | list  : List Item → Item

namespace Item

/-- Encode a typed RLP item. Returns `none` iff any nested string or
    list payload is `≥ 2^64` bytes. Total via structural recursion
    over `Item` — the `List.mapM` over `xs` recurses on strictly
    smaller subterms of `.list xs`. -/
def encode : Item → Option ByteArray
  | .bytes bs => encodeBytes bs
  | .list xs  => xs.mapM encode >>= encodeRawList

/-- Lift a `Nat` as a stripped big-endian integer (RLP canonical form). -/
def ofNat (n : Nat) : Item := .bytes (intToBytes n)

/-- Lift a `UInt256` as a stripped integer (RLP canonical form). -/
def ofUInt256 (v : UInt256) : Item := .bytes (intToBytes v.toNat)

/-- Lift a `UInt256` as a fixed-width 32-byte field, leading zeros
    preserved. Used inside hash preimages and MPT trie node encodings
    where leading zeros are significant. -/
def ofUInt256Bytes32 (v : UInt256) : Item := .bytes (uint256ToBytes32 v)

/-- Lift an `AccountAddress` as the 20-byte fixed-width string. -/
def ofAddress (addr : AccountAddress) : Item := .bytes (addressBytes addr)

/-- Lift a raw byte array as-is. -/
def ofByteArray (bs : ByteArray) : Item := .bytes bs

/-- Lift a `Bool`: `false` → empty string, `true` → single byte `0x01`. -/
def ofBool (b : Bool) : Item :=
  .bytes (if b then ByteArray.mk #[0x01] else ByteArray.empty)

end Item

----------------------------------------------------------------------------
-- Top-level convenience encoders.
----------------------------------------------------------------------------

/-- RLP-encode a `Nat` as a stripped big-endian integer. -/
def encodeNat (n : Nat) : Option ByteArray := (Item.ofNat n).encode

/-- RLP-encode a `UInt256` as a stripped big-endian integer. -/
def encodeUInt256 (v : UInt256) : Option ByteArray := (Item.ofUInt256 v).encode

/-- RLP-encode an `AccountAddress` as a 20-byte fixed-width string. -/
def encodeAddress (addr : AccountAddress) : Option ByteArray := (Item.ofAddress addr).encode

/-- RLP-encode a `Bool`. -/
def encodeBool (b : Bool) : Option ByteArray := (Item.ofBool b).encode

/-- RLP-encode a heterogeneous list of typed items. -/
def encodeList (items : List Item) : Option ByteArray := (Item.list items).encode

----------------------------------------------------------------------------
-- Backward-compat aliases for the existing CREATE / CREATE2 callers.
----------------------------------------------------------------------------

/-- RLP-encode a `Nat` (alias for `encodeNat`). -/
def encodeInt (n : Nat) : Option ByteArray := encodeNat n

/-- RLP-encode the two-element list `[address, nonce]`, as used by
    CREATE's address derivation:
    `keccak256(rlp([sender, sender.nonce]))[12:]`. -/
def encodeAddrNonce (addr : AccountAddress) (nonce : Nat) : Option ByteArray :=
  encodeList [.ofAddress addr, .ofNat nonce]

----------------------------------------------------------------------------
-- Totality lemmas for the encoder on bounded inputs. Used in
-- `Equiv.lean` to close `createAddress`'s unreachable `none` arm.
----------------------------------------------------------------------------

/-- `intToBytesAux n acc` produces a list whose length is at most
    `acc.length + k` where `k` is any integer satisfying `n < 256^k`.
    Used to bound `intToBytes`'s output size. -/
theorem intToBytesAux_length_le (k : Nat) :
    ∀ (n : Nat) (acc : List UInt8), n < 256^k →
      (intToBytesAux n acc).length ≤ k + acc.length := by
  induction k with
  | zero =>
    intro n acc h
    have h_n : n = 0 := by simp [Nat.pow_zero] at h; omega
    subst h_n
    unfold intToBytesAux
    simp
  | succ k' ih =>
    intro n acc h
    unfold intToBytesAux
    split
    · omega
    · rename_i h_nz
      have h_div : n / 256 < 256^k' := by
        rw [Nat.pow_succ] at h
        exact Nat.div_lt_iff_lt_mul (by decide) |>.mpr h
      have := ih (n / 256) (UInt8.ofNat (n % 256) :: acc) h_div
      simp [List.length_cons] at this
      omega

/-- `intToBytes n` has size ≤ `k` whenever `n < 256^k`. -/
theorem intToBytes_size_le (n k : Nat) (h : n < 256^k) :
    (intToBytes n).size ≤ k := by
  show (intToBytesAux n []).toArray.size ≤ k
  rw [List.size_toArray]
  have := intToBytesAux_length_le k n [] h
  simp at this
  exact this

/-- `intToBytes n` has size ≤ 32 whenever `n < 2^256`. The case used by
    `createAddress`: nonces are drawn from `UInt256`, so `n < 2^256`. -/
theorem intToBytes_size_le_32 (n : Nat) (h : n < 2^256) :
    (intToBytes n).size ≤ 32 := by
  apply intToBytes_size_le n 32
  have h_eq : (256 : Nat)^32 = 2^256 := by decide
  omega

/-- `lengthPrefix` returns `some` whenever the payload fits in 2^64 bytes. -/
theorem lengthPrefix_isSome {tagSmall tagLarge : UInt8} {n : Nat}
    (h : n < 2^64) : (lengthPrefix tagSmall tagLarge n).isSome := by
  unfold lengthPrefix
  by_cases h_small : n ≤ 55
  · simp [h_small]
  · simp [h_small]; exact h

/-- `encodeBytes bs` returns `some` whenever `bs.size < 2^64`. -/
theorem encodeBytes_isSome {bs : ByteArray} (h : bs.size < 2^64) :
    (encodeBytes bs).isSome := by
  unfold encodeBytes
  split
  · simp
  · have h_lp := lengthPrefix_isSome (tagSmall := 0x80) (tagLarge := 0xb7) h
    cases h_lp_eq : lengthPrefix 0x80 0xb7 bs.size with
    | none => rw [h_lp_eq] at h_lp; simp at h_lp
    | some _ => simp

/-- `encodeRawList` returns `some` whenever the concatenated payload
    fits in 2^64 bytes. -/
theorem encodeRawList_isSome {items : List ByteArray}
    (h : (items.foldl (· ++ ·) ByteArray.empty).size < 2^64) :
    (encodeRawList items).isSome := by
  unfold encodeRawList
  set payload := items.foldl (· ++ ·) ByteArray.empty with h_pay
  have h_lp := lengthPrefix_isSome (tagSmall := 0xc0) (tagLarge := 0xf7) (n := payload.size) h
  cases h_lp_eq : lengthPrefix 0xc0 0xf7 payload.size with
  | none => rw [h_lp_eq] at h_lp; simp at h_lp
  | some _ => simp [h_lp_eq]

/-- `addressBytes addr` has size 20 — the fixed-width 20-byte big-endian
    encoding of the address. The `Std.Range.forIn` in `natToBytesPadded`
    reduces (for the concrete `width = 20`) to a 20-element
    `Array UInt8` literal regardless of `addr.val`. -/
theorem addressBytes_size (addr : AccountAddress) :
    (addressBytes addr).size = 20 := by
  unfold addressBytes natToBytesPadded
  simp [Id.run, List.range']
  rfl

/-- `lengthPrefix` outputs at most 9 bytes (a single 1-byte tag, or a
    tag + up to 8 length bytes when the payload exceeds 55 bytes). -/
theorem lengthPrefix_size_le {tagSmall tagLarge : UInt8} {n : Nat} {p : ByteArray}
    (h_lp : lengthPrefix tagSmall tagLarge n = some p) : p.size ≤ 9 := by
  unfold lengthPrefix at h_lp
  split at h_lp
  · cases h_lp; show 1 ≤ 9; decide
  · split at h_lp
    · cases h_lp
      rw [ByteArray.size_append]
      have h_lt : n < 256^8 := by
        have : (256 : Nat)^8 = 2^64 := by decide
        rename_i hh; omega
      have := intToBytes_size_le n 8 h_lt
      show 1 + (intToBytes n).size ≤ 9
      omega
    · cases h_lp

/-- `encodeBytes bs` outputs at most `bs.size + 9` bytes. -/
theorem encodeBytes_size_le {bs ebs : ByteArray} (h : encodeBytes bs = some ebs) :
    ebs.size ≤ bs.size + 9 := by
  unfold encodeBytes at h
  split at h
  · cases h; omega
  · cases h_lp : lengthPrefix 0x80 0xb7 bs.size with
    | none => rw [h_lp] at h; simp at h
    | some p =>
      rw [h_lp] at h; simp at h; rw [← h, ByteArray.size_append]
      have := lengthPrefix_size_le h_lp
      omega

/-- `Rlp.encodeAddrNonce` returns `some` for any address and any nonce
    that fits in 256 bits — the payload (20-byte address + ≤32-byte
    stripped-Nat encoding of the nonce) is far below the `2^64`-byte
    cutoff of the RLP encoder. -/
theorem encodeAddrNonce_isSome (addr : AccountAddress) (nonce : Nat)
    (h_nonce : nonce < 2^256) :
    (encodeAddrNonce addr nonce).isSome := by
  have h_addr_sz : (addressBytes addr).size = 20 := addressBytes_size addr
  have h_nonce_sz : (intToBytes nonce).size ≤ 32 := intToBytes_size_le_32 nonce h_nonce
  have h_enc_addr : (encodeBytes (addressBytes addr)).isSome := by
    apply encodeBytes_isSome; rw [h_addr_sz]; decide
  have h_enc_nonce : (encodeBytes (intToBytes nonce)).isSome := by
    apply encodeBytes_isSome; omega
  obtain ⟨ea, h_ea⟩ := Option.isSome_iff_exists.mp h_enc_addr
  obtain ⟨en, h_en⟩ := Option.isSome_iff_exists.mp h_enc_nonce
  have h_ea_le : ea.size ≤ 29 := by
    have := encodeBytes_size_le h_ea
    rw [h_addr_sz] at this; omega
  have h_en_le : en.size ≤ 41 := by
    have := encodeBytes_size_le h_en
    omega
  unfold encodeAddrNonce encodeList Item.encode Item.ofAddress Item.ofNat
  show (List.mapM Item.encode [.bytes (addressBytes addr), .bytes (intToBytes nonce)] >>=
        encodeRawList).isSome
  rw [show List.mapM Item.encode
            [Item.bytes (addressBytes addr), Item.bytes (intToBytes nonce)]
        = some [ea, en] from by
    unfold List.mapM
    unfold List.mapM.loop
    simp [Item.encode, h_ea]
    unfold List.mapM.loop
    simp [Item.encode, h_en]
    unfold List.mapM.loop
    simp]
  show (encodeRawList [ea, en]).isSome
  apply encodeRawList_isSome
  show (List.foldl (· ++ ·) ByteArray.empty [ea, en]).size < 2^64
  simp [List.foldl, ByteArray.size_append]
  omega



end Rlp
end EvmSemantics
