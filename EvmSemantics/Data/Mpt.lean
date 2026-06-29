module

public import EvmSemantics.Data.Rlp
public import EvmSemantics.Crypto.Keccak256

/-!
`EvmSemantics.Mpt` — a minimal Modified Merkle Patricia Trie for
computing the Yellow Paper's `stateRoot` and per-account `storageRoot`
fields exposed by the BlockchainTests corpus.

We implement just the "trie of key-value pairs" view: given a finite
set of `(key, value)` pairs (the keys are full hash-length nibble
paths), build the canonical trie and return its 32-byte root hash. No
incremental updates, no persistent node store — the harness only
needs the root for comparison against the corpus, and rebuilding from
scratch on each call is fine for test workloads.

Three node shapes per Yellow Paper Appendix D:
* **Leaf**     `[compact(path, terminator=true), value]`
* **Extension** `[compact(path, terminator=false), childRef]`
* **Branch**   `[ch₀, ch₁, …, ch₁₅, value]` — 17 RLP items, each `chᵢ`
                is either inlined (encoding size `< 32`) or the
                32-byte keccak of the child's encoding.

The empty trie's root is the standard `keccak256(0x80)` — the hash
of the RLP-encoded empty byte string. -/

@[expose] public section

namespace EvmSemantics
namespace Mpt

/-- A nibble path: each entry is in `0..15`. -/
abbrev Nibbles := Array UInt8

/-- Split a byte array into nibbles (high-then-low per byte). -/
def toNibbles (bs : ByteArray) : Nibbles := Id.run do
  let mut ns : Array UInt8 := Array.mkEmpty (2 * bs.size)
  for i in [0:bs.size] do
    let b := bs[i]!
    ns := ns.push (b >>> 4)
    ns := ns.push (b &&& 0x0f)
  return ns

/-- Pack a nibble array (assumed even length) into bytes. -/
def packNibbles (ns : Array UInt8) : ByteArray := Id.run do
  let mut bs : Array UInt8 := Array.mkEmpty (ns.size / 2)
  let mut i := 0
  while i + 1 < ns.size + 1 ∧ i < ns.size do
    bs := bs.push ((ns[i]! <<< 4) ||| ns[i+1]!)
    i := i + 2
  return ByteArray.mk bs

/-- Hex-prefix (compact) encoding of a nibble path. The high nibble of
    the first byte holds two flags: `terminator` (1 if leaf, 0 if
    extension) and `oddLen` (1 if `|ns|` is odd). When `oddLen` is set
    the first path nibble shares that first byte; otherwise a `0`
    nibble pads. -/
def compactEncode (ns : Nibbles) (terminator : Bool) : ByteArray :=
  let t : UInt8 := if terminator then 2 else 0
  let odd       := ns.size % 2 = 1
  let oddBit    : UInt8 := if odd then 1 else 0
  let prefix2 : Array UInt8 :=
    if odd then #[((t ||| oddBit) <<< 4) ||| ns[0]!]
    else       #[(t ||| oddBit) <<< 4]
  -- Rest is even-length, pack pairs into bytes.
  let rest : Array UInt8 :=
    if odd then ns.toSubarray.toArray.extract 1 ns.size
    else ns
  let restPacked := packNibbles rest
  ByteArray.mk prefix2 ++ restPacked

/-- Longest common prefix of two nibble arrays. -/
def commonPrefixLen (a b : Nibbles) : Nat := Id.run do
  let n := Nat.min a.size b.size
  let mut i := 0
  while i < n ∧ a[i]! = b[i]! do i := i + 1
  return i

/-- Longest common prefix of a non-empty list of nibble arrays. -/
def commonPrefixAll (paths : List Nibbles) : Nat :=
  match paths with
  | []         => 0
  | p :: rest  => rest.foldl (fun k q => Nat.min k (commonPrefixLen p q)) p.size

/-- Drop the first `k` nibbles of a path. -/
def dropNibbles (ns : Nibbles) (k : Nat) : Nibbles :=
  ns.toSubarray.toArray.extract k ns.size

/-! ### Node encoding

`buildNode` produces the **RLP encoding** of a node from a list of
`(remainingPath, value)` pairs. `childRef` then turns that encoding
into the form a parent node embeds: inline if `< 32` bytes, otherwise
the 32-byte keccak hash wrapped as an RLP byte string. -/

/-- A child reference embedded in a parent: the child's encoding
    inline if `< 32` bytes, else the 32-byte keccak hash RLP-encoded
    as a byte string. -/
def childRef (enc : ByteArray) : ByteArray :=
  if enc.size < 32 then enc
  else Rlp.encodeBytes (Rlp.uint256ToBytes32 (EvmSemantics.keccak256 enc))

mutual

partial def buildNode (pairs : List (Nibbles × ByteArray)) : ByteArray :=
  match pairs with
  | [] =>
    Rlp.encodeBytes ByteArray.empty
  | [(path, value)] =>
    Rlp.encodeList [Rlp.encodeBytes (compactEncode path true),
                    Rlp.encodeBytes value]
  | _ =>
    let cp := commonPrefixAll (pairs.map (·.1))
    if cp > 0 then
      let stripped := pairs.map (fun (p, v) => (dropNibbles p cp, v))
      let prefixNibbles : Nibbles := (pairs.head!).1.toSubarray.toArray.extract 0 cp
      let childEnc := buildNode stripped
      Rlp.encodeList [Rlp.encodeBytes (compactEncode prefixNibbles false),
                      childRef childEnc]
    else
      buildBranch pairs

partial def buildBranch (pairs : List (Nibbles × ByteArray)) : ByteArray := Id.run do
  let mut buckets : Array (List (Nibbles × ByteArray)) := Array.replicate 16 []
  let mut value : Option ByteArray := none
  for (p, v) in pairs do
    if p.size = 0 then value := some v
    else
      let n := p[0]!.toNat
      buckets := buckets.set! n ((dropNibbles p 1, v) :: buckets[n]!)
  let mut items : List ByteArray := []
  for i in [0:16] do
    items := childRef (buildNode buckets[i]!) :: items
  items := items.reverse
  let valItem : ByteArray := match value with
    | none   => Rlp.encodeBytes ByteArray.empty
    | some v => Rlp.encodeBytes v
  return Rlp.encodeList (items ++ [valItem])

end

/-- The root hash of a trie holding the given `(key, value)` pairs.
    Keys are arbitrary `ByteArray`s — they are converted to nibble
    paths internally. Values are stored verbatim (the caller is
    responsible for any RLP encoding of structured values). -/
def rootHash (pairs : List (ByteArray × ByteArray)) : UInt256 :=
  match pairs with
  | [] => emptyTrieRoot
  | _  =>
    let nibblePairs := pairs.map (fun (k, v) => (toNibbles k, v))
    EvmSemantics.keccak256 (buildNode nibblePairs)
where
  /-- `keccak256(RLP empty string) = 0x56e81f17…3b421`. -/
  emptyTrieRoot : UInt256 :=
    EvmSemantics.keccak256 (Rlp.encodeBytes ByteArray.empty)

end Mpt

/-! ### Yellow-Paper roots over our `Storage` / `AccountMap`

The harness needs two outward-facing roots:
* `Storage.root`   — the per-account storage trie root
* `AccountMap.stateRoot` — the world-state trie root

Both iterate the runtime `cache` HashMap (the spec view's `toFun`
isn't enumerable). For storage we omit zero-valued slots per the
Yellow Paper convention; for the world trie we omit "empty" accounts
(EIP-161). -/

namespace Storage

/-- The 20-byte→nibble-key part of the storage trie. The MPT key is
    `keccak256(slot.toBytes32)`; the value is the slot's RLP-encoded
    integer value (stripped big-endian). -/
def root (s : Storage) : UInt256 :=
  let entries := s.cache.toList.filter (fun (_, v) => v.toNat ≠ 0)
  let pairs : List (ByteArray × ByteArray) := entries.map (fun (k, v) =>
    let keyHash := EvmSemantics.keccak256 (Rlp.uint256ToBytes32 k)
    (Rlp.uint256ToBytes32 keyHash, Rlp.encodeInt v.toNat))
  Mpt.rootHash pairs

end Storage

namespace Account

/-- `keccak256(<empty>) = 0xc5d2460186f7233c927e7db2dcc703c0e500b653…
    a470`. Hard-coded as a `UInt256` so the trie value for an account
    with no code is computable without re-hashing. -/
def emptyCodeHash : UInt256 :=
  EvmSemantics.keccak256 ByteArray.empty

/-- RLP-encode `[nonce, balance, storageRoot, codeHash]`, the trie
    value for an account in the world-state MPT. -/
def encodeForTrie (a : Account) : ByteArray :=
  let sroot := if a.storage.cache.isEmpty then
                 EvmSemantics.keccak256 (Rlp.encodeBytes ByteArray.empty)
               else Storage.root a.storage
  let chash := if a.code.size = 0 then emptyCodeHash
               else EvmSemantics.keccak256 a.code
  Rlp.encodeList
    [ Rlp.encodeInt a.nonce.toNat
    , Rlp.encodeInt a.balance.toNat
    , Rlp.encodeBytes (Rlp.uint256ToBytes32 sroot)
    , Rlp.encodeBytes (Rlp.uint256ToBytes32 chash) ]

end Account

namespace AccountMap

/-- The world-state trie root: `keccak256(addr.toBytes20)` keys mapping
    to `RLP([nonce, balance, storageRoot, codeHash])` values. Accounts
    that are EIP-161 *empty* (zero nonce, zero balance, no code,
    no storage) are omitted. -/
def stateRoot (σ : AccountMap) : UInt256 :=
  let entries := σ.cache.toList
  let pairs : List (ByteArray × ByteArray) := entries.map (fun (addr, a) =>
    let keyHash := EvmSemantics.keccak256 (Rlp.addressBytes addr)
    (Rlp.uint256ToBytes32 keyHash, Account.encodeForTrie a))
  Mpt.rootHash pairs

end AccountMap

end EvmSemantics
