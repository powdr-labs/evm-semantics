import EvmSemantics

open EvmSemantics

namespace MptSmoke

/-- Format a `UInt256` as a 64-char hex string (no `0x` prefix). -/
def hex64 (v : UInt256) : String :=
  let bs := Rlp.uint256ToBytes32 v
  let dig (n : Nat) : Char :=
    if n < 10 then Char.ofNat (n + '0'.toNat)
    else Char.ofNat (n - 10 + 'a'.toNat)
  bs.toList.foldl (fun s b =>
    s.push (dig (b.toNat / 16)) |>.push (dig (b.toNat % 16))) ""

/-- `keccak256(0x80)` — the canonical empty-trie root. -/
def emptyTrieRootExpected : String :=
  "56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421"

/-- `keccak256(<empty>)` — the canonical empty-code hash. -/
def emptyCodeHashExpected : String :=
  "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"

/-- A single-entry MPT: key = keccak256(`uint256(0).toBytes32`),
    value = `RLP(0x01)`. The expected root is the leaf node directly. -/
def go : IO Unit := do
  -- Empty trie root.
  let emptyRoot := Mpt.rootHash []
  IO.println s!"empty trie root: {hex64 emptyRoot}"
  IO.println s!"  expected      : {emptyTrieRootExpected}"
  IO.println s!"  ok            : {hex64 emptyRoot == emptyTrieRootExpected}"

  -- Empty code hash.
  let codeHash := Account.emptyCodeHash
  IO.println s!"empty code hash: {hex64 codeHash}"
  IO.println s!"  expected      : {emptyCodeHashExpected}"
  IO.println s!"  ok            : {hex64 codeHash == emptyCodeHashExpected}"

  -- Storage with one non-zero slot: slot 0 = 1.
  let mut s : Storage := Storage.empty
  s := s.set (UInt256.ofNat 0) (UInt256.ofNat 1)
  let r := Storage.root s
  IO.println s!"storage[0]=1 root: {hex64 r}"
  -- Expected: keccak256(rlp([compact(nibbles(keccak256(0x00…00)), leaf=true),
  --                          rlp(0x01) = 0x01])). Known mainnet test vector:
  --   keccak256(0x0000…00) = 0x290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563
  --   leaf = [<compact path of 64 nibbles, terminator=true>, 0x01]
  --   leaf RLP > 32 bytes, so root = keccak256(leaf RLP).
  IO.println s!"  expected      : 821e2556a290c86405f8160a2d662042a431ba456b9db265c79bb837c04be5f0"

end MptSmoke

def main : IO Unit := MptSmoke.go
