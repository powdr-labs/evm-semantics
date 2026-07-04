module

public import Lean.Data.Json
public import EvmSemantics
public import EvmSemantics.Data.Hex

/-!
`TrieTestRunner` — JSON driver for the `ethereum/tests` **TrieTests** suite.

Each fixture gives a set of key/value operations (`in`) and the expected MPT
root hash (`root`). `in` is either an *ordered* list of `[key, value]` pairs —
where a `null` (or empty) value **deletes** the key, so order matters — or an
unordered `{key: value}` object. A key/value string starting with `0x` is hex;
anything else is its UTF-8 bytes. The `*secureTrie*` fixtures build the
*secure* trie: each key is `keccak256(key)` (the transformation under both the
world-state and storage tries).

Since our `Mpt.rootHash` builds the canonical trie from a *final* key/value
set (no incremental updates — see `EvmSemantics/Data/Mpt.lean`), the runner
folds the operations into a map first (insert / overwrite / delete in order)
and hands the surviving pairs to `Mpt.rootHash`. The canonical trie of the
final set is exactly what the incremental updates in the reference clients
produce, so this tests the same object.

This is direct conformance for the MPT behind the `passRoot` tier of every
state/blockchain runner — until now it was exercised only end-to-end through
whole state roots. `trietestnextprev.json` tests iterator (`next`/`prev`)
semantics we don't model; its cases are reported `INCON` so they land in the
baseline rather than counting as failures.

Output format is identical to the `txtests` runner
(`pass=… fail=… incon=… crash=… (total …)` + per-test `FAIL <id>: …` notes),
so the CI shard reuses `txtests_run.sh` (via the `TXTESTS_BIN` override) and
`txtests_summary.sh` against this suite's own expected-failures baseline.
-/

@[expose] public section

namespace TrieTests

open EvmSemantics Lean

open EvmSemantics.Hex

----------------------------------------------------------------------------
-- JSON helpers (mirrors the other runners).
----------------------------------------------------------------------------

def strField (j : Json) (k : String) : String := (j.getObjValAs? String k).toOption.getD ""

def subObj (j : Json) (k : String) : Json := (j.getObjVal? k).toOption.getD Json.null

def hasField (j : Json) (k : String) : Bool := (j.getObjVal? k).toOption.isSome

def jsonArr (j : Json) : Array Json :=
  match j with | .arr a => a | _ => #[]

----------------------------------------------------------------------------
-- Key/value decoding and operation folding.
----------------------------------------------------------------------------

/-- Fixture string → bytes: `0x…` is hex, anything else UTF-8. -/
def strBytes (s : String) : ByteArray :=
  if s.startsWith "0x" then hexToBytes s else s.toUTF8

/-- One `[key, value]` operation: `none` value = delete. -/
def parseOp (j : Json) : Option (ByteArray × Option ByteArray) :=
  match j with
  | .arr a =>
    match a[0]?, a[1]? with
    | some (Json.str k), some (Json.str v) => some (strBytes k, some (strBytes v))
    | some (Json.str k), some Json.null    => some (strBytes k, none)
    | _, _ => none
  | _ => none

/-- The fixture's operations in application order: the pairs of an `in` list
    verbatim, or an `in` object's entries (order irrelevant there — objects
    carry no deletes). `none` if some entry has a shape we don't recognise. -/
def parseOps (inJson : Json) : Option (List (ByteArray × Option ByteArray)) :=
  match inJson with
  | .arr a => a.toList.mapM parseOp
  | .obj m => m.toArray.toList.mapM (fun (k, v) =>
      match v with
      | .str s => some (strBytes k, some (strBytes s))
      | .null  => some (strBytes k, none)
      | _      => none)
  | _ => none

/-- Apply the operations in order (insert / overwrite / delete) and return
    the surviving key/value pairs. Keys are tracked by their lowercase-hex
    spelling (`ByteArray` has no `Hashable` instance); an *empty* value
    deletes like a `null` one — the trie stores only non-empty values, and
    the reference clients treat an empty-value update as a removal. -/
def applyOps (ops : List (ByteArray × Option ByteArray)) :
    List (ByteArray × ByteArray) := Id.run do
  let mut m : Std.HashMap String (ByteArray × ByteArray) := ∅
  for (k, v) in ops do
    let hk := bytesToHex k
    match v with
    | some vb =>
      if vb.size = 0 then m := m.erase hk
      else m := m.insert hk (k, vb)
    | none => m := m.erase hk
  return m.toList.map (·.2)

----------------------------------------------------------------------------
-- Per-test evaluation.
----------------------------------------------------------------------------

/-- Outcome of one fixture. -/
inductive Outcome where
  | pass
  | fail  : String → Outcome
  | incon : String → Outcome
  deriving Inhabited

/-- Run one TrieTests fixture. `secure` hashes each key
    (`keccak256(key)`, 32-byte path) before building the trie. -/
def runTest (testObj : Json) (secure : Bool) : Outcome :=
  if ¬ hasField testObj "root" then
    .incon "no root field (next/prev iterator semantics not modelled)"
  else
    match parseOps (subObj testObj "in") with
    | none => .incon "unsupported `in` shape"
    | some ops =>
      let pairs := applyOps ops
      let pairs := if secure then
          pairs.map (fun (k, v) =>
            (Rlp.uint256ToBytes32 (EvmSemantics.keccak256 k), v))
        else pairs
      match Mpt.rootHash pairs with
      | none => .fail "root uncomputable (RLP encode overflow)"
      | some r =>
        let expected := hexToUInt256 (strField testObj "root")
        if r.toNat == expected.toNat then .pass
        else .fail s!"root mismatch: got 0x{bytesToHex (Rlp.uint256ToBytes32 r)}, \
expected {strField testObj "root"}"

----------------------------------------------------------------------------
-- Tally, driver, CLI (mirrors TransactionTestRunner).
----------------------------------------------------------------------------

structure Tally where
  pass  : Nat := 0
  fail  : Nat := 0
  incon : Nat := 0
  crash : Nat := 0
  deriving Inhabited

def Tally.total (t : Tally) : Nat := t.pass + t.fail + t.incon + t.crash

partial def collectJson (dir : System.FilePath) : IO (Array System.FilePath) := do
  let mut out : Array System.FilePath := #[]
  for ent in (← dir.readDir) do
    let path := ent.path
    if (← path.isDir) then out := out ++ (← collectJson path)
    else if path.toString.endsWith ".json" then out := out.push path
  return out.qsort (fun a b => a.toString < b.toString)

/-- Sanitize a test name into an id-safe token (no spaces/colons). -/
def sanitize (s : String) : String := (s.replace " " "_").replace ":" "_"

/-- Run every test in one file; one `(tag, id, msg)` per test key. The
    *secure*-trie fixtures are recognised by file name (`…securetrie…`). -/
def runFileResults (path : System.FilePath) :
    IO (Array (String × String × String)) := do
  let txt ← IO.FS.readFile path
  match Json.parse txt with
  | .error e => return #[("CRASH", path.fileName.getD path.toString, s!"parse: {e}")]
  | .ok j =>
    let tests := match j with | .obj m => m.toArray.toList | _ => []
    let fileTag := ((path.fileName.getD "").replace ".json" "")
    let secure := (fileTag.toLower.splitOn "securetrie").length > 1
    let mut out := #[]
    for (testName, testObj) in tests do
      let id := s!"{fileTag}_{sanitize testName}"
      let r : String × String × String :=
        match runTest testObj secure with
        | .pass    => ("PASS", id, "")
        | .fail m  => ("FAIL", id, m)
        | .incon m => ("INCON", id, m)
      out := out.push r
    return out

/-- Run `files` with up to `jobs` tasks in flight. -/
def runFiles (files : Array System.FilePath) (jobs : Nat) (verbose : Bool) :
    IO Tally := do
  let mut t : Tally := {}
  let n := files.size
  if n = 0 then return t
  let workers := Nat.max 1 jobs
  let mut slots : Array (Option (Task (Except IO.Error (Array (String × String × String))))) :=
    Array.replicate workers none
  let mut nextIdx : Nat := 0
  let mut remaining : Nat := n
  let fold : Tally → Except IO.Error (Array (String × String × String)) → IO Tally :=
    fun t r => do
      let mut t := t
      match r with
      | .ok results =>
        for (tag, name, msg) in results do
          match tag with
          | "PASS"  => t := { t with pass := t.pass + 1 }
          | "FAIL"  => t := { t with fail := t.fail + 1 }
                       if verbose then IO.println s!"FAIL {name}: {msg}"
          | "INCON" => t := { t with incon := t.incon + 1 }
                       if verbose then IO.println s!"INCON {name}: {msg}"
          | _       => t := { t with crash := t.crash + 1 }
                       if verbose then IO.println s!"CRASH {name}: {msg}"
      | .error e =>
        t := { t with crash := t.crash + 1 }
        if verbose then IO.println s!"CRASH (task): {e}"
      return t
  for i in [0:workers] do
    if nextIdx < n then
      let task ← IO.asTask (runFileResults files[nextIdx]!) Task.Priority.dedicated
      slots := slots.set! i (some task)
      nextIdx := nextIdx + 1
  while remaining > 0 do
    let mut progress := false
    for i in [0:workers] do
      match slots[i]! with
      | none => pure ()
      | some task =>
        if (← IO.hasFinished task) then
          t ← fold t (← IO.wait task)
          remaining := remaining - 1
          progress := true
          if nextIdx < n then
            let next ← IO.asTask (runFileResults files[nextIdx]!) Task.Priority.dedicated
            slots := slots.set! i (some next)
            nextIdx := nextIdx + 1
          else
            slots := slots.set! i none
    if !progress then IO.sleep 5
  return t

/-- Parse `-j N` out of `args`; returns `(jobs (0 = unset), remaining)`. -/
def parseFlags (args : List String) : Nat × List String := Id.run do
  let rec go : List String → Option Nat → List String → Nat × List String
    | [], j, acc => (j.getD 0, acc.reverse)
    | "-j" :: v :: rest, _, acc => go rest (some v.toNat!) acc
    | x :: rest, j, acc => go rest j (x :: acc)
  go args none []

/-- Entry point: `trietests [-v] [-j N] <dir-or-file>`. -/
def main (args : List String) : IO Unit := do
  let verbose := args.contains "-v"
  let (jobs0, rest) := parseFlags (args.filter (· != "-v"))
  let jobs ← if jobs0 > 0 then pure jobs0 else do
    match (← IO.getEnv "TRIETESTS_JOBS") with
    | some s => pure (Nat.max 1 s.toNat!)
    | none   => pure 8
  let root : System.FilePath := rest.headD "."
  let files ← if (← root.isDir) then collectJson root else pure #[root]
  let t ← runFiles files jobs verbose
  IO.println s!"pass={t.pass} fail={t.fail} incon={t.incon} crash={t.crash} (total {t.total})"

end TrieTests

def main (args : List String) : IO Unit := TrieTests.main args
