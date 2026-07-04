module

public import Lean.Data.Json
public import EvmSemantics
public import EvmSemantics.Data.Hex

/-!
`RlpTestRunner` — JSON driver for the `ethereum/tests` **RLPTests** suite.

Each fixture pairs an `in` value with its canonical RLP encoding `out`:

* an ordinary `in` (a JSON string, number, or arbitrarily nested list) must
  **encode** to exactly `out` — strings encode their UTF-8 bytes, numbers
  their stripped big-endian form, and a string beginning with `#` is a
  decimal bignum (`#1024` encodes the *integer* 1024, exercising scalars
  past 2⁶⁴);
* `in = "INVALID"` (`invalidRLPTest.json`) means `out` is a malformed or
  non-canonical encoding our decoder must **reject** — truncated payloads,
  wrong-size lists, leading zeros in a long length, a single byte `< 0x80`
  behind a length prefix, …;
* `in = "VALID"` (`RandomRLPTests`) means `out` must merely **decode**.

This is direct conformance for `EvmSemantics.Rlp` / `Rlp.decode` — the codec
under every transaction decode (sender recovery), the MPT node encodings
behind the `passRoot` tier, and the CREATE address derivation. The
TransactionTests `ttWrongRLP` cases exercise the decoder only through whole
transactions; this suite pins the codec down value-by-value.

Output format is identical to the `txtests` runner
(`pass=… fail=… incon=… crash=… (total …)` + per-test `FAIL <id>: …` notes),
so the CI shard reuses `txtests_run.sh` (via the `TXTESTS_BIN` override) and
`txtests_summary.sh` against this suite's own expected-failures baseline.
-/

@[expose] public section

namespace RlpTests

open EvmSemantics Lean

open EvmSemantics.Hex

----------------------------------------------------------------------------
-- JSON helpers (mirrors the other runners).
----------------------------------------------------------------------------

def strField (j : Json) (k : String) : String := (j.getObjValAs? String k).toOption.getD ""

def subObj (j : Json) (k : String) : Json := (j.getObjVal? k).toOption.getD Json.null

----------------------------------------------------------------------------
-- `in` value → RLP item.
----------------------------------------------------------------------------

/-- Build the `Rlp.Item` a fixture's `in` value denotes: a string encodes its
    UTF-8 bytes (a leading `#` marks a decimal bignum, encoded as a stripped
    big-endian scalar), a number encodes as a scalar, and a list recurses.
    `none` for shapes RLPTests never uses (objects, floats, negatives). -/
partial def jsonToItem : Json → Option Rlp.Item
  | .str s =>
    if s.startsWith "#" then
      ((s.drop 1).toNat?).map Rlp.Item.ofNat
    else some (.ofByteArray s.toUTF8)
  | .num n =>
    if n.exponent == 0 ∧ n.mantissa ≥ 0 then some (.ofNat n.mantissa.toNat)
    else none
  | .arr a => do
    let items ← a.toList.mapM jsonToItem
    pure (.list items)
  | _ => none

----------------------------------------------------------------------------
-- Per-test evaluation.
----------------------------------------------------------------------------

/-- Outcome of one fixture. -/
inductive Outcome where
  | pass
  | fail  : String → Outcome
  | incon : String → Outcome
  deriving Inhabited

/-- Run one RLPTests fixture. -/
def runTest (testObj : Json) : Outcome :=
  let inJson := subObj testObj "in"
  let outBytes := hexToBytes (strField testObj "out")
  match inJson with
  | .str "INVALID" =>
    -- The encoding must be rejected by the canonical decoder.
    match Rlp.decode outBytes with
    | none   => .pass
    | some _ => .fail "decoder accepted an invalid encoding"
  | .str "VALID" =>
    match Rlp.decode outBytes with
    | some _ => .pass
    | none   => .fail "decoder rejected a valid encoding"
  | _ =>
    match jsonToItem inJson with
    | none => .incon "unsupported `in` shape"
    | some item =>
      match item.encode with
      | none => .fail "encoder returned none"
      | some enc =>
        if enc.toList ≠ outBytes.toList then
          .fail s!"encoding mismatch: got 0x{bytesToHex enc}, expected 0x{bytesToHex outBytes}"
        -- The canonical encoding must also round-trip through the decoder.
        else if (Rlp.decode outBytes).isNone then
          .fail "decoder rejected the canonical encoding"
        else .pass

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

/-- Run every test in one file; one `(tag, id, msg)` per test key. -/
def runFileResults (path : System.FilePath) :
    IO (Array (String × String × String)) := do
  let txt ← IO.FS.readFile path
  match Json.parse txt with
  | .error e => return #[("CRASH", path.fileName.getD path.toString, s!"parse: {e}")]
  | .ok j =>
    let tests := match j with | .obj m => m.toArray.toList | _ => []
    let fileTag := ((path.fileName.getD "").replace ".json" "")
    let mut out := #[]
    for (testName, testObj) in tests do
      let id := s!"{fileTag}_{sanitize testName}"
      let r : String × String × String :=
        match runTest testObj with
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

/-- Entry point: `rlptests [-v] [-j N] <dir-or-file>`. -/
def main (args : List String) : IO Unit := do
  let verbose := args.contains "-v"
  let (jobs0, rest) := parseFlags (args.filter (· != "-v"))
  let jobs ← if jobs0 > 0 then pure jobs0 else do
    match (← IO.getEnv "RLPTESTS_JOBS") with
    | some s => pure (Nat.max 1 s.toNat!)
    | none   => pure 8
  let root : System.FilePath := rest.headD "."
  let files ← if (← root.isDir) then collectJson root else pure #[root]
  let t ← runFiles files jobs verbose
  IO.println s!"pass={t.pass} fail={t.fail} incon={t.incon} crash={t.crash} (total {t.total})"

end RlpTests

def main (args : List String) : IO Unit := RlpTests.main args
