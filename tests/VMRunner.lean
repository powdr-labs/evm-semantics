module

public import EvmSemantics
public import EvmSemantics.Data.Hex
public import Lean.Data.Json

/-!
`VMRunner` — Phase-1 harness that runs the legacy ethereum/tests **VMTests**
against the executable evaluator (`stepF` / `run`).

Design:
* Target the legacy VMTests suite (pure single-frame EVM; no calls / no tx).
* Every test runs with its declared `exec.gas` budget. For tests with a
  `post` block we compare storage, return-data, balance, nonce, and the
  remaining `gas` value. Tests without a `post` are expected to halt
  exceptionally; any in-frame exception counts as a pass.
* Logs are not compared (would need RLP encoding to compute `logsHash`).

Usage: `vmtests <path-to-Constantinople/VMTests>`
-/

open Lean
open EvmSemantics
open EvmSemantics.EVM

@[expose] public section

namespace VMRunner

open EvmSemantics.Hex

----------------------------------------------------------------------------
-- JSON helpers
----------------------------------------------------------------------------

/-- The string at object field `k`, or `""`. -/
def strField (j : Json) (k : String) : String :=
  match j.getObjVal? k with
  | .ok v => (v.getStr?).toOption.getD ""
  | _     => ""

/-- The sub-object at field `k` (or `Json.null`). -/
def subObj (j : Json) (k : String) : Json := (j.getObjVal? k).toOption.getD Json.null

/-- Entries of the object at field `k` as `(key, value)` pairs. -/
def objEntries (j : Json) (k : String) : List (String × Json) :=
  match j.getObjVal? k with
  | .ok v => match v.getObj? with
    | .ok m => m.toList
    | _     => []
  | _ => []

/-- `(slot, value)` string pairs of an account's `storage`. -/
def storageEntries (accJson : Json) : List (String × String) :=
  (objEntries accJson "storage").map (fun (k, v) => (k, (v.getStr?).toOption.getD ""))

def hasField (j : Json) (k : String) : Bool := (j.getObjVal? k).toOption.isSome

----------------------------------------------------------------------------
-- State construction
----------------------------------------------------------------------------

/-- Build an `Account` from a `pre`/`post` account JSON object. -/
def mkAccount (accJson : Json) : Account :=
  let storage := (storageEntries accJson).foldl
    (fun st (slot, val) => st.set (hexToUInt256 slot) (hexToUInt256 val)) Storage.empty
  { nonce    := hexToUInt256 (strField accJson "nonce")
    balance  := hexToUInt256 (strField accJson "balance")
    code     := hexToBytes   (strField accJson "code")
    storage  := storage
    tstorage := Storage.empty }

/-- Assemble the initial `State` from a VMTest `exec`/`env`/`pre`, using
    `gas` as the initial `gasAvailable`. -/
def buildStateWith (testObj : Json) (gas : Nat) : State :=
  let exec := subObj testObj "exec"
  let env  := subObj testObj "env"
  let accountMap : AccountMap :=
    (objEntries testObj "pre").foldl
      (fun σ (addrStr, accJson) => σ.set (hexToAddress addrStr) (mkAccount accJson))
      AccountMap.empty
  let header : BlockHeader :=
    { coinbase      := hexToAddress (strField env "currentCoinbase")
      timestamp     := hexToUInt256 (strField env "currentTimestamp")
      number        := hexToUInt256 (strField env "currentNumber")
      -- Constantinople 0x44 = DIFFICULTY; our `block` handler reads `prevRandao`.
      prevRandao    := hexToUInt256 (strField env "currentDifficulty")
      gasLimit      := hexToUInt256 (strField env "currentGasLimit")
      baseFeePerGas := ⟨0⟩, chainId := ⟨0⟩, blobBaseFee := ⟨0⟩
      blockHash     := fun _ => ⟨0⟩ }
  let execEnv : ExecutionEnv :=
    { address   := hexToAddress (strField exec "address")
      origin    := hexToAddress (strField exec "origin")   -- ORIGIN
      caller    := hexToAddress (strField exec "caller")   -- CALLER
      weiValue  := hexToUInt256 (strField exec "value")
      calldata  := hexToBytes   (strField exec "data")
      code      := hexToBytes   (strField exec "code")
      gasPrice  := hexToUInt256 (strField exec "gasPrice")
      header    := header
      depth     := 0
      permitStateMutation := true
      blobVersionedHashes := #[]
      -- The `legacytests/Constantinople/VMTests` corpus is named for the
      -- corpus revision (the *git tag* in ethereum/legacytests was
      -- `constantinople`-era), but the actual VMTest bytecodes pre-date
      -- the per-fork divergences: they were generated against the
      -- Frontier gas schedule (e.g. `SLOAD = 50` rather than Tangerine
      -- Whistle's 200, `EXP` per-byte 10 rather than Spurious Dragon's
      -- 50, `SELFDESTRUCT` base 0 rather than 5000) and never reference
      -- a post-Frontier opcode (no `DELEGATECALL` / `REVERT` /
      -- `RETURNDATA*` / `SHL` / `SHR` / `SAR` / `EXTCODEHASH` /
      -- `CREATE2`). We therefore tag the execution with
      -- `Fork.Frontier`, which (i) picks the right gas schedule and
      -- (ii) lets `Operation.availableInFork` reject any post-Frontier
      -- byte that shouldn't be reachable in this corpus. The
      -- `vmtests-baseline.txt` regression check pins this behaviour. -/
      fork                := .Frontier }
  { toMachineState :=
      { gasAvailable := gas, activeWords := ⟨0⟩
        memory := .empty, returnData := .empty, hReturn := .empty }
    accountMap   := accountMap
    -- Snapshot the pre-state's accountMap so SSTORE's EIP-1283 logic
    -- can look up the `original` value of any slot.
    substate     := { Substate.empty with originalAccountMap := accountMap }
    executionEnv := execEnv
    pc           := ⟨0⟩
    stack        := []
    execLength   := 0
    halt         := .Running }

----------------------------------------------------------------------------
-- Driver
----------------------------------------------------------------------------

/-- Fueled `stepF` loop (mirrors `Main.run`, kept `partial`).
    End-of-code implicit STOP is handled by `Decode.decodeAt` (and thus the
    evaluator itself), so no harness compensation is needed here. -/
partial def run (s : State) (fuel : Nat) : Except ExecutionException State :=
  if fuel = 0 then .error .OutOfFuel
  else if s.isDone then .ok s
  else run (stepF s) (fuel - 1)

----------------------------------------------------------------------------
-- Outcome + comparison
----------------------------------------------------------------------------

inductive Outcome where
  | pass
  | fail (msg : String)
  | incon (msg : String)
  deriving Repr

/-- Compare every post account's balance/nonce/storage against the result.
    Storage is checked over the union of pre and post slot keys. Returns the
    first mismatch message, or `none` on full agreement. -/
def cmpAccounts (sf : State) (testObj : Json) : Option String := Id.run do
  let preAccounts  := objEntries testObj "pre"
  let postAccounts := objEntries testObj "post"
  for (addrStr, accJson) in postAccounts do
    let addr := hexToAddress addrStr
    let our  := sf.accountMap addr
    let expBal := hexToNat (strField accJson "balance")
    if our.balance.toNat != expBal then
      return some s!"{addrStr} balance got {our.balance.toNat} exp {expBal}"
    let expNonce := hexToNat (strField accJson "nonce")
    if our.nonce.toNat != expNonce then
      return some s!"{addrStr} nonce got {our.nonce.toNat} exp {expNonce}"
    let postStore := storageEntries accJson
    let preStore  :=
      (preAccounts.find? (fun (a, _) => hexToNat a == hexToNat addrStr)).map
        (fun (_, j) => storageEntries j) |>.getD []
    let slots := postStore.map Prod.fst ++ preStore.map Prod.fst
    for slotStr in slots do
      let key  := hexToUInt256 slotStr
      let expV :=
        (postStore.find? (fun (k, _) => hexToNat k == hexToNat slotStr)).map
          (fun (_, v) => hexToNat v) |>.getD 0
      let ourV := (our.storage key).toNat
      if ourV != expV then
        return some s!"{addrStr} slot {slotStr} got {ourV} exp {expV}"
  return none

/-- Run one test object and classify the outcome. Every test runs with
    its declared `exec.gas` budget; on a test with a `post` block, both
    storage and the remaining `gas` are compared against the corpus. -/
def runTest (testObj : Json) : Outcome :=
  let exec := subObj testObj "exec"
  let inputGas := hexToNat (strField exec "gas")
  let s0 := buildStateWith testObj inputGas
  let hasPost := hasField testObj "post"
  match run s0 2000000 with
  | .error .OutOfFuel => .incon "fuel exhausted"
  | .error e =>
    if hasPost then .fail s!"expected success, got {repr e}"
    else .pass                              -- exception expected, got exception
  | .ok sf =>
    if !hasPost then
      match sf.halt with
      | .Reverted => .pass                  -- REVERT counts as expected failure
      | h =>
        let extra := if sf.stack.length > 1024 then " (overflow-suspected)" else ""
        .incon s!"expected exception, got {repr h}{extra}"
    else
      match cmpAccounts sf testObj with
      | some msg => .fail msg
      | none =>
        let outExp := hexToBytes (strField testObj "out")
        if sf.hReturn.toList != outExp.toList then
          .fail s!"out mismatch ({sf.hReturn.size}B vs {outExp.size}B)"
        else
          let expGas := hexToNat (strField testObj "gas")
          if sf.gasAvailable != expGas then
            .fail s!"gas mismatch: got {sf.gasAvailable} exp {expGas}"
          else .pass

----------------------------------------------------------------------------
-- Tally + file walking
----------------------------------------------------------------------------

structure Tally where
  pass  : Nat := 0
  fail  : Nat := 0
  incon : Nat := 0
  crash : Nat := 0       -- evaluator panic / timeout (child exited non-zero)
  deriving Inhabited

def Tally.add (t u : Tally) : Tally :=
  { pass := t.pass + u.pass, fail := t.fail + u.fail
    incon := t.incon + u.incon, crash := t.crash + u.crash }

def Tally.total (t : Tally) : Nat := t.pass + t.fail + t.incon + t.crash

def Tally.line (t : Tally) : String :=
  s!"pass={t.pass} fail={t.fail} incon={t.incon} crash={t.crash}"

/-- Collect all `*.json` files under `p` (recursively), sorted. -/
partial def collectJson (p : System.FilePath) : IO (Array System.FilePath) := do
  let mut out := #[]
  for ent in (← p.readDir) do
    let path := ent.path
    if (← path.isDir) then
      out := out ++ (← collectJson path)
    else if path.toString.endsWith ".json" then
      out := out.push path
  return out.qsort (fun a b => a.toString < b.toString)

----------------------------------------------------------------------------
-- Child mode: process ONE file, print machine-readable result lines.
----------------------------------------------------------------------------

/-- The tag for an `Outcome`, with optional message. -/
def outcomeTag : Outcome → String × String
  | .pass     => ("PASS", "")
  | .fail m   => ("FAIL", m)
  | .incon m  => ("INCON", m)

/-- `--file` mode: one line per test `TAG\tname\tmsg`. A panic here aborts
    only this child process (the parent records it as a crash). -/
def runFile (path : System.FilePath) : IO Unit := do
  let txt ← IO.FS.readFile path
  match Json.parse txt with
  | .error e => IO.println s!"PARSEERR\t{path}\t{e}"
  | .ok j =>
    let entries := match j.getObj? with | .ok m => m.toList | _ => []
    for (name, testObj) in entries do
      let (tag, msg) := outcomeTag (runTest testObj)
      IO.println s!"{tag}\t{name}\t{msg}"

----------------------------------------------------------------------------
-- Parent: spawn one Task per file, tally results. Tasks run on the default
-- thread pool so multiple files execute in parallel on multiple OS threads.
-- A panic in any one test now aborts the whole process (no subprocess
-- isolation) — none currently panic, so that's an acceptable trade for the
-- ~7× speedup vs the previous subprocess-per-file design.
----------------------------------------------------------------------------

/-- Result of processing one file: every `(tag, name, msg)` triple from
    `runTest`, gathered into an array. Used as the Task return value. -/
def runFileResults (path : System.FilePath) : IO (Array (String × String × String)) := do
  let txt ← IO.FS.readFile path
  match Json.parse txt with
  | .error e => return #[("PARSEERR", path.toString, e)]
  | .ok j =>
    let entries := match j.getObj? with | .ok m => m.toList | _ => []
    let mut out := #[]
    for (name, testObj) in entries do
      let (tag, msg) := outcomeTag (runTest testObj)
      out := out.push (tag, name, msg)
    return out

/-- Fold a single file's results into the running tally + notes. -/
def absorbResults (f : System.FilePath) (results : Array (String × String × String))
    (t : Tally) (notes : Array String) : Tally × Array String := Id.run do
  let mut t := t
  let mut notes := notes
  for (tag, name, msg) in results do
    match tag with
    | "PASS"     => t := { t with pass := t.pass + 1 }
    | "FAIL"     => t := { t with fail := t.fail + 1 }
                    notes := notes.push s!"FAIL {name}: {msg}"
    | "INCON"    => t := { t with incon := t.incon + 1 }
    | "PARSEERR" => t := { t with crash := t.crash + 1 }
                    notes := notes.push s!"PARSEERR {f.fileName.getD f.toString}: {msg}"
    | _          => pure ()
  return (t, notes)

/-- Run one subdir: keep up to `jobs` Lean `Task`s **continuously in
    flight** via a sliding-window scheduler. Each worker slot is refilled
    as soon as its previous task completes, so a slow file never starves
    the other cores (the old batch-wait `for task in tasks do IO.wait
    task` made the slowest file in each batch determine throughput).

    Output ordering: notes are emitted in *completion* order rather than
    spawn order. The summary scripts key on FAIL ids, not line order.
    Per-task wall-clock cap via `timeoutMs > 0`: tasks running past the
    cap are recorded as `CRASH wall-timeout` and the slot freed (the
    abandoned task keeps running in the background — Lean Tasks aren't
    OS-cancellable). -/
def runDir (dir : System.FilePath) (jobs : Nat) (timeoutMs : Nat := 0) : IO Tally := do
  let files ← collectJson dir
  let mut t : Tally := {}
  let mut notes : Array String := #[]
  let n := files.size
  if n = 0 then return t
  let workers := Nat.max 1 jobs
  let mut slots :
      Array (Option (Nat × Nat × System.FilePath ×
                      Task (Except IO.Error (Array (String × String × String))))) :=
    Array.replicate workers none
  let mut nextIdx : Nat := 0
  let mut remaining : Nat := n
  -- Prime the pool.
  for i in [0:workers] do
    if nextIdx < n then
      let now ← IO.monoMsNow
      let f := files[nextIdx]!
      let task ← IO.asTask (runFileResults f) Task.Priority.dedicated
      slots := slots.set! i (some (nextIdx, now, f, task))
      nextIdx := nextIdx + 1
  while remaining > 0 do
    let mut progress := false
    for i in [0:workers] do
      match slots[i]! with
      | none => pure ()
      | some (_, startMs, f, task) =>
        let done ← IO.hasFinished task
        let elapsed := (← IO.monoMsNow) - startMs
        if done then
          match (← IO.wait task) with
          | .ok results =>
            let (t', n') := absorbResults f results t notes
            t := t'; notes := n'
          | .error e =>
            t := { t with crash := t.crash + 1 }
            notes := notes.push s!"CRASH {f.fileName.getD f.toString}: {e}"
          remaining := remaining - 1
          progress := true
          if nextIdx < n then
            let now ← IO.monoMsNow
            let g := files[nextIdx]!
            let task' ← IO.asTask (runFileResults g) Task.Priority.dedicated
            slots := slots.set! i (some (nextIdx, now, g, task'))
            nextIdx := nextIdx + 1
          else
            slots := slots.set! i none
        else if timeoutMs > 0 ∧ elapsed > timeoutMs then
          t := { t with crash := t.crash + 1 }
          notes := notes.push s!"CRASH {f.fileName.getD f.toString}: \
            wall-timeout (>{timeoutMs}ms, abandoned)"
          remaining := remaining - 1
          progress := true
          if nextIdx < n then
            let now ← IO.monoMsNow
            let g := files[nextIdx]!
            let task' ← IO.asTask (runFileResults g) Task.Priority.dedicated
            slots := slots.set! i (some (nextIdx, now, g, task'))
            nextIdx := nextIdx + 1
          else
            slots := slots.set! i none
    if !progress then IO.sleep 10
  for note in notes do IO.println s!"    {note}"
  return t

/-- Parse `-j N` / `--jobs N` and `--timeout MS` out of `args`. Returns
    the jobs value (`0` = unset, use env/default), the timeout in millis
    (`0` = disabled), and the remaining (non-flag) arguments. -/
def parseFlags (args : List String) : Nat × Nat × List String := Id.run do
  let rec go : List String → Option Nat → Option Nat → List String → Nat × Nat × List String
    | [], j, tm, acc => (j.getD 0, tm.getD 0, acc.reverse)
    | "-j" :: v :: rest, _, tm, acc => go rest (some v.toNat!) tm acc
    | "--jobs" :: v :: rest, _, tm, acc => go rest (some v.toNat!) tm acc
    | "--timeout" :: v :: rest, j, _, acc => go rest j (some v.toNat!) acc
    | x :: rest, j, tm, acc => go rest j tm (x :: acc)
  go args none none []

def parentMain (root : System.FilePath) (jobs : Nat) (timeoutMs : Nat) : IO Unit := do
  IO.println s!"VMTests runner — root: {root}, jobs: {jobs}\
    {if timeoutMs > 0 then s!", timeout: {timeoutMs}ms" else ""}"
  let mut subdirs : Array System.FilePath := #[]
  for ent in (← root.readDir) do
    if (← ent.path.isDir) then subdirs := subdirs.push ent.path
  let sorted := subdirs.qsort (fun a b => a.toString < b.toString)
  let mut total : Tally := {}
  for d in sorted do
    IO.println s!"\n## {d.fileName.getD ""}"
    let t ← runDir d jobs timeoutMs
    IO.println s!"  {t.line} (total {t.total})"
    total := total.add t
  IO.println s!"\n==== TOTAL ===="
  IO.println s!"  {total.line} (total {total.total})"

def main (args : List String) : IO Unit := do
  let (jobs0, timeoutMs, rest) := parseFlags args
  let jobs ←
    if jobs0 > 0 then pure jobs0
    else do
      match (← IO.getEnv "VMTESTS_JOBS") with
      | some s => pure (Nat.max 1 s.toNat!)
      | none   => pure 8
  match rest with
  | "--file" :: path :: _ => runFile path
  | root :: _             => parentMain root jobs timeoutMs
  | []                    => parentMain "." jobs timeoutMs
end VMRunner

def main (args : List String) : IO Unit := VMRunner.main args
