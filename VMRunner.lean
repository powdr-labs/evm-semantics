module

public import EvmSemantics
public import EvmSemantics.Data.Hex
public import Lean.Data.Json

/-!
`VMRunner` — Phase-1 harness that runs the legacy ethereum/tests **VMTests**
against the executable evaluator (`stepF` / `run`).

Design (see the agreed plan):
* Target the legacy VMTests suite (pure single-frame EVM; no calls / no tx).
* **Ignore gas**: inject a huge `gasAvailable` so `OutOfGas` never fires, and
  never compare the `gas` field. Tests whose code uses the `GAS` opcode are
  skipped (its pushed value would be poisoned by the injected gas).
* **Skip unsupported opcodes**: a pre-scan of `exec.code` skips any test
  whose code contains CREATE/CREATE2/SELFDESTRUCT (the still-unimplemented
  system ops).
* Compare storage / return-data / balance / nonce; logs are not compared
  (require RLP + real keccak — phase 2).

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

def hugeGas : Nat := 2 ^ 63

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
      fork                := .Constantinople }
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

/-- Default `buildState`: inject `hugeGas` so `OutOfGas` never fires. Used
    for tests that aren't gas-comparable (any opcode with dynamic cost). -/
def buildState (testObj : Json) : State := buildStateWith testObj hugeGas

----------------------------------------------------------------------------
-- Driver
----------------------------------------------------------------------------

/-- Fueled `stepF` loop (mirrors `Main.run`, kept `partial`).
    End-of-code implicit STOP is handled by `Decode.decodeAt` (and thus the
    evaluator itself), so no harness compensation is needed here. -/
partial def run (s : State) (fuel : Nat) : Except ExecutionException State :=
  if fuel = 0 then .error .OutOfFuel else
    -- A nested CALL leaves the active frame halted while `callStack` is
    -- non-empty; `stepF` then resumes the caller. So we loop until the whole
    -- execution is *done* (halted with an empty call stack), not merely until
    -- the active frame halts.
    if s.isDone then .ok s else
      match stepF s with
      | .ok s'   => run s' (fuel - 1)
      | .error e => .error e

----------------------------------------------------------------------------
-- Opcode pre-scan
----------------------------------------------------------------------------

/-- Reason (if any) the opcode forces the test to be skipped *outright*
    (regardless of gas mode). `GAS` is intentionally not listed here — it's
    fine under gas-compared mode (the pushed value is then correct); under
    hugeGas mode the parent decides via `usesGas` below. -/
def skipReasonOf (_op : Operation) : Option String := none

/-- True when this opcode's `Gas.baseCost s.fork` value matches the real EVM's fee
    schedule exactly (no cold/warm split, no per-word/byte/topic dynamic
    component). A test whose bytecode contains only such opcodes is
    eligible for gas comparison against the corpus's expected `gas` value. -/
def gasComparableOpcode (op : Operation) : Bool :=
  match op with
  -- KECCAK256: base 30 + per-word 6·⌈size/32⌉.
  | .Keccak _ => true
  -- EIP-2929 cold/warm-split account / slot access — not yet modelled.
  | .BALANCE | .EXTCODESIZE | .EXTCODEHASH | .EXTCODECOPY => false
  -- SLOAD: Constantinople flat 50 (Frontier value used by corpus).
  -- SSTORE: pre-EIP-1283 schedule via `Gas.sstoreCost`.
  | .SLOAD | .SSTORE => true
  -- Dynamic copy/log/exp costs charged in stepF (and proved in Step).
  | .CALLDATACOPY | .CODECOPY | .RETURNDATACOPY | .MCOPY => true
  | .EXP | .Log _ => true
  -- CALL family: dynamic value/new-account surcharge + 63/64
  -- forwarding interact with caller gas in ways the comparator hasn't
  -- been audited for, so kept non-comparable.
  | .CALL | .CALLCODE | .DELEGATECALL | .STATICCALL => false
  -- SELFDESTRUCT, CREATE, CREATE2: gas-comparable now.
  -- - SELFDESTRUCT: on `Constantinople` the legacy corpus uses Frontier
  --   rules (cost 0, no `G_newaccount` surcharge), so `baseCost` +
  --   `selfDestructSurcharge` collapse to 0 here and the corpus's
  --   per-frame `gas` value matches exactly. The 24000 refund stays in
  --   `Substate.refundBalance` but is NOT applied at frame end (the
  --   legacy VMTests corpus reports pre-refund gas).
  -- - CREATE / CREATE2: the VMTests corpus has no test that actually
  --   reaches these as instruction-boundary opcodes (any `0xf0`/`0xf5`
  --   byte sits inside a PUSH immediate). Flipping the flag here lets
  --   those tests get gas-checked too without changing any behaviour.
  | .SELFDESTRUCT | .CREATE | .CREATE2 => true
  | _ => true

/-- Outcome of a full bytecode scan. `skipReason` overrides everything
    else; otherwise `gasComparable` says whether the test can use its real
    `exec.gas` and have its remaining-`gas` field compared. -/
structure ScanResult where
  skipReason    : Option String
  gasComparable : Bool
  usesGas       : Bool       -- bytecode contains the `GAS` opcode
  deriving Inhabited

/-- Scan `code` for opcodes that force a skip and track whether the test is
    gas-comparable. On an undefined byte, advance by 1 and keep scanning;
    on a known op advance past its immediate (`1 + argBytes`). -/
partial def scanCode (code : ByteArray) (pc : Nat)
    (gasOk : Bool := true) (sawGas : Bool := false) : ScanResult :=
  if pc ≥ code.size then
    { skipReason    := none
      gasComparable := gasOk
      usesGas       := sawGas }
  else
    match Decode.opcodeOf (code.get! pc) with
    | some op =>
      match skipReasonOf op with
      | some r => { skipReason := some r, gasComparable := false, usesGas := sawGas }
      | none   =>
        let sawGas' := sawGas || (op == .GAS)
        scanCode code (pc + 1 + op.argBytes) (gasOk && gasComparableOpcode op) sawGas'
    | none => scanCode code (pc + 1) gasOk sawGas

----------------------------------------------------------------------------
-- Outcome + comparison
----------------------------------------------------------------------------

inductive Outcome where
  | pass (gasChecked : Bool := false)
  | fail (msg : String)
  | skip (reason : String)   -- "unsupported" | "keccak" | "gas"
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

/-- Run one test object and classify the outcome. -/
def runTest (testObj : Json) : Outcome :=
  let exec := subObj testObj "exec"
  let code := hexToBytes (strField exec "code")
  let scan := scanCode code 0
  match scan.skipReason with
  | some r => .skip r
  | none =>
    -- Gas-comparable iff every opcode has the EVM's fee-schedule-exact
    -- fixed cost. Tests with the `GAS` opcode are only OK under
    -- gas-comparable mode (under hugeGas, the pushed value would be
    -- meaningless).
    let gasCompare := scan.gasComparable
    if scan.usesGas && !gasCompare then
      .skip "gas"
    else
      let inputGas := hexToNat (strField exec "gas")
      let s0 := buildStateWith testObj (if gasCompare then inputGas else hugeGas)
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
            else if gasCompare then
              let expGas := hexToNat (strField testObj "gas")
              if sf.gasAvailable != expGas then
                .fail s!"gas mismatch: got {sf.gasAvailable} exp {expGas}"
              else .pass (gasChecked := true)
            else .pass

----------------------------------------------------------------------------
-- Tally + file walking
----------------------------------------------------------------------------

structure Tally where
  pass : Nat := 0
  passGasChecked : Nat := 0    -- of `pass`, how many also matched the `gas` field
  fail : Nat := 0
  skipUns : Nat := 0
  skipKec : Nat := 0
  skipGas : Nat := 0
  incon : Nat := 0
  crash : Nat := 0       -- evaluator panic / timeout (child exited non-zero)
  deriving Inhabited

def Tally.add (t u : Tally) : Tally :=
  { pass := t.pass + u.pass, passGasChecked := t.passGasChecked + u.passGasChecked
    fail := t.fail + u.fail
    skipUns := t.skipUns + u.skipUns, skipKec := t.skipKec + u.skipKec
    skipGas := t.skipGas + u.skipGas, incon := t.incon + u.incon
    crash := t.crash + u.crash }

def Tally.total (t : Tally) : Nat :=
  t.pass + t.fail + t.skipUns + t.skipKec + t.skipGas + t.incon + t.crash

def Tally.line (t : Tally) : String :=
  s!"pass={t.pass} (gas-checked={t.passGasChecked}) fail={t.fail} " ++
  s!"skip(unsup={t.skipUns} keccak={t.skipKec} gas={t.skipGas}) " ++
  s!"incon={t.incon} crash={t.crash}"

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

/-- The tag for an `Outcome`, with optional message. The `pass` variant
    uses `msg = "gas"` to mark a gas-checked pass, `""` otherwise. -/
def outcomeTag : Outcome → String × String
  | .pass gc => ("PASS", if gc then "gas" else "")
  | .fail m  => ("FAIL", m)
  | .incon m => ("INCON", m)
  | .skip r  => ("SKIP", r)

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
    | "PASS"     =>
      t := { t with pass := t.pass + 1 }
      if msg == "gas" then
        t := { t with passGasChecked := t.passGasChecked + 1 }
    | "FAIL"     => t := { t with fail := t.fail + 1 }
                    notes := notes.push s!"FAIL {name}: {msg}"
    | "INCON"    => t := { t with incon := t.incon + 1 }
    | "SKIP"     => match msg with
        | "unsupported" => t := { t with skipUns := t.skipUns + 1 }
        | "keccak"      => t := { t with skipKec := t.skipKec + 1 }
        | _             => t := { t with skipGas := t.skipGas + 1 }
    | "PARSEERR" => t := { t with crash := t.crash + 1 }
                    notes := notes.push s!"PARSEERR {f.fileName.getD f.toString}: {msg}"
    | _          => pure ()
  return (t, notes)

/-- Run one subdir: spawn a Lean `Task` per file, up to `jobs` in flight
    concurrently. Results are folded in spawn order so notes are stable. -/
def runDir (dir : System.FilePath) (jobs : Nat) : IO Tally := do
  let files ← collectJson dir
  let mut t : Tally := {}
  let mut notes : Array String := #[]
  let mut i := 0
  let n := files.size
  let batch := Nat.max 1 jobs
  while i < n do
    let stop := Nat.min (i + batch) n
    -- Spawn `stop - i` tasks; each runs on the default thread pool.
    let mut tasks : Array (System.FilePath ×
                            Task (Except IO.Error (Array (String × String × String)))) := #[]
    for k in [i:stop] do
      let f := files[k]!
      let task ← IO.asTask (runFileResults f)
      tasks := tasks.push (f, task)
    -- Wait for each in spawn order so the notes array stays stable.
    for (f, task) in tasks do
      match (← IO.wait task) with
      | .ok results =>
        let (t', n') := absorbResults f results t notes
        t := t'; notes := n'
      | .error e =>
        t := { t with crash := t.crash + 1 }
        notes := notes.push s!"CRASH {f.fileName.getD f.toString}: {e}"
    i := stop
  for note in notes do IO.println s!"    {note}"
  return t

/-- Resolve the worker count: explicit `--jobs N` / `-j N`, else env
    `VMTESTS_JOBS`, else default `4`. Returns the resolved count and the
    remaining (non-`-j`) arguments. -/
def parseJobs (args : List String) : Nat × List String := Id.run do
  let rec go : List String → Option Nat → List String → Nat × List String
    | [], n, acc => (n.getD 0, acc.reverse)
    | "-j" :: v :: rest, _, acc => go rest (some v.toNat!) acc
    | "--jobs" :: v :: rest, _, acc => go rest (some v.toNat!) acc
    | x :: rest, n, acc => go rest n (x :: acc)
  go args none []

def parentMain (root : System.FilePath) (jobs : Nat) : IO Unit := do
  IO.println s!"VMTests runner — root: {root}, jobs: {jobs}"
  let mut subdirs : Array System.FilePath := #[]
  for ent in (← root.readDir) do
    if (← ent.path.isDir) then subdirs := subdirs.push ent.path
  let sorted := subdirs.qsort (fun a b => a.toString < b.toString)
  let mut total : Tally := {}
  for d in sorted do
    IO.println s!"\n## {d.fileName.getD ""}"
    let t ← runDir d jobs
    IO.println s!"  {t.line} (total {t.total})"
    total := total.add t
  IO.println s!"\n==== TOTAL ===="
  IO.println s!"  {total.line} (total {total.total})"

def main (args : List String) : IO Unit := do
  let (jobs0, rest) := parseJobs args
  let jobs ←
    if jobs0 > 0 then pure jobs0
    else do
      match (← IO.getEnv "VMTESTS_JOBS") with
      | some s => pure (Nat.max 1 s.toNat!)
      | none   => pure 8
  match rest with
  | "--file" :: path :: _ => runFile path
  | root :: _             => parentMain root jobs
  | []                    => parentMain "." jobs
end VMRunner

def main (args : List String) : IO Unit := VMRunner.main args
