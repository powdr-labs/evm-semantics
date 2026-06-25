module

public import EvmSemantics
public import Lean.Data.Json

/-!
`VMRunner` — Phase-1 harness that runs the legacy ethereum/tests **VMTests**
against the executable evaluator (`stepF` / `run`).

Design (see the agreed plan):
* Target the legacy VMTests suite (pure single-frame EVM; no calls / no tx).
* **Ignore gas**: inject a huge `gasAvailable` so `OutOfGas` never fires, and
  never compare the `gas` field. Tests whose code uses the `GAS` opcode are
  skipped (its pushed value would be poisoned by the injected gas).
* **Skip unsupported opcodes**: a pre-scan of `exec.code` skips any test whose
  code contains CALL/CREATE-family or SELFDESTRUCT (unimplemented), or
  KECCAK256 / EXTCODEHASH (keccak is `opaque`, returns 0 at runtime).
* Compare storage / return-data / balance / nonce; logs are not compared
  (require RLP + real keccak — phase 2).

Usage: `vmtests <path-to-Constantinople/VMTests>`
-/

open Lean
open EvmSemantics
open EvmSemantics.EVM

@[expose] public section

namespace VMRunner

----------------------------------------------------------------------------
-- Hex helpers
----------------------------------------------------------------------------

def hexVal (c : Char) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else if 'A' ≤ c ∧ c ≤ 'F' then c.toNat - 'A'.toNat + 10
  else 0

def strip0x (s : String) : String :=
  if s.startsWith "0x" ∨ s.startsWith "0X" then String.ofList (s.toList.drop 2) else s

def hexToNat (s : String) : Nat :=
  (strip0x s).foldl (fun acc c => acc * 16 + hexVal c) 0

def hexToUInt256 (s : String) : UInt256 := UInt256.ofNat (hexToNat s)

def hexToAddress (s : String) : AccountAddress := AccountAddress.ofNat (hexToNat s)

/-- Parse a `0x`-hex bytestring into a `ByteArray` (pairs of nibbles). -/
def hexToBytes (s : String) : ByteArray := Id.run do
  let cs0 := (strip0x s).toList
  let cs := if cs0.length % 2 == 1 then '0' :: cs0 else cs0
  let mut out : ByteArray := .empty
  let mut rest := cs
  while rest.length ≥ 2 do
    match rest with
    | hi :: lo :: tl =>
      out := out.push (UInt8.ofNat (hexVal hi * 16 + hexVal lo))
      rest := tl
    | _ => rest := []
  return out

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

/-- Assemble the initial `State` from a VMTest `exec`/`env`/`pre`. -/
def buildState (testObj : Json) : State :=
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
    { codeOwner := hexToAddress (strField exec "address")
      sender    := hexToAddress (strField exec "origin")   -- ORIGIN
      source    := hexToAddress (strField exec "caller")   -- CALLER
      weiValue  := hexToUInt256 (strField exec "value")
      calldata  := hexToBytes   (strField exec "data")
      code      := hexToBytes   (strField exec "code")
      gasPrice  := hexToUInt256 (strField exec "gasPrice")
      header    := header
      depth     := 0
      permitStateMutation := true
      blobVersionedHashes := #[] }
  { toMachineState :=
      { gasAvailable := hugeGas, activeWords := ⟨0⟩
        memory := .empty, returnData := .empty, H_return := .empty }
    accountMap   := accountMap
    substate     := Substate.empty
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
  if fuel = 0 then .error .OutOfFuel else
    match s.halt with
    | .Running =>
      match stepF s with
      | .ok s'   => run s' (fuel - 1)
      | .error e => .error e
    | _ => .ok s

----------------------------------------------------------------------------
-- Opcode pre-scan
----------------------------------------------------------------------------

/-- Reason (if any) the opcode forces the test to be skipped. -/
def skipReasonOf (op : Operation) : Option String :=
  match op with
  | .System .CALL | .System .CALLCODE | .System .DELEGATECALL | .System .STATICCALL
  | .System .CREATE | .System .CREATE2 | .System .SELFDESTRUCT => some "unsupported"
  | .Keccak _        => some "keccak"
  | .Env .EXTCODEHASH => some "keccak"
  | .StackMemFlow .GAS => some "gas"
  | _ => none

/-- Scan `code` for an opcode that forces a skip. On an undefined byte,
    advance by 1 and keep scanning (so an unsupported op after a data byte is
    not missed); on a known op advance past its immediate (`1 + argBytes`). -/
partial def scanCode (code : ByteArray) (pc : Nat) : Option String :=
  if pc ≥ code.size then none
  else
    match Decode.opcodeOf (code.get! pc) with
    | some op =>
      match skipReasonOf op with
      | some r => some r
      | none   => scanCode code (pc + 1 + op.argBytes)
    | none => scanCode code (pc + 1)

----------------------------------------------------------------------------
-- Outcome + comparison
----------------------------------------------------------------------------

inductive Outcome where
  | pass
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
  let code := hexToBytes (strField (subObj testObj "exec") "code")
  match scanCode code 0 with
  | some r => .skip r
  | none =>
    let s0 := buildState testObj
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
          if sf.H_return.toList == outExp.toList then .pass
          else .fail s!"out mismatch ({sf.H_return.size}B vs {outExp.size}B)"

----------------------------------------------------------------------------
-- Tally + file walking
----------------------------------------------------------------------------

structure Tally where
  pass : Nat := 0
  fail : Nat := 0
  skipUns : Nat := 0
  skipKec : Nat := 0
  skipGas : Nat := 0
  incon : Nat := 0
  crash : Nat := 0       -- evaluator panic / timeout (child exited non-zero)
  deriving Inhabited

def Tally.add (t u : Tally) : Tally :=
  { pass := t.pass + u.pass, fail := t.fail + u.fail
    skipUns := t.skipUns + u.skipUns, skipKec := t.skipKec + u.skipKec
    skipGas := t.skipGas + u.skipGas, incon := t.incon + u.incon
    crash := t.crash + u.crash }

def Tally.total (t : Tally) : Nat :=
  t.pass + t.fail + t.skipUns + t.skipKec + t.skipGas + t.incon + t.crash

def Tally.line (t : Tally) : String :=
  s!"pass={t.pass} fail={t.fail} skip(unsup={t.skipUns} keccak={t.skipKec} gas={t.skipGas}) " ++
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

def outcomeTag : Outcome → String × String
  | .pass    => ("PASS", "")
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
-- Parent mode: spawn one isolated child per file, tally results.
----------------------------------------------------------------------------

/-- Run one subdir: spawn `timeout <secs> <self> --file <f>` per file. -/
def runDir (self : String) (dir : System.FilePath) (timeoutSecs : Nat) : IO Tally := do
  let files ← collectJson dir
  let mut t : Tally := {}
  let mut notes : Array String := #[]
  for f in files do
    let out ← IO.Process.output
      { cmd := "timeout", args := #[toString timeoutSecs, self, "--file", f.toString] }
    if out.exitCode != 0 then
      t := { t with crash := t.crash + 1 }
      let why := if out.exitCode == 124 then "timeout" else s!"exit {out.exitCode}"
      notes := notes.push s!"CRASH {f.fileName.getD f.toString}: {why}"
    else
      for line in out.stdout.splitOn "\n" do
        let parts := line.splitOn "\t"
        match parts with
        | tag :: name :: rest =>
          let msg := String.intercalate "\t" rest
          match tag with
          | "PASS"  => t := { t with pass := t.pass + 1 }
          | "FAIL"  => t := { t with fail := t.fail + 1 }; notes := notes.push s!"FAIL {name}: {msg}"
          | "INCON" => t := { t with incon := t.incon + 1 }
          | "SKIP"  => match msg with
              | "unsupported" => t := { t with skipUns := t.skipUns + 1 }
              | "keccak"      => t := { t with skipKec := t.skipKec + 1 }
              | _             => t := { t with skipGas := t.skipGas + 1 }
          | _ => pure ()
        | _ => pure ()
  for n in notes do IO.println s!"    {n}"
  return t

def parentMain (root : System.FilePath) : IO Unit := do
  let self := (← IO.appPath).toString
  IO.println s!"VMTests runner — root: {root}"
  let mut subdirs : Array System.FilePath := #[]
  for ent in (← root.readDir) do
    if (← ent.path.isDir) then subdirs := subdirs.push ent.path
  let sorted := subdirs.qsort (fun a b => a.toString < b.toString)
  let mut total : Tally := {}
  for d in sorted do
    -- vmPerformance has legitimately long programs; give it more time.
    let secs := if (d.fileName.getD "") == "vmPerformance" then 120 else 30
    IO.println s!"\n## {d.fileName.getD ""}"
    let t ← runDir self d secs
    IO.println s!"  {t.line} (total {t.total})"
    total := total.add t
  IO.println s!"\n==== TOTAL ===="
  IO.println s!"  {total.line} (total {total.total})"

def main (args : List String) : IO Unit :=
  match args with
  | "--file" :: path :: _ => runFile path
  | root :: _             => parentMain root
  | []                    => parentMain "."
end VMRunner

def main (args : List String) : IO Unit := VMRunner.main args
