import EvmSemantics
import Std.Internal.Parsec
import Lean.Data.Json

/-!
`statetests` — a conformance runner for the **BlockchainTests** form of the
ethereum/legacytests GeneralStateTests (`Constantinople/BlockchainTests/
GeneralStateTests/stCall*`). Unlike the plain GeneralStateTests (which give only
a post-state-root `hash`, needing keccak + RLP + a Merkle-Patricia trie), the
BlockchainTests carry an **expanded `postState`** (balance/code/nonce/storage
per account), so we can verify the recursive CALL semantics directly.

Scope (v1): we run only the `Constantinople` fork variant of each test (the only
fork whose schedule `EvmSemantics` models for the CALL family — EIP-150 gas).
The top-level transaction is executed as the `to` account's code; CALL opcodes
inside it recurse through the new frame-stack machinery. We compare the
resulting accounts against `postState`:

* **core** match = storage + nonce + code (the CALL-semantics signal);
* **full** match also requires the gas-dependent **balances** to agree.

`core` is the headline pass metric; `full` is reported separately because exact
balances require exact gas accounting (the hardest part to get right).
-/

open EvmSemantics EvmSemantics.EVM Lean

namespace StateTests

----------------------------------------------------------------------------
-- Hex / JSON helpers (kept self-contained).
----------------------------------------------------------------------------

def hexVal (c : Char) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else if 'A' ≤ c ∧ c ≤ 'F' then c.toNat - 'A'.toNat + 10
  else 0

def strip0x (s : String) : String :=
  if s.startsWith "0x" then String.ofList (s.toList.drop 2) else s

def hexToNat (s : String) : Nat :=
  (strip0x s).foldl (fun acc c => acc * 16 + hexVal c) 0

def hexToUInt256 (s : String) : UInt256 := UInt256.ofNat (hexToNat s)
def hexToAddress (s : String) : AccountAddress := AccountAddress.ofNat (hexToNat s)

def hexToBytes (s : String) : ByteArray := Id.run do
  let cs := (strip0x s).toList
  let mut out := ByteArray.empty
  let mut i := 0
  let arr := cs.toArray
  while i + 1 < arr.size + 1 ∧ i + 1 ≤ arr.size do
    if i + 1 < arr.size then
      out := out.push (UInt8.ofNat (hexVal arr[i]! * 16 + hexVal arr[i+1]!))
      i := i + 2
    else
      out := out.push (UInt8.ofNat (hexVal arr[i]! * 16))
      i := i + 2
  return out

def strField (j : Json) (k : String) : String :=
  match j.getObjVal? k with
  | .ok v => (v.getStr?.toOption.getD (toString v))
  | .error _ => ""

def subObj (j : Json) (k : String) : Json := (j.getObjVal? k).toOption.getD Json.null

def objEntries (j : Json) (k : String) : List (String × Json) :=
  match (subObj j k) with
  | .obj m => m.toArray.toList.map (fun (kv) => (kv.1, kv.2))
  | _ => []

/-- Storage slot→value entries of an account JSON object. -/
def storageEntries (accJson : Json) : List (String × String) :=
  match subObj accJson "storage" with
  | .obj m => m.toArray.toList.filterMap (fun kv =>
      (kv.2.getStr?.toOption).map (fun v => (kv.1, v)))
  | _ => []

----------------------------------------------------------------------------
-- State construction.
----------------------------------------------------------------------------

/-- The fixed ethereum/tests transaction sender (we have no ECDSA recovery; the
    transactions carry only `v/r/s`). All stCall* `pre` states fund this EOA. -/
def txSender : AccountAddress := hexToAddress "0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b"

def mkAccount (accJson : Json) : Account :=
  let storage := (storageEntries accJson).foldl
    (fun st (slot, val) => st.set (hexToUInt256 slot) (hexToUInt256 val)) Storage.empty
  { nonce    := hexToUInt256 (strField accJson "nonce")
    balance  := hexToUInt256 (strField accJson "balance")
    code     := hexToBytes   (strField accJson "code")
    storage  := storage
    tstorage := Storage.empty }

/-- Intrinsic transaction gas: 21000 + 16 per non-zero calldata byte + 4 per
    zero byte (pre-EIP-2028 the non-zero rate was 68; Constantinople uses 68).
    The legacy corpus predates EIP-2028, so we use 68/4. -/
def intrinsicGas (data : ByteArray) : Nat := Id.run do
  let mut g := 21000
  for b in data do
    g := g + (if b == 0 then 4 else 68)
  return g

/-- Build the top-level execution `State` for a BlockchainTest test object,
    given its `pre` accounts and the block's transaction JSON. -/
def buildState (preMap : AccountMap) (env tx : Json) : State :=
  let toAddr   := hexToAddress (strField tx "to")
  let value    := hexToUInt256 (strField tx "value")
  let data     := hexToBytes   (strField tx "data")
  let gasLimit := hexToNat     (strField tx "gasLimit")
  let gasPrice := hexToUInt256 (strField tx "gasPrice")
  -- Apply the transaction-level effects up front: bump the sender nonce, debit
  -- the up-front gas charge, and transfer `value` to the callee.
  let sender := preMap txSender
  let upfront := gasLimit * gasPrice.toNat
  let preMap := preMap.set txSender
    { sender with nonce := sender.nonce + UInt256.ofNat 1
                  balance := sender.balance - UInt256.ofNat upfront }
  let accountMap := preMap.transfer txSender toAddr value
  let header : BlockHeader :=
    { coinbase      := hexToAddress (strField env "currentCoinbase")
      timestamp     := hexToUInt256 (strField env "currentTimestamp")
      number        := hexToUInt256 (strField env "currentNumber")
      prevRandao    := hexToUInt256 (strField env "currentDifficulty")
      gasLimit      := hexToUInt256 (strField env "currentGasLimit")
      baseFeePerGas := ⟨0⟩, chainId := ⟨0⟩, blobBaseFee := ⟨0⟩
      blockHash     := fun _ => ⟨0⟩ }
  let execEnv : ExecutionEnv :=
    { codeOwner := toAddr
      sender    := txSender
      source    := txSender
      weiValue  := value
      calldata  := data
      code      := (accountMap toAddr).code
      gasPrice  := gasPrice
      header    := header
      depth     := 0
      permitStateMutation := true
      blobVersionedHashes := #[]
      fork                := .Constantinople }
  { toMachineState :=
      { gasAvailable := gasLimit - intrinsicGas data, activeWords := ⟨0⟩
        memory := .empty, returnData := .empty, hReturn := .empty }
    accountMap   := accountMap
    substate     := { Substate.empty with originalAccountMap := accountMap }
    executionEnv := execEnv
    pc           := ⟨0⟩
    stack        := []
    execLength   := 0
    halt         := .Running }

----------------------------------------------------------------------------
-- Runner.
----------------------------------------------------------------------------

/-- Fueled `stepF` loop until the whole execution is done.

    `stepF` reports an in-frame exception as `Except.error` rather than as a
    `halt := .Exception` state. When that happens *inside a sub-call* (the call
    stack is non-empty) it is **not** a transaction abort — the callee faulted,
    so we resume the caller with a `0` (and roll its world back to the snapshot).
    This is the executable bridge to the relational `callReturnException` rule.
    Only a fault at the top frame (empty call stack) aborts the whole run. -/
partial def run (s : State) (fuel : Nat) : Except ExecutionException State :=
  if fuel = 0 then .error .OutOfFuel else
    if s.isDone then .ok s else
      match stepF s with
      | .ok s'   => run s' (fuel - 1)
      | .error e =>
        match s.callStack with
        | []        => .error e
        | f :: rest => run (({ s with halt := .Exception e }).resumeException f rest) (fuel - 1)

inductive Outcome where
  | passCore       -- storage + nonce + code match (balances not checked)
  | passFull       -- core + balances also match
  | fail (msg : String)
  | incon (msg : String)
  deriving Repr

/-- Compare the run's final accounts to `postState`. Returns a list of
    mismatch descriptions; checks storage/nonce/code always, balance only when
    `checkBal` is set. -/
def cmpPost (sf : State) (postEntries : List (String × Json)) (checkBal : Bool) :
    List String := Id.run do
  let mut msgs := []
  for (addrStr, accJson) in postEntries do
    let a := hexToAddress addrStr
    let got := sf.accountMap a
    let expNonce := hexToUInt256 (strField accJson "nonce")
    let expCode := hexToBytes (strField accJson "code")
    if got.nonce.toNat != expNonce.toNat then
      msgs := s!"{addrStr} nonce {got.nonce.toNat}≠{expNonce.toNat}" :: msgs
    if got.code.toList != expCode.toList then
      msgs := s!"{addrStr} code size {got.code.size}≠{expCode.size}" :: msgs
    for (slot, val) in storageEntries accJson do
      let k := hexToUInt256 slot
      let want := hexToUInt256 val
      if (got.storage k).toNat != want.toNat then
        msgs := s!"{addrStr}[{slot}] {(got.storage k).toNat}≠{want.toNat}" :: msgs
    if checkBal then
      let expBal := hexToUInt256 (strField accJson "balance")
      if got.balance.toNat != expBal.toNat then
        msgs := s!"{addrStr} bal {got.balance.toNat}≠{expBal.toNat}" :: msgs
  return msgs

def runOne (testObj : Json) : Outcome :=
  let preMap : AccountMap :=
    (objEntries testObj "pre").foldl
      (fun σ (addrStr, accJson) => σ.set (hexToAddress addrStr) (mkAccount accJson))
      AccountMap.empty
  let blocks := match subObj testObj "blocks" with | .arr a => a.toList | _ => []
  match blocks with
  | block :: _ =>
    let txs := match subObj block "transactions" with | .arr a => a.toList | _ => []
    match txs with
    | tx :: _ =>
      let s0 := buildState preMap (subObj testObj "env") tx
      -- Steps are bounded by gas: every non-halting opcode costs ≥1 gas, and
      -- resume steps are bounded by the number of CALLs (≥700 gas each). So
      -- `2·gasAvailable` (plus slack) can never pre-empt a genuine OutOfGas; it
      -- is purely a backstop against an evaluator bug producing a 0-gas
      -- non-halting step.
      match run s0 (2 * s0.gasAvailable + 100000) with
      | .error .OutOfFuel => .incon "fuel exhausted"
      | .error e => .incon s!"top-level halt {repr e}"
      | .ok sf =>
        let post := objEntries testObj "postState"
        match cmpPost sf post false with
        | [] => match cmpPost sf post true with
                | [] => .passFull
                | _  => .passCore
        | msgs => .fail (String.intercalate "; " (msgs.take 3))
    | [] => .incon "no transactions"
  | [] => .incon "no blocks"

structure Tally where
  passFull : Nat := 0
  passCore : Nat := 0
  fail : Nat := 0
  incon : Nat := 0
  crash : Nat := 0
  deriving Inhabited

partial def collectJson (p : System.FilePath) : IO (Array System.FilePath) := do
  let mut out := #[]
  for ent in (← p.readDir) do
    let path := ent.path
    if (← path.isDir) then out := out ++ (← collectJson path)
    else if path.toString.endsWith ".json" then out := out.push path
  return out.qsort (fun a b => a.toString < b.toString)

/-- Run every `*_Constantinople` test in a file. -/
def runFile (path : System.FilePath) (verbose : Bool) : IO Tally := do
  let txt ← IO.FS.readFile path
  match Json.parse txt with
  | .error _ => return { crash := 1 }
  | .ok j =>
    let entries := match j with | .obj m => m.toArray.toList | _ => []
    let mut t : Tally := {}
    for (name, testObj) in entries do
      if !name.endsWith "_Constantinople" then continue
      match runOne testObj with
      | .passFull => t := { t with passFull := t.passFull + 1 }
      | .passCore => t := { t with passCore := t.passCore + 1 }
      | .fail m   => t := { t with fail := t.fail + 1 }
                     if verbose then IO.println s!"FAIL {name}: {m}"
      | .incon m  => t := { t with incon := t.incon + 1 }
                     if verbose then IO.println s!"INCON {name}: {m}"
    return t

def main (args : List String) : IO Unit := do
  let verbose := args.contains "-v"
  let dirs := args.filter (fun a => a != "-v")
  let root : System.FilePath := dirs.headD "."
  let files ← if (← root.isDir) then collectJson root else pure #[root]
  let mut tot : Tally := {}
  for f in files do
    let t ← runFile f verbose
    tot := { passFull := tot.passFull + t.passFull, passCore := tot.passCore + t.passCore
             fail := tot.fail + t.fail, incon := tot.incon + t.incon
             crash := tot.crash + t.crash }
  IO.println s!"pass(full={tot.passFull} core+={tot.passCore}) fail={tot.fail} \
incon={tot.incon} crash={tot.crash} \
(total {tot.passFull + tot.passCore + tot.fail + tot.incon + tot.crash})"

end StateTests

def main (args : List String) : IO Unit := StateTests.main args
