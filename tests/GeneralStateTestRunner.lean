module

public import Lean.Data.Json
public import EvmSemantics
public import EvmSemantics.Data.Hex
public import tests.FakeExponential

/-!
`GeneralStateTestRunner` — JSON driver around `EvmSemantics.Tx.execute` for the
**modern `ethereum/tests` GeneralStateTests** (`state_test` fixture format), as
shipped in `fixtures_general_state_tests.tgz`.

This is the maintained counterpart to `tests/StateTestRunner.lean` (which runs
the frozen `ethereum/legacytests` BlockchainTests). The two formats differ
enough that a separate, self-contained runner is clearer than a shared module:

* block context lives in a flat `env` object (`currentCoinbase`,
  `currentBaseFee`, `currentRandom`, …) rather than `blocks[].blockHeader`;
* the transaction is a *template* — `data`/`gasLimit`/`value` are arrays, and
  each `post` entry selects one combination via `indexes.{data,gas,value}`;
* the sender is given **directly** (`transaction.sender`), so no ECDSA recovery
  is needed (contrast the legacy runner, which recovers from `v,r,s`);
* `post` is keyed by *bare* fork name (`"Cancun"`) → an array of entries, each
  carrying an expanded `state` (per-account post-state, compared directly) plus
  a state-root `hash` (compared via the world MPT root for the strongest tier).

**Scope (minimal framework).** Legacy (`gasPrice`), EIP-1559 (`maxFeePerGas`),
EIP-2930 (access-list), EIP-4844 (blob) and EIP-7702 (set-code) transactions
are all executed. Two corpora feed this runner: the frozen `ethereum/tests`
set (filled for Cancun/Prague) and the EEST/`execution-specs` Osaka
`state_tests` (EIP-7825/7823/7883/7939/7951).
`Tx.execute` applies the EIP-1559 fee split (London+ burns the base-fee slice,
crediting the coinbase only the priority tip), so post-London txs reach the
balance-exact tiers. See `VMTESTS.md`.
-/

@[expose] public section

namespace GeneralStateTests

open EvmSemantics EvmSemantics.EVM Lean

open EvmSemantics.Hex

----------------------------------------------------------------------------
-- JSON helpers (mirrors tests/StateTestRunner.lean; kept local so this
-- runner is self-contained and can't destabilise the legacy runner).
----------------------------------------------------------------------------

/-- The string value of object field `k`, or `""` when absent / non-string. -/
def strField (j : Json) (k : String) : String := (j.getObjValAs? String k).toOption.getD ""

/-- The sub-object at field `k`, or `Json.null` when absent. -/
def subObj (j : Json) (k : String) : Json := (j.getObjVal? k).toOption.getD Json.null

/-- The `(key, value)` entries of the object at field `k` (`[]` if not an object). -/
def objEntries (j : Json) (k : String) : List (String × Json) :=
  match subObj j k with
  | .obj m => m.toArray.toList
  | _      => []

/-- The elements of `j` when it is a JSON array, else `#[]`. -/
def jsonArr (j : Json) : Array Json :=
  match j with | .arr a => a | _ => #[]

/-- The string element at index `i` of the array field `k` (`""` if absent). -/
def arrStr (j : Json) (k : String) (i : Nat) : String :=
  match (jsonArr (subObj j k))[i]? with
  | some (.str s) => s
  | _             => ""

/-- The `Nat` value of object field `k`, or `0` when absent / not a number. -/
def natField (j : Json) (k : String) : Nat := (j.getObjValAs? Nat k).toOption.getD 0

/-- The `(slot, value)` storage entries of an account JSON object. -/
def storageEntries (j : Json) : List (String × String) :=
  match (j.getObjVal? "storage").toOption.getD Json.null with
  | .obj m => m.toArray.toList.filterMap (fun (k, v) =>
      match v with
      | .str s => some (k, s)
      | _      => none)
  | _      => []

/-- Build an `Account` from a `{balance, code, nonce, storage}` JSON object. -/
def mkAccount (j : Json) : Account :=
  let balance := hexToUInt256 (strField j "balance")
  let code    := hexToBytes   (strField j "code")
  let nonce   := hexToUInt256 (strField j "nonce")
  let storage : Storage :=
    (storageEntries j).foldl
      (fun σ (k, v) => σ.set (hexToUInt256 k) (hexToUInt256 v))
      Storage.empty
  { balance := balance, nonce := nonce, code := code, storage := storage,
    tstorage := Storage.empty }

----------------------------------------------------------------------------
-- Env / transaction / fork decode.
----------------------------------------------------------------------------

/-- EIP-4844/7691 blob base fee derived from `excessBlobGas`, with the
    fork's `BLOB_BASE_FEE_UPDATE_FRACTION` (`3338477` at Cancun, `5007716`
    from Prague). -/
def blobBaseFeeOf (excessBlobGas : Nat) (fork : Fork) : Nat :=
  TestSupport.fakeExponential 1 excessBlobGas (if fork ≥ .Prague then 5007716 else 3338477)

/-- Decode the modern `state_test` `env` object into a `BlockHeader`.

    Distinct from the legacy `StateTestRunner.decodeHeader`: the modern corpus
    is filled for post-Merge forks, so `prevRandao` reads `currentRandom`
    first, only falling back to the pre-Merge `currentDifficulty` when
    `currentRandom` is absent. `chainId` is fixed to mainnet `1`; `blobBaseFee`
    is derived from `currentExcessBlobGas` via EIP-4844 `fake_exp` with the
    `fork`'s update fraction. -/
def decodeEnv (env : Json) (fork : Fork) : BlockHeader :=
  let randomStr := strField env "currentRandom"
  let prevRandao : UInt256 :=
    if randomStr ≠ "" then hexToUInt256 randomStr
    else hexToUInt256 (strField env "currentDifficulty")
  let excessStr := strField env "currentExcessBlobGas"
  let blobBaseFee : UInt256 :=
    if excessStr ≠ "" then
      UInt256.ofNat (blobBaseFeeOf (hexToUInt256 excessStr).toNat fork)
    else ⟨0⟩
  { coinbase      := hexToAddress (strField env "currentCoinbase")
    timestamp     := hexToUInt256 (strField env "currentTimestamp")
    number        := hexToUInt256 (strField env "currentNumber")
    prevRandao    := prevRandao
    gasLimit      := hexToUInt256 (strField env "currentGasLimit")
    baseFeePerGas := hexToUInt256 (strField env "currentBaseFee")
    chainId       := ⟨1⟩
    blobBaseFee   := blobBaseFee
    blockHash     := fun _ => ⟨0⟩ }

/-- Map a *bare* modern fork name (the `post` object's keys, e.g. `"Cancun"`)
    to a `Fork`. Unlike `StateTestRunner.parseFork`, this is an exact match, not
    a `_suffix` test. Returns `none` for forks we don't model. -/
def parseForkExact (s : String) : Option Fork :=
  match s with
  | "Frontier"          => some .Frontier
  | "Homestead"         => some .Homestead
  | "EIP150"            => some .TangerineWhistle
  | "EIP158"            => some .SpuriousDragon
  | "Byzantium"         => some .Byzantium
  | "Constantinople"    => some .Constantinople
  | "ConstantinopleFix" => some .Petersburg
  | "Petersburg"        => some .Petersburg
  | "Istanbul"          => some .Istanbul
  | "MuirGlacier"       => some .MuirGlacier
  | "Berlin"            => some .Berlin
  | "London"            => some .London
  | "ArrowGlacier"      => some .ArrowGlacier
  | "GrayGlacier"       => some .GrayGlacier
  | "Merge" | "Paris"   => some .Paris
  | "Shanghai"          => some .Shanghai
  | "Cancun"            => some .Cancun
  | "Prague"            => some .Prague
  | "Osaka"             => some .Osaka
  | _                   => none

/-- Reason a transaction variant can't be executed by this runner, or `none`
    if it can. All modelled tx kinds now execute — legacy, EIP-1559,
    EIP-2930 (access-list), EIP-4844 (blob) and EIP-7702 (set-code) — so this
    is `none` for every transaction; kept as a hook for a future unmodelled
    envelope. -/
def txUnsupportedReason (_txJson : Json) : Option String := none

/-- Parse the EIP-2930 access list for the selected `data` index into
    `(address, storageKeys)` pairs. `accessLists` is an array parallel to
    `data`/`gasLimit`/`value`; each element is a list of
    `{address, storageKeys:[…]}`. Empty when absent. -/
def parseAccessList (txJson : Json) (dataIdx : Nat) :
    List (AccountAddress × List UInt256) :=
  match (jsonArr (subObj txJson "accessLists"))[dataIdx]? with
  | some (.arr entries) =>
    entries.toList.map (fun e =>
      let addr := hexToAddress (strField e "address")
      let keys := (jsonArr (subObj e "storageKeys")).toList.filterMap
        (fun k => match k with | .str s => some (hexToUInt256 s) | _ => none)
      (addr, keys))
  | _ => []

/-- Parse the EIP-4844 `blobVersionedHashes` (a flat array, not indexed by
    `data`). Empty for non-blob txs. -/
def parseBlobHashes (txJson : Json) : Array UInt256 :=
  (jsonArr (subObj txJson "blobVersionedHashes")).filterMap
    (fun h => match h with | .str s => some (hexToUInt256 s) | _ => none)

/-- EIP-4844 blob-tx validity that needs the type-3 signal (`Tx.execute` can't
    see it from the collapsed effective price): a blob tx (`maxFeePerBlobGas`
    present) must carry at least one blob, and every versioned hash must use the
    KZG version byte `0x01` (the hash's top byte). Fixtures: `emptyBlobhashList`,
    `wrongBlobhashVersion`. Count / no-create / fee-cap gates live in
    `Tx.execute`. -/
def invalidBlob (txJson : Json) (blobHashes : Array UInt256) : Bool :=
  if (txJson.getObjVal? "maxFeePerBlobGas").toOption.isNone then false
  else blobHashes.size = 0 ∨ blobHashes.any (fun h => h.toNat >>> 248 ≠ 1)

/-- Effective gas price: for EIP-1559 (`maxFeePerGas` present) it's
    `min(maxFeePerGas, baseFee + maxPriorityFeePerGas)`; otherwise the legacy
    `gasPrice`. A `maxFeePerGas` below `baseFee` yields an effective price below
    `baseFee`, which `Tx.execute`'s EIP-1559 floor (London+) then rejects as an
    invalid tx — so no extra gate is needed here. -/
def effectiveGasPrice (txJson : Json) (baseFee : Nat) : UInt256 :=
  if (txJson.getObjVal? "maxFeePerGas").toOption.isSome then
    let maxFee  := hexToNat (strField txJson "maxFeePerGas")
    let maxPrio := hexToNat (strField txJson "maxPriorityFeePerGas")
    UInt256.ofNat (Nat.min maxFee (baseFee + maxPrio))
  else hexToUInt256 (strField txJson "gasPrice")

/-- Parse the EIP-7702 `authorizationList` into `Tx.Authorization`s. Uses the
    fixture's recovered `signer` as the authority (consistent with this runner
    taking `transaction.sender` directly rather than recovering it). -/
def parseAuthList (txJson : Json) : List Tx.Authorization :=
  (jsonArr (subObj txJson "authorizationList")).toList.map (fun e =>
    { chainId   := hexToNat     (strField e "chainId")
      address   := hexToAddress (strField e "address")
      nonce     := hexToNat     (strField e "nonce")
      authority := hexToAddress (strField e "signer") })

/-- Build a `Tx.Transaction` from the transaction template and a chosen
    `(data, gas, value)` index triple, resolving the fee via `effectiveGasPrice`
    (`baseFee` is the block base fee). Assumes `txUnsupportedReason` already
    rejected the unmodelled variants. `to = ""` marks a contract-creating tx
    (`recipient = none`). -/
def buildTx (txJson : Json) (dataIdx gasIdx valIdx baseFee : Nat) : Tx.Transaction :=
  let toStr := strField txJson "to"
  { sender    := hexToAddress (strField txJson "sender")
    recipient := if toStr = "" then none else some (hexToAddress toStr)
    value     := hexToUInt256 (arrStr txJson "value" valIdx)
    data      := hexToBytes   (arrStr txJson "data" dataIdx)
    gasLimit  := hexToNat     (arrStr txJson "gasLimit" gasIdx)
    gasPrice  := effectiveGasPrice txJson baseFee
    nonce     := hexToUInt256 (strField txJson "nonce")
    accessList := parseAccessList txJson dataIdx
    maxFeePerBlobGas := hexToUInt256 (strField txJson "maxFeePerBlobGas")
    authList  := parseAuthList txJson }

/-- EIP-1559 / EIP-4844 validity conditions a legacy-shaped `Tx.execute` can't
    see (it only receives the *effective* `gasPrice`, not the fee caps). For a
    fee-market tx (`maxFeePerGas` present) the tx is invalid — not included,
    world left unchanged — when:
    * the priority fee exceeds the fee cap (`maxPriorityFeePerGas > maxFeePerGas`);
    * the sender can't afford `gasLimit · maxFeePerGas + value` plus, for a
      blob tx, the *cap-priced* blob fee `blob_count · GAS_PER_BLOB ·
      maxFeePerBlobGas` (EIP-4844's affordability check uses the caps, not the
      effective/burned prices — fixtures: `insufficient_balance_blob_tx`); or
    * `gasLimit` exceeds the block gas limit.
    Legacy txs return `false` here — `Tx.execute`'s own gates cover them. -/
def invalid1559 (txJson : Json) (gasIdx valIdx : Nat)
    (header : BlockHeader) (senderBalance : Nat)
    (blobHashes : Array UInt256) : Bool :=
  if (txJson.getObjVal? "maxFeePerGas").toOption.isNone then false
  else
    let maxFee   := hexToNat (strField txJson "maxFeePerGas")
    let maxPrio  := hexToNat (strField txJson "maxPriorityFeePerGas")
    let gasLimit := hexToNat (arrStr txJson "gasLimit" gasIdx)
    let value    := (hexToUInt256 (arrStr txJson "value" valIdx)).toNat
    let blobFeeCap := blobHashes.size * Tx.gasPerBlob
                        * hexToNat (strField txJson "maxFeePerBlobGas")
    maxPrio > maxFee
      || gasLimit * maxFee + value + blobFeeCap > senderBalance
      || gasLimit > header.gasLimit.toNat

/-- The EIP-2718 transaction *type* a fixture's transaction template denotes,
    from its distinguishing fields: an `authorizationList` marks a type-4
    set-code tx, `maxFeePerBlobGas`/`blobVersionedHashes` a type-3 blob tx,
    `maxFeePerGas` a type-2 fee-market tx, and an `accessLists` entry that is
    non-`null` *for the selected data index* a type-1 access-list tx (legacy
    fixtures may carry `accessLists: [null, …]`, which stays type 0). -/
def txTypeOf (txJson : Json) (dataIdx : Nat) : Nat :=
  let has (k : String) : Bool :=
    match (txJson.getObjVal? k).toOption with
    | some .null => false
    | some _     => true
    | none       => false
  if has "authorizationList" then 4
  else if has "maxFeePerBlobGas" ∨ has "blobVersionedHashes" then 3
  else if has "maxFeePerGas" ∨ has "maxPriorityFeePerGas" then 2
  else
    match (jsonArr (subObj txJson "accessLists"))[dataIdx]? with
    | some (Json.arr _) => 1
    | _                 => 0

/-- The fork a transaction type activates at: an envelope used *before* its
    activation fork is `TYPE_NOT_SUPPORTED` — invalid regardless of its body
    (fixtures: `test_eip2930_tx_validity[fork_<pre-Berlin>-invalid…]`,
    `test_blob_type_tx_pre_fork`, `test_set_code_type_tx_pre_fork`, …). -/
def typeActivation (t : Nat) : Fork :=
  match t with
  | 4 => .Prague
  | 3 => .Cancun
  | 2 => .London
  | 1 => .Berlin
  | _ => .Frontier

/-- EIP-7702 static validity `Tx.execute` can't see (it receives the parsed
    `authList`, not the type-4 signal): a set-code tx must carry a *non-empty*
    authorization list and cannot be a contract creation. Fixtures:
    `test_empty_authorization_list`, `test_contract_create`. -/
def invalid7702 (txJson : Json) (txType : Nat) : Bool :=
  txType == 4 ∧
    ((jsonArr (subObj txJson "authorizationList")).isEmpty
      ∨ strField txJson "to" = "")

----------------------------------------------------------------------------
-- Post-state comparison (mirrors tests/StateTestRunner.lean).
----------------------------------------------------------------------------

/-- Outcome tiers, strongest-first: `passRoot ⊃ passFull ⊃ passCore`. -/
inductive Outcome where
  /-- Storage + nonce + code match, but balances don't. -/
  | passCore
  /-- `passCore` plus exact balances, but the MPT `stateRoot` differs. -/
  | passFull
  /-- `passFull` plus the world MPT root matches the entry's `hash`. -/
  | passRoot
  | fail (msg : String)
  | incon (msg : String)
  deriving Repr

/-- Compare the run's final accounts to a post-state `state` object. Returns a
    list of mismatch descriptions; checks storage/nonce/code always, balance
    only when `checkBal` is set. Storage is checked over the union of pre-state
    and post-state slot keys (post omits zero slots, so a cleared non-zero
    pre-state slot would otherwise be invisible). -/
def cmpPost (finalAccounts : AccountMap)
    (preEntries postEntries : List (String × Json)) (checkBal : Bool) :
    List String := Id.run do
  let mut msgs := []
  for (addrStr, accJson) in postEntries do
    let a := hexToAddress addrStr
    let got := finalAccounts a
    let expNonce := hexToUInt256 (strField accJson "nonce")
    let expCode := hexToBytes (strField accJson "code")
    if got.nonce.toNat != expNonce.toNat then
      msgs := s!"{addrStr} nonce {got.nonce.toNat}≠{expNonce.toNat}" :: msgs
    if got.code.toList != expCode.toList then
      msgs := s!"{addrStr} code size {got.code.size}≠{expCode.size}" :: msgs
    let postSlots := storageEntries accJson
    let preSlots :=
      match preEntries.find? (fun (k, _) => k == addrStr) with
      | some (_, preJson) => storageEntries preJson
      | none              => []
    let mut seen : List String := []
    for (slot, val) in postSlots do
      seen := slot :: seen
      let k := hexToUInt256 slot
      let want := hexToUInt256 val
      if (got.storage k).toNat != want.toNat then
        msgs := s!"{addrStr}[{slot}] {(got.storage k).toNat}≠{want.toNat}" :: msgs
    for (slot, _) in preSlots do
      if seen.contains slot then continue
      let k := hexToUInt256 slot
      if (got.storage k).toNat != 0 then
        msgs := s!"{addrStr}[{slot}] {(got.storage k).toNat}≠0 (cleared)" :: msgs
    if checkBal then
      let expBal := hexToUInt256 (strField accJson "balance")
      if got.balance.toNat != expBal.toNat then
        msgs := s!"{addrStr} bal {got.balance.toNat}≠{expBal.toNat}" :: msgs
  return msgs

----------------------------------------------------------------------------
-- Per-entry runner.
----------------------------------------------------------------------------

/-- Run one `post[fork][i]` entry: select the tx variant, execute, and compare
    against the entry's expanded `state` (tiered) and `hash` (root tier). -/
def runEntry (preMap : AccountMap) (preEntries : List (String × Json))
    (env txJson : Json) (fork : Fork) (entry : Json) : Outcome :=
  let idx := subObj entry "indexes"
  let dataIdx := natField idx "data"
  let gasIdx  := natField idx "gas"
  let valIdx  := natField idx "value"
  match txUnsupportedReason txJson with
  | some reason => .incon reason
  | none =>
    let header := decodeEnv env fork
    let tx := buildTx txJson dataIdx gasIdx valIdx header.baseFeePerGas.toNat
    let blobHashes := parseBlobHashes txJson
    let txType := txTypeOf txJson dataIdx
    -- Fuel is a backstop against a 0-gas non-halting evaluator bug; the CI
    -- wall-timeout is the real bound on runaway tests.
    let fuel := 2 * tx.gasLimit + 100_000
    -- A typed tx failing a validity rule that the legacy-shaped `Tx.execute`
    -- can't see (type not yet activated at this fork, cap-based 1559/4844
    -- affordability, empty/wrong-version blob lists, 7702 static shape) is
    -- invalid: not applied, world unchanged — model it as an exceptional
    -- no-op (`finalAccounts := preMap`).
    let result : Tx.ExecResult :=
      if fork < typeActivation txType
         ∨ invalid1559 txJson gasIdx valIdx header (preMap tx.sender).balance.toNat blobHashes
         ∨ invalidBlob txJson blobHashes
         ∨ invalid7702 txJson txType then
        { finalAccounts := preMap, outcome := .exceptional }
      else EvmSemantics.Tx.execute preMap header tx fork fuel blobHashes
    match result.outcome with
    | .fuelExhausted => .incon "fuel exhausted"
    | _ =>
      let post := objEntries entry "state"
      match cmpPost result.finalAccounts preEntries post false with
      | [] =>
        match cmpPost result.finalAccounts preEntries post true with
        | [] =>
          let expRoot := hexToUInt256 (strField entry "hash")
          let isPrecompileAddr (a : AccountAddress) : Bool :=
            let n := a.val
            decide (1 ≤ n) && decide (n ≤ 9)
          let wasInPreState : AccountAddress → Bool :=
            fun a => preMap.contains a && ¬ isPrecompileAddr a
          match AccountMap.stateRoot result.finalAccounts fork wasInPreState with
          | some ourRoot =>
            if ourRoot.toNat == expRoot.toNat then .passRoot else .passFull
          | none => .passFull
        | _ => .passCore
      | msgs => .fail (String.intercalate "; " (msgs.take 3))

----------------------------------------------------------------------------
-- Tally + file/dir driver.
----------------------------------------------------------------------------

/-- Aggregate pass/fail counts across tests, mirroring the legacy runner so the
    `statetests_*` CI summary/check scripts parse the output verbatim. -/
structure Tally where
  passRoot : Nat := 0
  passFull : Nat := 0
  passCore : Nat := 0
  fail : Nat := 0
  incon : Nat := 0
  crash : Nat := 0
  deriving Inhabited

/-- Component-wise sum of two tallies. -/
def Tally.add (t u : Tally) : Tally :=
  { passRoot := t.passRoot + u.passRoot
    passFull := t.passFull + u.passFull
    passCore := t.passCore + u.passCore
    fail := t.fail + u.fail, incon := t.incon + u.incon, crash := t.crash + u.crash }

/-- Total number of classified cases. -/
def Tally.total (t : Tally) : Nat :=
  t.passRoot + t.passFull + t.passCore + t.fail + t.incon + t.crash

/-- Walk `dir` recursively, returning every `*.json` underneath, sorted. -/
partial def collectJson (dir : System.FilePath) :
    IO (Array System.FilePath) := do
  let mut out : Array System.FilePath := #[]
  for ent in (← dir.readDir) do
    let path := ent.path
    if (← path.isDir) then out := out ++ (← collectJson path)
    else if path.toString.endsWith ".json" then out := out.push path
  return out.qsort (fun a b => a.toString < b.toString)

/-- Turn a modern test key's `::`-name segment into an id-safe token: spaces
    and colons become `_` so the result can never contain the `": "` field
    separator that the summary / expected-failures scripts split on. -/
def sanitizeName (s : String) : String :=
  (s.replace " " "_").replace ":" "_"

/-- Derive a stable, colon-free, per-entry id: `<dir>_<file>_<Fork>_d<d>g<g>v<v>`,
    for EEST keys suffixed with the sanitized `::`-name and the post-array index.
    The modern test key is `<path>::<name>-fork_…`; the `<path>` segment (e.g.
    `GeneralStateTests/stCallCodes/Call1024OOG.json`) is used — with the
    `GeneralStateTests/` prefix and `.json` suffix stripped and `/` → `_` — so
    that same-named tests in different directories get distinct ids (a
    name-only id collides, masking a regression).

    Legacy `ethereum/tests` keys (`GeneralStateTests/…json::name`) carry exactly
    one top-level key per file with a distinct `d/g/v` per post entry, so `base`
    alone is unique and stays byte-stable — no baseline churn. EEST /
    `execution-specs` keys (`tests/…py::name[params]`) pack many parametrized
    keys per file — and some pack several post entries under a single key — all
    at `d0g0v0`; for those we append the sanitized name *and* the post-array
    index `entryIdx` so every case gets a distinct id instead of collapsing. -/
def entryId (testKey forkName : String) (d g v entryIdx : Nat) : String :=
  let parts := testKey.splitOn "::"
  let pathPart := parts.head!
  let dirFile := (((pathPart.replace "GeneralStateTests/" "").replace ".json" "")).replace "/" "_"
  let base := s!"{dirFile}_{forkName}_d{d}g{g}v{v}"
  if pathPart.startsWith "GeneralStateTests/" then base
  else
    let namePart := String.intercalate "::" (parts.drop 1)
    s!"{base}_{sanitizeName namePart}_e{entryIdx}"

/-- Run every `(fork, entry)` in one file; one `(tag, id, msg)` per entry
    (`tag ∈ {PASS_ROOT, PASS_FULL, PASS_CORE, FAIL, INCON, CRASH}`). Forks we
    don't model are skipped silently. -/
def runFileResults (path : System.FilePath) : IO (Array (String × String × String)) := do
  let txt ← IO.FS.readFile path
  match Json.parse txt with
  | .error e => return #[("CRASH", path.fileName.getD path.toString, s!"parse: {e}")]
  | .ok j =>
    let tests := match j with | .obj m => m.toArray.toList | _ => []
    let mut out := #[]
    for (testKey, testObj) in tests do
      let preEntries := objEntries testObj "pre"
      let preMap : AccountMap :=
        preEntries.foldl
          (fun σ (addrStr, accJson) => σ.set (hexToAddress addrStr) (mkAccount accJson))
          AccountMap.empty
      let env := subObj testObj "env"
      let txJson := subObj testObj "transaction"
      for (forkName, arr) in objEntries testObj "post" do
        match parseForkExact forkName with
        | none => pure ()
        | some fork =>
          -- `entryIdx` disambiguates several post entries sharing one EEST key
          -- (e.g. `test_eip_mainnet.py`, all at d0g0v0); unused for legacy ids.
          let mut entryIdx := 0
          for entry in jsonArr arr do
            let idx := subObj entry "indexes"
            let d := natField idx "data"
            let g := natField idx "gas"
            let v := natField idx "value"
            let id := entryId testKey forkName d g v entryIdx
            let r := match runEntry preMap preEntries env txJson fork entry with
              | .passRoot => ("PASS_ROOT", id, "")
              | .passFull => ("PASS_FULL", id, "")
              | .passCore => ("PASS_CORE", id, "")
              | .fail m   => ("FAIL", id, m)
              | .incon m  => ("INCON", id, m)
            out := out.push r
            entryIdx := entryIdx + 1
    return out

/-- Run `files` keeping up to `jobs` `Task`s continuously in flight, with an
    optional per-task wall-clock cap (`timeoutMs > 0`): a task exceeding the cap
    is marked `INCON wall-timeout`, its slot freed, and the next file dispatched
    (the abandoned task keeps running; Lean `Task`s aren't OS-cancellable).
    Output is in completion order; the summary scripts key on ids, not order. -/
def runFiles (files : Array System.FilePath) (jobs : Nat) (verbose : Bool)
    (timeoutMs : Nat := 0) : IO Tally := do
  let mut t : Tally := {}
  let n := files.size
  if n = 0 then return t
  let workers := Nat.max 1 jobs
  let mut slots :
      Array (Option (Nat × Nat × Task (Except IO.Error (Array (String × String × String))))) :=
    Array.replicate workers none
  let mut nextIdx : Nat := 0
  let mut remaining : Nat := n
  let foldResult : Tally → Bool →
      Except IO.Error (Array (String × String × String)) → IO Tally :=
    fun t verb r => do
      let mut t := t
      match r with
      | .ok results =>
        for (tag, name, msg) in results do
          match tag with
          | "PASS_ROOT" => t := { t with passRoot := t.passRoot + 1 }
          | "PASS_FULL" => t := { t with passFull := t.passFull + 1 }
          | "PASS_CORE" => t := { t with passCore := t.passCore + 1 }
          | "FAIL"      => t := { t with fail := t.fail + 1 }
                           if verb then IO.println s!"FAIL {name}: {msg}"
          | "INCON"     => t := { t with incon := t.incon + 1 }
                           if verb then IO.println s!"INCON {name}: {msg}"
          | _           => t := { t with crash := t.crash + 1 }
                           if verb then IO.println s!"CRASH {name}: {msg}"
      | .error e =>
        t := { t with crash := t.crash + 1 }
        if verb then IO.println s!"CRASH (task): {e}"
      return t
  for i in [0:workers] do
    if nextIdx < n then
      let now ← IO.monoMsNow
      let task ← IO.asTask (runFileResults files[nextIdx]!) Task.Priority.dedicated
      slots := slots.set! i (some (nextIdx, now, task))
      nextIdx := nextIdx + 1
  while remaining > 0 do
    let mut progress := false
    for i in [0:workers] do
      match slots[i]! with
      | none => pure ()
      | some (idx, startMs, task) =>
        let done ← IO.hasFinished task
        let elapsed := (← IO.monoMsNow) - startMs
        if done then
          t ← foldResult t verbose (← IO.wait task)
          remaining := remaining - 1
          progress := true
          if nextIdx < n then
            let now ← IO.monoMsNow
            let next ← IO.asTask (runFileResults files[nextIdx]!) Task.Priority.dedicated
            slots := slots.set! i (some (nextIdx, now, next))
            nextIdx := nextIdx + 1
          else
            slots := slots.set! i none
        else if timeoutMs > 0 ∧ elapsed > timeoutMs then
          t := { t with incon := t.incon + 1 }
          if verbose then
            IO.println s!"INCON {files[idx]!.fileName.getD files[idx]!.toString}: \
              wall-timeout (>{timeoutMs}ms, abandoned)"
          remaining := remaining - 1
          progress := true
          if nextIdx < n then
            let now ← IO.monoMsNow
            let next ← IO.asTask (runFileResults files[nextIdx]!) Task.Priority.dedicated
            slots := slots.set! i (some (nextIdx, now, next))
            nextIdx := nextIdx + 1
          else
            slots := slots.set! i none
    if !progress then IO.sleep 10
  return t

/-- Parse `-j N` and `--timeout MS` out of `args`; returns
    `(jobs (0 = unset), timeoutMs (0 = disabled), remaining args)`. -/
def parseFlags (args : List String) : Nat × Nat × List String := Id.run do
  let rec go : List String → Option Nat → Option Nat → List String → Nat × Nat × List String
    | [], j, tm, acc => (j.getD 0, tm.getD 0, acc.reverse)
    | "-j" :: v :: rest, _, tm, acc => go rest (some v.toNat!) tm acc
    | "--timeout" :: v :: rest, j, _, acc => go rest j (some v.toNat!) acc
    | x :: rest, j, tm, acc => go rest j tm (x :: acc)
  go args none none []

/-- Entry point: `gstatetests [-v] [-j N] [--timeout MS] <dir-or-file>`. -/
def main (args : List String) : IO Unit := do
  let verbose := args.contains "-v"
  let (jobs0, timeoutMs, rest) := parseFlags (args.filter (· != "-v"))
  let jobs ← if jobs0 > 0 then pure jobs0 else do
    match (← IO.getEnv "GSTATETESTS_JOBS") with
    | some s => pure (Nat.max 1 s.toNat!)
    | none   => pure 8
  let root : System.FilePath := rest.headD "."
  let files ← if (← root.isDir) then collectJson root else pure #[root]
  let t ← runFiles files jobs verbose timeoutMs
  IO.println s!"pass(root={t.passRoot} full+={t.passFull} core+={t.passCore}) \
fail={t.fail} incon={t.incon} crash={t.crash} (total {t.total})"

end GeneralStateTests

def main (args : List String) : IO Unit := GeneralStateTests.main args
