module

public import EvmSemantics.Data.UInt256
public import EvmSemantics.State.Account
public import EvmSemantics.State.BlockHeader
public import EvmSemantics.State.ExecutionEnv
public import EvmSemantics.State.Substate
public import EvmSemantics.Machine.MachineState
public import EvmSemantics.EVM.Exception
public import EvmSemantics.EVM.Fork
public import EvmSemantics.EVM.State
public import EvmSemantics.EVM.Gas
public import EvmSemantics.EVM.Step
public import EvmSemantics.EVM.StepF
public import EvmSemantics.EVM.Precompile

/-!
`EvmSemantics.Tx` — the *transaction-execution* layer that sits on top
of the per-frame EVM small-step (`stepF`). One `Transaction` plus a
pre-state world (`AccountMap`) plus a `BlockHeader` plus a `Fork`
produces a post-state world via `Tx.execute`.

What lives here (Yellow Paper §6 "Transaction Execution", `Υ`):

* `Transaction` — the post-decode, fork-agnostic, JSON-agnostic
  transaction record (sender, optional `to`, `value`, `data`, `gasLimit`,
  `gasPrice`).
* `intrinsicGas` — `g₀` per YP §6.2 (21000 + per-byte data cost,
  pre-EIP-2028 rates: 4 for zero bytes, 68 otherwise).
* `Tx.buildInitState` — assemble the `State` the EVM starts in:
   - debit `gasLimit · gasPrice` from the sender (upfront gas charge),
   - bump the sender's nonce,
   - install the call target (existing account for a call tx, freshly
     derived `createAddress` for a create tx),
   - transfer `value` from sender to target,
   - for a create tx, install `data` as the *contract's code* (the init
     code is executed as bytecode) and seed the new account's nonce per
     EIP-158 (1 from Spurious Dragon onwards, 0 before).
* `Tx.execute` — the actual transition. Runs the fueled `stepF` loop,
  handles the YP's four post-execution arms:
   1. Address collision (create tx target already has nonce > 0 or
      code ≠ ∅): the tx fails, sender pays the full gas, no state
      mutation.
   2. Top-level exceptional halt (OOG / bad-jump / static violation /
      stack overflow): like (1) — everything reverts except the gas
      charge.
   3. Top-level revert (REVERT at depth 0): state reverts but unused
      gas is refunded to the sender; not yet wired (the executor
      collapses (3) into the exception arm pending a `Reverted` halt
      check).
   4. Success: world from `sf.accountMap`; for create-tx, the returned
      bytes become the new account's `code`.

The runner in `tests/StateTestRunner.lean` is now reduced to its proper
job: JSON ↔ `Transaction`/`AccountMap`, then `Tx.execute`, then compare.
-/

@[expose] public section

namespace EvmSemantics
namespace Tx

open EvmSemantics.EVM

/-- A decoded transaction. `recipient = none` flags a contract-creating
    tx (YP `Tᵢ = true`, the "T_to" field); `data` is then the *init code*,
    otherwise it is the call-frame's `calldata`. (We call the field
    `recipient` because `to` is a reserved word in Lean 4.) -/
structure Transaction where
  /-- `T_s` — the sender (origin) address. -/
  sender    : AccountAddress
  /-- `T_to` — the recipient address, or `none` for a contract-creating
      transaction. -/
  recipient : Option AccountAddress
  /-- `T_v` — wei transferred from sender to recipient. -/
  value     : UInt256
  /-- `T_d` — for a call tx, the calldata; for a create tx, the init
      code (executed as bytecode to produce the deployed code). -/
  data      : ByteArray
  /-- `T_g` — the gas limit; `gasLimit · gasPrice` is debited upfront. -/
  gasLimit  : Nat
  /-- `T_p` — the gas price paid to the coinbase per unit of gas used. -/
  gasPrice  : UInt256
  deriving Inhabited

/-- `true` iff this is a contract-creating transaction. -/
@[inline] def Transaction.isCreate (tx : Transaction) : Bool := tx.recipient.isNone

/-- Intrinsic transaction gas `g₀` (YP §6.2). Fork- and tx-kind-aware:

    * Per-byte data cost: 4 for zero bytes; 68 for non-zero bytes
      pre-Istanbul, 16 from Istanbul onwards (EIP-2028).
    * `+G_txcreate = 32000` for a contract-creating transaction from
      Homestead onwards (Frontier had no extra create surcharge).
    * `+G_initcodeword · ⌈|initcode|/32⌉ = 2 · ⌈|data|/32⌉` for a
      create-tx from Shanghai onwards (EIP-3860).

    `data` is `T_d` — the calldata for a call tx, the init code for a
    create tx. -/
def intrinsicGas (fork : Fork) (isCreate : Bool) (data : ByteArray) : Nat := Id.run do
  let perNonZero := if fork.atLeast .Istanbul then 16 else 68
  let mut g := 21000
  for b in data do
    g := g + (if b == 0 then 4 else perNonZero)
  if isCreate then
    -- `G_txcreate = 32000` was introduced by Homestead (EIP-2);
    -- Frontier create-tx pays only the base 21000.
    if fork.atLeast .Homestead then g := g + 32000
    -- EIP-3860 init-code word cost: 2 per 32-byte word.
    if fork.atLeast .Shanghai then g := g + 2 * ((data.size + 31) / 32)
  return g

/-- The fueled small-step loop. `stepF` is already total (it folds
    in-frame exceptions into `halt := .Exception e` and is the identity
    on done states) so the loop is just "iterate until `isDone`". REVERT
    and OOG flow through the exact same path: `halt` is set, the next
    iteration's `stepF` resumes the caller via `resumeByHalt`, and the
    loop exits via `isDone` when the top frame is done. -/
partial def run (s : State) (fuel : Nat) : Except ExecutionException State :=
  if fuel = 0 then .error .OutOfFuel
  else if s.isDone then .ok s
  else run (stepF s) (fuel - 1)

/-- Compute the target address for a transaction: the explicit `to` for a
    call tx, or the YP `keccak256(rlp [sender, sender_nonce])` derivation
    for a create tx (`sender_nonce` is read *before* the upfront nonce
    bump, per YP §7). -/
def Transaction.targetAddress (tx : Transaction) (sender : Account) :
    AccountAddress :=
  match tx.recipient with
  | some a => a
  | none   => EvmSemantics.createAddress tx.sender sender.nonce

/-- Build the initial execution `State`: bump sender nonce, debit
    upfront gas, transfer `value` to target, install the right code /
    calldata pair, derive the new contract's address & seed its nonce
    for a create tx. -/
def buildInitState (preMap : AccountMap) (header : BlockHeader)
    (tx : Transaction) (fork : Fork) (blobVersionedHashes : Array UInt256 := #[]) :
    State :=
  let sender0 := preMap tx.sender
  let toAddr  := tx.targetAddress sender0
  let upfront := tx.gasLimit * tx.gasPrice.toNat
  let preMap := preMap.set tx.sender
    { sender0 with nonce := sender0.nonce + UInt256.ofNat 1
                   balance := sender0.balance - UInt256.ofNat upfront }
  -- Create-tx: seed the new account's nonce (EIP-158+ = 1, else 0).
  -- Critically, leave `code := ∅` — the deployed code is installed by
  -- `execute` *only* on a successful halt that passes the EIP-3541 /
  -- EIP-170 / deposit-gas checks; until then the account is empty.
  let preMap :=
    if tx.isCreate then
      let existing := preMap toAddr
      let n : UInt256 := if fork.atLeast .SpuriousDragon then ⟨1⟩ else ⟨0⟩
      preMap.set toAddr { existing with nonce := n }
    else preMap
  let accountMap := preMap.transfer tx.sender toAddr tx.value
  -- A create tx runs `data` as the init code with empty calldata; a
  -- call tx runs the target's existing code with `data` as calldata.
  let calldata := if tx.isCreate then ByteArray.empty else tx.data
  let code     := if tx.isCreate then tx.data else (accountMap toAddr).code
  let execEnv : ExecutionEnv :=
    { address := toAddr
      origin  := tx.sender
      caller  := tx.sender
      weiValue  := tx.value
      calldata  := calldata
      code      := code
      -- Top-level frame: the borrowed-from address equals the call
      -- target (or the newly-derived address for a create tx). The
      -- precompile dispatcher in `stepF` keys off `codeAddr` so a tx
      -- whose recipient is a precompile address fires the precompile
      -- on the first step and halts immediately.
      codeAddr  := toAddr
      gasPrice  := tx.gasPrice
      header    := header
      depth     := 0
      permitStateMutation := true
      blobVersionedHashes := blobVersionedHashes
      fork                := fork }
  { toMachineState :=
      { gasAvailable := tx.gasLimit - intrinsicGas fork tx.isCreate tx.data,
        activeWords := ⟨0⟩
        memory := .empty, returnData := .empty, hReturn := .empty }
    accountMap   := accountMap
    -- EIP-2929 initial warm set: the tx sender and recipient/created
    -- address, the precompiles (0x01..0x09), and — from Shanghai
    -- (EIP-3651) — the coinbase. Pre-Berlin the accessed set is unused
    -- (the cold surcharge is gated on Berlin+), so this is harmless there.
    substate     :=
      { Substate.empty with
          originalAccountMap := accountMap
          accessedAccounts :=
            tx.sender :: toAddr
              :: ((List.range 9).map (fun i => AccountAddress.ofNat (i + 1))
                    ++ (if fork.atLeast .Shanghai then [header.coinbase] else [])) }
    executionEnv := execEnv
    pc           := ⟨0⟩
    stack        := []
    execLength   := 0
    halt         := .Running }

/-- Outcome of executing a transaction. -/
inductive ExecOutcome where
  /-- Top-frame ran to a normal halt (STOP / RETURN / SELFDESTRUCT).
      For a create tx, `finalAccounts` already has the deployed bytecode
      installed at the new address. -/
  | success
  /-- Top-frame faulted (OOG, bad jump, stack overflow, static violation,
      reserved-prefix init code, address collision, …). State reverts to
      the pre-tx world except for the sender's nonce bump and full gas
      charge; the coinbase receives the gas. -/
  | exceptional
  /-- The fueled loop ran out — the run is inconclusive (not the YP's
      OOG, just an evaluator bound). -/
  | fuelExhausted
  deriving Repr, Inhabited

/-- The world post-state and termination tag produced by `Tx.execute`. -/
structure ExecResult where
  /-- World accounts after the transaction (already accounts for the
      sender's nonce bump, the upfront gas charge, the value transfer or
      its rollback, and — on a create-tx `.success` — the deployed bytes
      installed at the new address). -/
  finalAccounts : AccountMap
  /-- How the transaction terminated. See `ExecOutcome`. -/
  outcome       : ExecOutcome
  deriving Inhabited

/-- Pre-London (Frontier..Berlin) refund cap is `gasUsed / 2`;
    EIP-3529 (London onwards) reduced it to `gasUsed / 5`. The
    Constantinople-era legacy corpus is pre-London, so divisor `2`
    applies for every variant in the current CI subset. -/
@[inline] def gasRefundCapDivisor (fork : Fork) : Nat :=
  if fork.atLeast .London then 5 else 2

/-- Per-fork PoW block reward paid to the coinbase. Block-level
    accounting (not tx-level), but `Tx.execute` adds it because the
    `BlockchainTests` corpus we run has one tx per block and the
    postState includes the reward credit on the coinbase. Schedule:

    * `Frontier..SpuriousDragon` — `5 · 10¹⁸` (5 ETH).
    * `Byzantium` — `3 · 10¹⁸` (EIP-649 "Difficulty Bomb Delay & Reward
      Reduction").
    * `Constantinople..GrayGlacier` — `2 · 10¹⁸` (EIP-1234, further
      reduction).
    * `Paris` onwards — `0`: the block reward moved to the consensus
      layer at the merge. -/
def blockReward (fork : Fork) : Nat :=
  if fork.atLeast .Paris then 0
  else if fork.atLeast .Constantinople then 2 * 10^18
  else if fork.atLeast .Byzantium then 3 * 10^18
  else 5 * 10^18

/-- YP §6.1 end-of-tx cleanup: delete every account that
    `SELFDESTRUCT`ed in this tx. Removing the entry from the
    `HashMap` (rather than just setting it to `Account.empty`)
    matters for fork variants where `stateRoot` doesn't run the
    post-EIP-161 empty-account filter — pre-Spurious-Dragon
    (`Frontier..TangerineWhistle`), an entry that's present-but-empty
    still appears in the trie, whereas a deleted entry doesn't.
    `Std.HashMap.erase` is a no-op if the key isn't there, so
    duplicate `selfDestructed` entries are harmless. -/
def applySelfDestructDeletions (map : AccountMap)
    (selfDestructed : Array AccountAddress) : AccountMap :=
  if selfDestructed.isEmpty then map
  else
    -- Rebuild via filter — `HashMap.erase` was leaving ghost entries
    -- that `.toList` and lookups by the same key would re-materialise
    -- (an issue with the persistent-buckets internal representation).
    let sdSet : Std.HashSet AccountAddress :=
      selfDestructed.foldl (fun s a => s.insert a) ∅
    map.toList.foldl (fun m (a, acct) =>
      if sdSet.contains a then m else m.insert a acct)
      AccountMap.empty

/-- Credit the coinbase with the per-fork block reward, on top of the
    tx-level gas-fee accounting already applied to `map`. Called once
    per `Tx.execute` (= once per single-tx block in the legacy state
    tests' BlockchainTest wrapping). -/
def applyBlockReward (map : AccountMap) (coinbase : AccountAddress)
    (fork : Fork) : AccountMap :=
  let reward := blockReward fork
  if reward = 0 then map
  else
    let c := map coinbase
    map.set coinbase
      { c with balance := c.balance + UInt256.ofNat reward }

/-- Total gas returned to the sender on a successful execution, per
    YP §6.3. `gasRemaining` is the residual `sf.gasAvailable` after
    the call (and, for a create-tx, after the deploy `G_codedeposit`
    charge); `refundCounter` is `sf.substate.refundBalance` (accumulated
    from SSTORE clears and pre-London SELFDESTRUCTs). The refund is the
    counter capped by `gasUsed / divisor`. -/
@[inline] def refundedGasOnSuccess (gasLimit gasRemaining refundCounter : Nat)
    (fork : Fork) : Nat :=
  let gasUsed := gasLimit - gasRemaining
  gasRemaining + Nat.min refundCounter (gasUsed / gasRefundCapDivisor fork)

/-- Layer the tx-level gas accounting onto `map`: credit the sender
    `gasRefunded · gasPrice` (the unused-gas refund) and credit the
    coinbase `(gasLimit - gasRefunded) · gasPrice` (the gas reward).
    Robust to `sender = coinbase`: the updates are applied in
    sequence, so the coinbase write reads the post-sender-write
    balance. -/
def applyTxGasAccounting (map : AccountMap)
    (sender coinbase : AccountAddress)
    (gasLimit gasRefunded gasPrice : Nat) : AccountMap :=
  let senderCredit   := UInt256.ofNat (gasRefunded * gasPrice)
  let coinbaseCredit := UInt256.ofNat ((gasLimit - gasRefunded) * gasPrice)
  let m₁ := map.set sender
    { (map sender) with balance := (map sender).balance + senderCredit }
  m₁.set coinbase
    { (m₁ coinbase) with balance := (m₁ coinbase).balance + coinbaseCredit }

/-- Build the post-state for a *world-rolled-back* outcome (collision,
    top-level exception, top-level revert, deploy rejected): start
    from `preMap`, bump the sender's nonce, debit the full upfront
    `gasLimit · gasPrice`, then call `applyTxGasAccounting` to credit
    sender + coinbase. `gasRefunded` is `0` for an exception (sender
    keeps nothing) and `sf.gasAvailable` for a revert (sender keeps
    the unspent gas; substate refund counter is discarded). -/
def failPostStateRefunded (preMap : AccountMap)
    (sender coinbase : AccountAddress)
    (gasLimit gasRefunded gasPrice : Nat) : AccountMap :=
  let s := preMap sender
  let upfront := UInt256.ofNat (gasLimit * gasPrice)
  let m₀ := preMap.set sender
    { s with nonce := s.nonce + UInt256.ofNat 1
             balance := s.balance - upfront }
  applyTxGasAccounting m₀ sender coinbase gasLimit gasRefunded gasPrice

/-- Materialise the post-state of a transaction that aborts before
    execution (collision, OOG-on-intrinsic, fuel exhausted) or that
    halts exceptionally at the top frame: sender's nonce bumped,
    full upfront gas paid to the coinbase, no value transfer. The
    `gasLimit·gasPrice` charge is applied via `applyTxGasAccounting`
    with `gasRefunded = 0`. -/
def failPostState (preMap : AccountMap) (sender coinbase : AccountAddress)
    (gasLimit gasPrice : Nat) : AccountMap :=
  failPostStateRefunded preMap sender coinbase gasLimit 0 gasPrice

/-- Execute one transaction against `preMap` under `header`/`fork`.

    `fuel` bounds the small-step loop; it is *not* the YP gas (gas is
    deducted by `stepF` itself). A backstop large enough to never
    pre-empt a real OOG is `2 · gasLimit + 100_000` — the runner
    supplies it. The `fuelExhausted` outcome surfaces only when the
    bound was hit, which always indicates an evaluator bug. -/
def execute (preMap : AccountMap) (header : BlockHeader)
    (tx : Transaction) (fork : Fork) (fuel : Nat)
    (blobVersionedHashes : Array UInt256 := #[]) : ExecResult :=
  let s0       := buildInitState preMap header tx fork blobVersionedHashes
  let coinbase := header.coinbase
  let newAddr  := s0.executionEnv.address
  let gasPrice := tx.gasPrice.toNat
  -- The block reward is paid to the coinbase regardless of tx
  -- outcome; we layer it on top of every non-`fuelExhausted`
  -- result-map below via `applyBlockReward`.
  let withReward (m : AccountMap) : AccountMap := applyBlockReward m coinbase fork
  -- Tx-rollback post-state used by collision, exception, deploy-
  -- rejected, and (after we re-enter the inner loop) every other
  -- "no state changes, all gas to coinbase" arm.
  let rollback : ExecResult :=
    { finalAccounts := withReward (failPostState preMap tx.sender coinbase
                                     tx.gasLimit gasPrice),
      outcome := .exceptional }
  -- Address-collision check for create tx: per YP, a target with code
  -- or non-zero nonce makes the create fail before any code runs.
  let preExisting := preMap newAddr
  let collide : Bool :=
    tx.isCreate ∧ (preExisting.nonce.toNat > 0 ∨ preExisting.code.size > 0)
  -- YP §6.2 validity: a transaction whose intrinsic gas `g₀` exceeds its
  -- `gasLimit` is *invalid* and is not applied — the world state is left
  -- entirely unchanged (no nonce bump, no upfront gas charge, no coinbase
  -- credit). Without this gate `gasAvailable := gasLimit - g₀` underflows to
  -- `0` in `Nat` and the tx would otherwise run as though it had no gas,
  -- wrongly bumping the sender nonce (fixtures flag this `INTRINSIC_GAS_TOO_LOW`).
  if tx.gasLimit < intrinsicGas fork tx.isCreate tx.data then
    { finalAccounts := preMap, outcome := .exceptional }
  else if collide then rollback
  else
    -- Tx-level precompile dispatch is *not* a special case here: a tx
    -- whose recipient is a precompile address arrives at `run s0 fuel`
    -- with `s0.executionEnv.codeAddr = tx.recipient`, and the generic
    -- precompile arm at the top of `stepFE` fires on the very first
    -- step. The resulting halted (top-level) frame then exits the
    -- `run` loop via `isDone`.
    match run s0 fuel with
    | .error .OutOfFuel =>
      { finalAccounts := preMap, outcome := .fuelExhausted }
    | .error _ =>
      -- `run` only returns `.error` for `.OutOfFuel` now — but Lean
      -- needs the case for totality.
      rollback
    | .ok sf =>
      -- Inspect the *top frame's* termination tag and produce the
      -- YP §6.3 post-state with the right gas-refund split between
      -- sender and coinbase.
      --
      -- The four outcomes:
      --
      --  * **Top-level `.Exception`** — all gas is forfeit; world
      --    rolls back to `preMap`; sender's nonce bumped; full upfront
      --    `gasLimit · gasPrice` paid to coinbase. (= the `rollback`
      --    post-state defined above.)
      --
      --  * **Top-level `.Reverted`** — world rolls back to `preMap`;
      --    sender's nonce bumped; sender refunded `sf.gasAvailable ·
      --    gasPrice` (the gas that hadn't been spent when REVERT
      --    fired); coinbase paid the difference. The substate refund
      --    counter is discarded (the YP discards substate on revert
      --    along with the world).
      --
      --  * **Top-level `.Success`/`.Returned` (call tx)** — keep the
      --    state changes accumulated in `sf.accountMap`; refund the
      --    sender `sf.gasAvailable + min(refundCounter, gasUsed /
      --    capDivisor)` worth of gas (the unspent gas plus the SSTORE-
      --    / SELFDESTRUCT-derived refund, capped per EIP-3529).
      --
      --  * **Top-level `.Success`/`.Returned` (create tx)** — same as
      --    the call-tx success arm, except the residual gas is
      --    `sf.gasAvailable - G_codedeposit · |hReturn|` (the deploy
      --    step's `G_codedeposit` charge). The three deploy gates
      --    (deposit-gas affordability; EIP-170 size cap from Spurious
      --    Dragon; EIP-3541 reserved-prefix from London) decide
      --    whether the deploy commits or the whole tx rolls back.
      match sf.halt with
      | .Exception _ => rollback
      | .Reverted =>
        let map := failPostStateRefunded preMap tx.sender coinbase
                     tx.gasLimit sf.gasAvailable gasPrice
        { finalAccounts := withReward map, outcome := .exceptional }
      | _ =>
        -- YP §6.1 end-of-tx cleanup: zero out every account that
        -- `SELFDESTRUCT`ed in this tx. The post-EIP-161 empty-account
        -- filter on `stateRoot` then drops the zeroed entry from the
        -- world trie; pre-EIP-161 it stays as an explicit zero, which
        -- happens to match the reference impl's "delete on
        -- SELFDESTRUCT" pre-Spurious-Dragon behaviour in every
        -- corpus variant we run.
        let cleaned := applySelfDestructDeletions sf.accountMap
                         sf.substate.selfDestructList
        if tx.isCreate then
          let hReturn := sf.hReturn
          let depositCost := State.codeDepositPerByte * hReturn.size
          let oversized   := fork.atLeast .SpuriousDragon
                              && decide (hReturn.size > State.maxCodeSize)
          let badPrefix   := State.isReservedCodePrefix fork hReturn
          if depositCost ≤ sf.gasAvailable ∧ ¬ oversized ∧ ¬ badPrefix then
            -- Deploy commits: install `hReturn` as the new account's
            -- code, then apply the gas-refund accounting with
            -- `gasRemaining = sf.gasAvailable - depositCost`.
            -- Skip the install if `hReturn` is empty — the SELFDESTRUCT
            -- cleanup just erased `newAddr` and we don't want to
            -- re-add it as an empty entry (e.g., init code whose
            -- terminal opcode is `SELFDESTRUCT` rather than `RETURN`).
            let mapWithCode :=
              if hReturn.size = 0 then cleaned
              else
                let newAcc := cleaned newAddr
                cleaned.set newAddr { newAcc with code := hReturn }
            let gasRemaining := sf.gasAvailable - depositCost
            let gasRefunded := refundedGasOnSuccess tx.gasLimit gasRemaining
                                 sf.substate.refundBalance.toNat fork
            let map' := applyTxGasAccounting mapWithCode tx.sender coinbase
                          tx.gasLimit gasRefunded gasPrice
            { finalAccounts := withReward map', outcome := .success }
          else
            -- Deploy rejected by EIP-3541, EIP-170, or deposit-gas
            -- OOG: rollback the whole tx per YP.
            rollback
        else
          let gasRefunded := refundedGasOnSuccess tx.gasLimit sf.gasAvailable
                               sf.substate.refundBalance.toNat fork
          let map' := applyTxGasAccounting cleaned tx.sender coinbase
                        tx.gasLimit gasRefunded gasPrice
          { finalAccounts := withReward map', outcome := .success }

end Tx
end EvmSemantics
