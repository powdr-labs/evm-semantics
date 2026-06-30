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

/-- One step of the executable EVM, but **total** in the in-frame
    exception sense: every `Except.error e` `stepF` would have returned
    is folded into `halt := .Exception e` on the active frame. That
    makes exceptions look exactly like a `REVERT` from `stepF`'s
    perspective — `halt` is set, `isDone` decides whether the loop is
    over, and the next iteration's `stepF` routes the halted state
    through `resumeByHalt` (which dispatches CALL vs CREATE frames).

    Net result: `run` becomes a one-liner — *no special handling at
    all*. REVERT and OOG flow through the exact same path; the
    surface-level distinction belongs to the caller, which can inspect
    `s.halt` after the loop exits via `isDone`. -/
@[inline] def step (s : State) : State :=
  match stepF s with
  | .ok s'  => s'
  | .error e => { s with halt := .Exception e }

/-- The fueled small-step loop. Just iterate `step` until `isDone`. -/
partial def run (s : State) (fuel : Nat) : Except ExecutionException State :=
  if fuel = 0 then .error .OutOfFuel
  else if s.isDone then .ok s
  else run (step s) (fuel - 1)

/-- Compute the target address for a transaction: the explicit `to` for a
    call tx, or the YP `keccak256(rlp [sender, sender_nonce])` derivation
    for a create tx (`sender_nonce` is read *before* the upfront nonce
    bump, per YP §7). -/
def Transaction.targetAddress (tx : Transaction) (sender : Account) :
    AccountAddress :=
  match tx.recipient with
  | some a => a
  | none   => (EvmSemantics.createAddress tx.sender sender.nonce.toNat).getD default

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
    substate     := { Substate.empty with originalAccountMap := accountMap }
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

/-- Materialise the post-state of a *failed* transaction (collision or
    top-level exception): everything from `preMap` except the sender's
    nonce bumped, the full `gasLimit·gasPrice` debited, and the coinbase
    credited the same amount. The value transfer that `buildInitState`
    layered on top is *not* replayed. -/
def failPostState (preMap : AccountMap) (sender coinbase : AccountAddress)
    (upfront : Nat) : AccountMap :=
  let s := preMap sender
  let c := preMap coinbase
  let m₁ := preMap.set sender
    { s with nonce := s.nonce + UInt256.ofNat 1
             balance := s.balance - UInt256.ofNat upfront }
  m₁.set coinbase { c with balance := c.balance + UInt256.ofNat upfront }

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
  let upfront  := tx.gasLimit * tx.gasPrice.toNat
  let coinbase := header.coinbase
  let newAddr  := s0.executionEnv.address
  -- The YP tx-level rollback post-state: sender's nonce bumped, sender
  -- debited the full upfront gas charge, coinbase credited the same
  -- amount; everything else as in `preMap`. Used by the collision,
  -- top-level-exception, top-level-revert, and deploy-rejected arms.
  let rollback : ExecResult :=
    { finalAccounts := failPostState preMap tx.sender coinbase upfront,
      outcome := .exceptional }
  -- Address-collision check for create tx: per YP, a target with code
  -- or non-zero nonce makes the create fail before any code runs.
  let preExisting := preMap newAddr
  let collide : Bool :=
    tx.isCreate ∧ (preExisting.nonce.toNat > 0 ∨ preExisting.code.size > 0)
  if collide then rollback
  else
    match run s0 fuel with
    | .error .OutOfFuel =>
      { finalAccounts := preMap, outcome := .fuelExhausted }
    | .error _ =>
      -- `run` only returns `.error` for `.OutOfFuel` now — but Lean
      -- needs the case for totality.
      rollback
    | .ok sf =>
      -- Inspect the *top frame's* termination tag.
      --
      -- For a **call tx**: `.Success`/`.Returned` keeps the world
      -- mutations `sf.accountMap` produced; `.Reverted` and
      -- `.Exception _` roll back to the pre-tx state (sender keeps
      -- value, gas paid in full to the coinbase).
      --
      -- For a **create tx** with `.Success`/`.Returned`: run the YP
      -- `Λ` deploy step — install `sf.hReturn` as `newAddr.code` only
      -- if all three deploy checks pass:
      --   (i) `G_codedeposit · |hReturn| ≤ sf.gasAvailable`
      --       (deposit-gas affordability);
      --  (ii) `|hReturn| ≤ maxCodeSize` from Spurious Dragon onwards
      --       (EIP-170);
      -- (iii) `hReturn` does *not* begin with `0xEF` from London
      --       onwards (EIP-3541).
      -- Any one of these failing — or `.Reverted` / `.Exception` —
      -- collapses the create-tx into the rollback post-state.
      match sf.halt with
      | .Exception _ | .Reverted => rollback
      | _ =>
        if tx.isCreate then
          let hReturn := sf.hReturn
          let depositCost := State.codeDepositPerByte * hReturn.size
          let oversized   := fork.atLeast .SpuriousDragon
                              && decide (hReturn.size > State.maxCodeSize)
          let badPrefix   := State.isReservedCodePrefix fork hReturn
          if depositCost ≤ sf.gasAvailable ∧ ¬ oversized ∧ ¬ badPrefix then
            let newAcc := sf.accountMap newAddr
            let map' := sf.accountMap.set newAddr { newAcc with code := hReturn }
            { finalAccounts := map',
              outcome := .success }
          else
            -- Deploy rejected by EIP-3541, EIP-170, or deposit-gas
            -- OOG: rollback the whole tx per YP.
            rollback
        else
          { finalAccounts := sf.accountMap, outcome := .success }

end Tx
end EvmSemantics
