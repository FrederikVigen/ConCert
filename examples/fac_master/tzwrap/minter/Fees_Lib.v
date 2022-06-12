(** * Fees Library for the Fees part of the Minter Contract *)
(** This file contains helper functions that are used in the Fees file which is a part of the Minter Contract
    The file this file has been translated from can be found here:
    https://github.com/bender-labs/wrap-tz-contracts/blob/1655949e61b05a1c25cc00dcb8c1da9d91799f31/ligo/minter/fees_lib.mligo
*)
Require Import Storage.
Require Import Blockchain.
Require Import Types.
Require Import ZArith.
Require Import Monads.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import ContractCommon.


Section Fees_Lib.
Context {BaseTypes : ChainBase}.

Open Scope N_scope.

(** ** Substitution function with optional return based on underflow *)
Definition sub (n m : N) : option N := do _ <- throwIf (n <? m) ; Some (n - m).

(** ** Converts N to Basis Points*)
Definition bps_of (val : N) (bps : bps) : N :=
    val * bps / 10000.

(** ** Splits input into fees and amount to mint *)
Definition compute_fees (val : N) (bps : bps) : option (N * N) :=
    let fees := bps_of val bps in
    do amount_to_mint <- sub val fees;
    Some (amount_to_mint, fees).

(** ** Gets the token balance of a specific address on the Ledger *)
Definition token_balance (ledger : TokenLedger) (target : Address) (token : TokenAddress) : N :=
    let info_opt := (FMap.find (target, token) ledger) in 
    match info_opt with
    | Some n => n
    | None => 0
    end.

(** ** Gets the XTZ balance of a specific address on the ledger *)
Definition xtz_balance (ledger: XTZLedger) (target: Address) :=
    let info_opt := (FMap.find target ledger) in
    match info_opt with
    | Some n => n
    | None => 0
    end.

(** ** Increments the balance for a specific token *)
Definition inc_token_balance (ledger: TokenLedger) (target: Address) (token: TokenAddress) (value: N) :=
    let current_balance := token_balance ledger target token in
    let key := (target, token) in
    FMap.update key (Some (value + current_balance)) ledger.

(** ** Increments the XTZ balance for a specific token *)
Definition inc_xtz_balance (ledger: XTZLedger) (target: Address) (value: N) :=
    let info_opt := (FMap.find target ledger) in
    let new_balance:= 
        match info_opt with
        | None => value
        | Some info => value + info
        end in
    FMap.update target (Some (new_balance)) ledger.

(** ** Check if fees are high enough *)
(** The 2 checking functions are identical because on the LIGO side it is possible to add a fail message, where this is not possible for the throwIf functionality in Coq*)
Definition check_fees_high_enough (v min: N) :=
    throwIf (v <? min).

Definition check_nft_fees_high_enough (v min: N) :=
    throwIf (v <? min).

End Fees_Lib.