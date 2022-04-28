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

Definition sub (n m : N) : option N := do _ <- throwIf (n <? m) ; Some (n - m).

Definition bps_of (val : N) (bps : bps) : N :=
    val * bps / 10000.

Definition compute_fees (val : N) (bps : bps) : option (N * N) :=
    let fees := bps_of val bps in
    do amount_to_mint <- sub val fees;
    Some (amount_to_mint, fees).

Definition token_balance (ledger : TokenLedger) (target : Address) (token : TokenAddress) : N :=
    let info_opt := (FMap.find (target, token) ledger) in 
    match info_opt with
    | Some n => n
    | None => 0
    end.

Definition xtz_balance (ledger: XTZLedger) (target: Address) :=
    let info_opt := (FMap.find target ledger) in
    match info_opt with
    | Some n => n
    | None => 0
    end.

Definition inc_token_balance (ledger: TokenLedger) (target: Address) (token: TokenAddress) (value: N) :=
    let current_balance := token_balance ledger target token in
    let key := (target, token) in
    FMap.update key (Some (value + current_balance)) ledger.


Definition inc_xtz_balance (ledger: XTZLedger) (target: Address) (value: N) :=
    let info_opt := (FMap.find target ledger) in
    let new_balance:= 
        match info_opt with
        | None => value
        | Some info => value + info
        end in
    FMap.update target (Some (new_balance)) ledger.

Definition check_fees_high_enough (v min: N) :=
    throwIf (v <? min).

Definition check_nft_fees_high_enough (v min: N) :=
    throwIf (v <? min).

End Fees_Lib.