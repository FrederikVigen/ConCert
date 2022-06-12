(** * Fees part of the Minter Contract *)
(** This file contains the functionality for withdrawal of fees that were distributed by wrapping and unwrapping.
    The fees distributed is defined by the percentage set by the admin quorum. The withdrawal can be done either for a single token/xtz or for all of the tokens or xtz's
    This file together with Fees_Lib and Fees_Interface contains the full logic and functionality of the Fees part of the Minter Contract
    The file this file has been translated from can be found here:
    https://github.com/bender-labs/wrap-tz-contracts/blob/1655949e61b05a1c25cc00dcb8c1da9d91799f31/ligo/minter/fees.mligo
*)
Require Import Storage.
Require Import Blockchain.
Require Import Types.
Require Import Storage.
Require Import Fees_Lib.
Require Import Fees_Interface.
Require Import Serializable.
Require Import Monads.
From ConCert.Utils Require Import RecordUpdate.
From ConCert.Examples Require Import FA2Interface.
From ConCert.Execution Require Import Containers.
Require Import FA2Interface_Wrap.
Require Import Extras.
Require Import List.
Import ListNotations.
From Coq Require Import ZArith.
Require Import ContractCommon.


Section Fees.
Set Nonrecursive Elimination Schemes.
Context {BaseTypes : ChainBase}.
Open Scope N_scope.

(** ** Convert N to amount *)
Definition N_to_amount : N -> Amount := Z.of_N.

(** ** Sends XTZ's to a specific address from the contract address *)
Definition transfer_xtz (addr: Address) (value: N) : option ActionBody :=
    do _ <- throwIf (address_is_contract addr);
    Some (act_transfer addr (N_to_amount value)).

(** ** Withdraw an amount of XTZ *)
Definition withdraw_xtz (ctx : ContractCallContext) (a : option N) (s : XTZLedger) : option (list ActionBody * XTZLedger) :=
    let available := xtz_balance s ctx.(ctx_from)  in 
    let value_opt := match a with
    | Some v => if available <? v then None else Some v
    | None => Some available
    end in
    do value <- value_opt ;
    if available =? 0 then Some ([], s)
    else 
    do op <- transfer_xtz ctx.(ctx_from) value;
    let new_d := 
        if available - value =? 0
        then FMap.remove ctx.(ctx_from) s
        else FMap.update ctx.(ctx_from) (Some (available - value)) s
        in Some ([op], new_d).

(** ** The return type for transfer generation *)
Definition tx_result : Type := list transfer_destination * TokenLedger.

(** ** Generation of the FA2 transfer destinations *)
(** This function also returns an updated ledger with all of the transfer destinations applied *)
Definition generate_tx_destinations (ctx: ContractCallContext) (p : WithdrawTokensParam) (ledger: TokenLedger) : tx_result := 
    fold_left (fun (acc : tx_result) (token_id : N) => 
        let (dsts, s) := acc in
        let key := (p.(wtp_fa2_tokens), token_id) in
        let available := token_balance ledger ctx.(ctx_from) key in
        if available =? 0 then acc
        else let new_dst : transfer_destination := {|
            to_ := ctx.(ctx_from);
            dst_token_id := token_id;
            amount := available;
        |} in
        let new_ledger := FMap.remove (ctx.(ctx_from), key) s in
        ((new_dst :: dsts), new_ledger) 
    ) p.(wtp_tokens) ([], ledger).

(** ** Calls the transfer function on the fa2 contract with a list of destinations *)
Definition transfer_operation (fa2 from: Address) (dests : list transfer_destination): ActionBody :=
    let tx : transfer := {|
        from_ := from;
        txs := dests
    |} in
    act_call fa2 (N_to_amount 0) (serialize tx).

(** ** Genereate multiple token transfers and call the FA2 contract *)
Definition generate_tokens_transfer (ctx: ContractCallContext) (p : WithdrawTokensParam) (ledger: TokenLedger) : list ActionBody * TokenLedger :=
    let (tx_dsts, new_s) := generate_tx_destinations ctx p ledger in
    if N_of_nat (length tx_dsts) =? 0
    then ([], new_s)
    else 
        let callback_op := transfer_operation ctx.(ctx_contract_address) p.(wtp_fa2_tokens) tx_dsts in
        ([callback_op], new_s).
    
(** ** Generate a single token transfer and call the FA2 contract *)
Definition generate_token_transfer (ctx : ContractCallContext) (p : WithdrawTokenParam) (ledger: TokenLedger) : option (list ActionBody * TokenLedger) :=
    let key := (p.(fa2_token), p.(wtp_token_id)) in
    let available := token_balance ledger ctx.(ctx_from) key in
    do n <- sub available p.(wtp_amount);
    let destination : transfer_destination := {|
        to_ := ctx.(ctx_from);
        dst_token_id := p.(wtp_token_id);
        amount := p.(wtp_amount);
    |} in
    let callback_op := transfer_operation ctx.(ctx_contract_address) p.(fa2_token) [destination] in
    let new_ledger := 
    if n =? 0
    then FMap.remove (ctx.(ctx_from), key) ledger
    else FMap.update (ctx.(ctx_from), key) (Some n) ledger 
    in
    Some ([callback_op], new_ledger).
   

(** ** The Main entrypoint for the Fees *)
Definition fees_main (ctx : ContractCallContext) (s: State) (p: WithdrawalEntrypoint): option ReturnType :=
    match p with
    | Withdraw_all_tokens p =>
        let (ops, new_b) := generate_tokens_transfer ctx p s.(fees).(fees_storage_tokens) in
        Some (s<|fees:=s.(fees)<|fees_storage_tokens:=new_b|>|>, ops)
    | Withdraw_all_xtz =>
        do res <- withdraw_xtz ctx None s.(fees).(fees_storage_xtz) ;
        Some (s<|fees:=s.(fees)<|fees_storage_xtz:=snd res|>|>, fst res)
    | Withdraw_token p => 
        do res <- generate_token_transfer ctx p s.(fees).(fees_storage_tokens) ;
        Some (s<|fees:=s.(fees)<|fees_storage_tokens:=snd res|>|>, fst res)
    | Withdraw_xtz a => 
        do res <- withdraw_xtz ctx (Some a) s.(fees).(fees_storage_xtz);
        Some (s<|fees:=s.(fees)<|fees_storage_xtz:=snd res|>|>, fst res)
    end.
End Fees.