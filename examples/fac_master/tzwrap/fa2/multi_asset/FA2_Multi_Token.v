(** * FA2 Multi Token*)
(** This file contains the implementation of the file: 
https://github.com/bender-labs/wrap-tz-contracts/blob/1655949e61b05a1c25cc00dcb8c1da9d91799f31/ligo/fa2/multi_asset/fa2_multi_token.mligo
It contains methods for changing the balances of token accounts holding wrapped assets, mainly through transfers.
*)
Require Import ZArith.
Require Import Blockchain.
From ConCert.Examples Require Import FA2Interface.
Require Import FA2Interface_Wrap.
Require Import Fees_Lib.
Require Import FA2Types.
Require Import Containers.
Require Import Monads.
Require Import FA2_Operator_Lib.
Require Import List.
Require Import Serializable.
Require Import RecordUpdate.
Require Import ContractCommon.
Import ListNotations.

Section FA2_Multi_Token.

Context {BaseTypes : ChainBase}.

Open Scope N_scope.

(** ** Get Balance Amount *)
Definition get_balance_amt (key : (Address * N)) (ledger : Ledger) : N :=
    let bal_opt := FMap.find key ledger in
    match bal_opt with
    | None => 0
    | Some b => b
    end.
(** ** Increment Balance *)    
Definition inc_balance (owner: Address) (token_id : token_id) (amt : N) (ledger : Ledger) : Ledger :=
    let key := (owner, token_id) in 
    let bal := get_balance_amt key ledger in 
    let updated_bal := bal + amt in 
    if updated_bal =? 0
    then FMap.remove key ledger
    else FMap.update key (Some updated_bal) ledger.

(** ** Decrement Balance *)
Definition dec_balance (owner: Address) (token_id : token_id) (amt : N) (ledger : Ledger) : option Ledger :=
    let key := (owner, token_id) in
    let bal := get_balance_amt key ledger in
    do new_bal <- sub bal  amt ;
     Some (if new_bal =? 0
    then FMap.remove key ledger
    else FMap.update key (Some new_bal) ledger).

(** ** Transfer *)
Definition transfer (ctx : ContractCallContext) (transfers : list transfer) (validate_op : OperatorValidator) (storage : MultiTokenStorage) : option Ledger :=
  let make_transfer := fun (l_opt : option Ledger) (tx : transfer) =>
    do l <- l_opt ;
    fold_left (fun (ll_opt : option Ledger) (dst : transfer_destination) =>
      do ll <- ll_opt ;
      do _ <- FMap.find dst.(dst_token_id) storage.(mts_token_metadata) ;
      do _ <- validate_op tx.(from_) ctx.(ctx_from) dst.(dst_token_id) storage.(operators) ;
      do lll <- dec_balance tx.(from_) dst.(dst_token_id) dst.(amount) ll ;
      Some (inc_balance dst.(to_) dst.(dst_token_id) dst.(amount) lll)
    ) tx.(txs) (Some l)
  in
  fold_left make_transfer transfers (Some storage.(ledger)).

(** ** Get Balance *)
Definition get_balance (p : balance_of_param) (ledger : Ledger) (tokens : TokenMetaDataStorage) : option ActionBody :=
  let to_balance := fun (acc_opt : option (list balance_of_response)) (r : balance_of_request) =>
    do acc <- acc_opt ;
    do _ <- FMap.find r.(bal_req_token_id) tokens ;
    let key := (r.(owner), r.(bal_req_token_id)) in
    let bal := get_balance_amt key ledger in
    let response := {|request := r; balance := bal|} in
    Some (response :: acc)
  in
  let responses_opt := fold_left to_balance p.(bal_requests) (Some []) in
  do responses <- responses_opt ;
  Some (act_call p.(bal_callback) 0 (serialize responses)).

(** ** Main method of Multi Token *)
Definition fa2_main (ctx : ContractCallContext) (param : FA2EntryPoints) (storage : MultiTokenStorage) : option (MultiTokenStorage * (list ActionBody)) :=
  match param with 
  | FA2_Transfer txs => 
    do new_ledger <- transfer ctx txs default_operator_validator storage ;
    let new_storage := storage<|ledger := new_ledger|> in
    Some (new_storage, [])
  | Balance_of p => 
    do op <- get_balance p storage.(ledger) storage.(mts_token_metadata) ;
    Some (storage, [op])
  | Update_operators updates =>
    do new_ops <- fa2_update_operators ctx updates storage.(operators) ;
    Some (storage, [])
  end.
    
End FA2_Multi_Token.