Require Import ZArith.
Require Import Blockchain.
From ConCert.Examples Require Import FA2Interface.
Require Import FA2InterfaceOwn.
Require Import Fees_Lib.
Require Import FA2Types.
Require Import Containers.
Require Import Monads.
Require Import FA2_Operator_Lib.
Require Import List.
Require Import Serializable.
Require Import RecordUpdate.
Import ListNotations.

Section FA2_Multi_Token.

Context {BaseTypes : ChainBase}.

Definition get_balance_amt (key : (Address * N)) (ledger : Ledger) : N :=
    let bal_opt := FMap.find key ledger in
    match bal_opt with
    | None => 0
    | Some b => b
    end.
    
Definition inc_balance (owner: Address) (token_id : token_id) (amt : N) (ledger : Ledger) : Ledger :=
    let key := (owner, token_id) in 
    let bal := get_balance_amt key ledger in 
    let updated_bal := bal + amt in 
    if updated_bal =? 0
    then FMap.remove key ledger
    else FMap.update key (Some updated_bal) ledger.

Definition dec_balance (owner: Address) (token_id : token_id) (amt : N) (ledger : Ledger) : option Ledger :=
    let key := (owner, token_id) in
    let bal := get_balance_amt key ledger in
    do new_bal <- maybe (bal - amt) ;
     if new_bal =? 0
    then Some (FMap.remove key ledger)
    else Some (FMap.update key (Some new_bal) ledger).

Definition transfer (ctx : ContractCallContext) (transfers : list Transfer) (validate_op : OperatorValidator) (storage : MultiTokenStorage) : option Ledger :=
  let make_transfer := fun (tx : Transfer) (l_opt : option Ledger) =>
    do l <- l_opt ;
    fold_right (fun (dst : TransferDestination) (ll_opt : option Ledger) =>
      do ll <- ll_opt ;
      do _ <- FMap.find dst.(dst_token_id) storage.(token_metadata) ;
      let u := validate_op tx.(from_) ctx.(ctx_from) dst.(dst_token_id) storage.(operators) in
      do lll <- dec_balance tx.(from_) dst.(dst_token_id) dst.(amount) ll ;
      Some (inc_balance dst.(to_) dst.(dst_token_id) dst.(amount) lll)
    ) (Some l) tx.(txs)
  in
  fold_right make_transfer (Some storage.(ledger)) transfers.

Definition get_balance (p : balance_of_param) (ledger : Ledger) (tokens : TokenMetaDataStorage) : option ActionBody :=
  let to_balance := fun (r : balance_of_request) (acc_opt : option (list balance_of_response)) =>
    do acc <- acc_opt ;
    do _ <- FMap.find r.(bal_req_token_id) tokens ;
    let key := (r.(owner), r.(bal_req_token_id)) in
    let bal := get_balance_amt key ledger in
    let response := {|request := r; balance := bal|} in
    Some (response :: acc)
  in
  let responses_opt := fold_right to_balance (Some []) p.(bal_requests) in
  do responses <- responses_opt ;
  Some (act_call p.(bal_callback) 0 (serialize responses)).

Definition fa2_main (ctx : ContractCallContext) (param : FA2EntryPoints) (storage : MultiTokenStorage) : option ((list ActionBody) * MultiTokenStorage) :=
  match param with 
  | FA2_Transfer txs => 
    do new_ledger <- transfer ctx txs default_operator_validator storage ;
    let new_storage := storage<|ledger := new_ledger|> in
    Some ([], new_storage)
  | Balance_of p => 
    do op <- get_balance p storage.(ledger) storage.(token_metadata) ;
    Some ([op], storage)
  | Update_operators updates =>
    do new_ops <- fa2_update_operators ctx updates storage.(operators) ;
    Some ([], storage)
  end.
    
End FA2_Multi_Token.