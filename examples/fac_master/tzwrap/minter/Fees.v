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
Require Import FA2InterfaceOwn.
Require Import Extras.
Require Import List.
Import ListNotations.
From Coq Require Import ZArith.
Require Import ContractCommon.


Section Fees.
Set Nonrecursive Elimination Schemes.
Context {BaseTypes : ChainBase}.

Open Scope N_scope.

Definition N_to_amount : N -> Amount := Z.of_N.

Definition transfer_xtz (addr: Address) (value: N) : option ActionBody :=
    do _ <- throwIf (address_is_contract addr);
    Some (act_transfer addr (N_to_amount value)).

Definition withdraw_xtz (ctx : ContractCallContext) (a : option N) (s : XTZLedger) : option (list ActionBody * XTZLedger) :=
    let available :=  xtz_balance s ctx.(ctx_from)  in 
    do v <- a;
    do _ <- throwIf (available <? v);
    if available =? 0 then Some ([], s)
    else 
    do op <- transfer_xtz ctx.(ctx_from) v;
    let new_d := 
        if available - v =? 0
        then FMap.remove ctx.(ctx_from) s
        else FMap.update ctx.(ctx_from) (Some (available - v)) s
        in Some ([op], new_d).

Definition tx_result : Type := list TransferDestination * TokenLedger.

Definition generate_tx_destinations (ctx: ContractCallContext) (p : WithdrawTokensParam) (ledger: TokenLedger) : tx_result := 
    fold_right (fun (token_id : N) (acc : tx_result) => 
        let (dsts, s) := acc in
        let key := (p.(fa2_tokens), token_id) in
        let available := token_balance ledger ctx.(ctx_from) key in
        if available =? 0 then acc
        else let new_dst : TransferDestination := {|
            to_ := ctx.(ctx_from);
            dst_token_id := token_id;
            amount := available;
        |} in
        acc
    ) ([], ledger) p.(tokens).

Definition transfer_operation (fa2 from: Address) (dests : list TransferDestination): ActionBody :=
    let tx : Transfer := {|
        from_ := from;
        txs := dests
    |} in
    act_call fa2 (N_to_amount 0) (serialize tx).

Definition generate_tokens_transfer (ctx: ContractCallContext) (p : WithdrawTokensParam) (ledger: TokenLedger) : list ActionBody * TokenLedger :=
    let (tx_dsts, new_s) := generate_tx_destinations ctx p ledger in
    if N_of_nat (length tx_dsts) =? 0
    then ([], new_s)
    else 
        let callback_op := transfer_operation ctx.(ctx_contract_address) p.(fa2_tokens) tx_dsts in
        ([callback_op], new_s).
    
Definition generate_token_transfer (ctx : ContractCallContext) (p : WithdrawTokenParam) (ledger: TokenLedger) : option (list ActionBody * TokenLedger) :=
    let key := (p.(fa2_token), p.(wtp_token_id)) in
    let available := token_balance ledger ctx.(ctx_from) key in
    do n <- maybe (available - p.(wtp_amount));
    let destination : TransferDestination := {|
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