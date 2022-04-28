Require Import FA2InterfaceOwn.
Require Import FA2_Multi_Token.
Require Import FA2Types.
Require Import List.
Require Import Blockchain.
Require Import Monads.
Require Import Containers.
Require Import ZArith.
Require Import RecordUpdate.
Require Import Fees_Lib.
Require Import ContractCommon.
Import ListNotations.

Section Token_Manager.

Open Scope N_scope.

Context {BaseTypes : ChainBase}.

Definition mint_update_balances (txs : list MintBurnTx) (ledger: Ledger) : Ledger :=
    let mint := fun (tx: MintBurnTx) (l: Ledger) =>
        inc_balance tx.(mint_burn_owner) tx.(mint_burn_token_id) tx.(mint_burn_amount) l in
    fold_right mint ledger txs.

Definition mint_update_total_supply (txs : list MintBurnTx) (total_supplies : TokenTotalSupply) : option TokenTotalSupply :=
    let update := fun (tx : MintBurnTx) (supplies_opt : option TokenTotalSupply) =>
        do supplies <- supplies_opt ;
        do ts <- FMap.find tx.(mint_burn_token_id) supplies ;
        let new_s := ts + tx.(mint_burn_amount) in
        Some (FMap.update tx.(mint_burn_token_id) (Some new_s) supplies)
    in
    fold_right update (Some total_supplies) txs.

Definition mint_tokens (param : MintBurnTokensParam) (storage : MultiTokenStorage) : option MultiTokenStorage :=
    let new_ledger := mint_update_balances param storage.(ledger) in
    do new_supply <- mint_update_total_supply param storage.(token_total_supply);
    let new_s := storage<|ledger := new_ledger|><|token_total_supply := new_supply|> in
    Some new_s.

Definition burn_update_balances (txs : list MintBurnTx) (ledger : Ledger) : option Ledger :=
    let burn := fun (tx : MintBurnTx) (l_opt : option Ledger) =>
        do l <- l_opt ;
        dec_balance tx.(mint_burn_owner) tx.(mint_burn_token_id) tx.(mint_burn_amount) l 
    in
    fold_right burn (Some ledger) txs.

Definition burn_update_total_supply (txs : list MintBurnTx) (total_supplies : TokenTotalSupply) : option TokenTotalSupply :=
    let update := fun (tx: MintBurnTx) (supplies_opt : option TokenTotalSupply) =>
        do supplies <- supplies_opt ;    
        do ts <- FMap.find tx.(mint_burn_token_id) supplies ;
        do new_s <- maybe (ts - tx.(mint_burn_amount)) ;
        Some (FMap.update tx.(mint_burn_token_id) (Some new_s) supplies)
    in
    fold_right update (Some total_supplies) txs.

Definition burn_tokens (param : MintBurnTokensParam) (storage : MultiTokenStorage) : option MultiTokenStorage :=
    do new_ledger <- burn_update_balances param storage.(ledger) ;
    do new_supply <- burn_update_total_supply param storage.(token_total_supply) ;
    let new_s := storage<|ledger:= new_ledger|><|token_total_supply := new_supply|> in
    Some new_s.

Definition token_manager (param : TokenManager) (s : MultiTokenStorage) : option (MultiTokenStorage * list ActionBody) :=
    match param with
    | MintTokens param =>
        do new_s <- mint_tokens param s ;
        Some (new_s, [])
    | BurnTokens param => 
        do new_s <- burn_tokens param s ;
        Some (new_s, [])
    end.
    
End Token_Manager.