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
    let mint := fun (l: Ledger) (tx: MintBurnTx) =>
        inc_balance tx.(mint_burn_owner) tx.(mint_burn_token_id) tx.(mint_burn_amount) l in
    fold_left mint txs ledger.

Definition mint_update_total_supply (txs : list MintBurnTx) (total_supplies : TokenTotalSupply) : option TokenTotalSupply :=
    let update := fun (supplies_opt : option TokenTotalSupply) (tx : MintBurnTx) =>
        do supplies <- supplies_opt ;
        do ts <- FMap.find tx.(mint_burn_token_id) supplies ;
        let new_s := ts + tx.(mint_burn_amount) in
        Some (FMap.update tx.(mint_burn_token_id) (Some new_s) supplies)
    in
    fold_left update txs (Some total_supplies).

Definition mint_tokens (param : MintBurnTokensParam) (storage : MultiTokenStorage) : option MultiTokenStorage :=
    let new_ledger := mint_update_balances param storage.(ledger) in
    do new_supply <- mint_update_total_supply param storage.(token_total_supply);
    let new_s := storage<|ledger := new_ledger|><|token_total_supply := new_supply|> in
    Some new_s.

Definition burn_update_balances (txs : list MintBurnTx) (ledger : Ledger) : option Ledger :=
    let burn := fun (l_opt : option Ledger) (tx : MintBurnTx) =>
        do l <- l_opt ;
        dec_balance tx.(mint_burn_owner) tx.(mint_burn_token_id) tx.(mint_burn_amount) l 
    in
    fold_left burn txs (Some ledger).

Definition burn_update_total_supply (txs : list MintBurnTx) (total_supplies : TokenTotalSupply) : option TokenTotalSupply :=
    let update := fun (supplies_opt : option TokenTotalSupply) (tx: MintBurnTx) =>
        do supplies <- supplies_opt ;    
        do ts <- FMap.find tx.(mint_burn_token_id) supplies ;
        do new_s <- sub ts tx.(mint_burn_amount) ;
        Some (FMap.update tx.(mint_burn_token_id) (Some new_s) supplies)
    in
    fold_left update txs (Some total_supplies).

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
    

Lemma mint_update_balances_app : forall (a : MintBurnTx) (l : list MintBurnTx) (total_supplies : TokenTotalSupply),
    mint_update_total_supply (a :: l) total_supplies =
    do total_supplies' <- mint_update_total_supply [a] total_supplies ;
    mint_update_total_supply l (total_supplies').
Proof.
    induction l. cbn in *.
    - cbn. intros. destruct (FMap.find (mint_burn_token_id a) total_supplies) eqn:E; now setoid_rewrite E.
    - cbn in *.
    
    
Qed.

End Token_Manager.
