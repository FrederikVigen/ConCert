Require Import Blockchain.
From ConCert.Examples Require Import FA2Interface.
From ConCert.Utils Require Import Extras.
From ConCert.Execution Require Import InterContractCommunication.
Require Import FA2InterfaceOwn.
Require Import RecordUpdate.
Require Import ContractCommon.
Require Import FA2Types.
Require Import MultiTokenAdmin.
Require Import TokenAdmin.
Require Import FA2_Multi_Token.
Require Import Token_Manager.
Require Import Monads.
Require Import ZArith.
Require Import Containers.
Require Import String.
Require Import List.
Require Import Fees_Lib.
Require Import Serializable.
Require Import FA2_Operator_Lib.
Require Import FSets.
Require Import FMapList.
Require Import Psatz.
Require Import TokenAdmin.
Import ListNotations.


Section FA2_Multi_Asset.
Context {BaseTypes : ChainBase}.
Set Nonrecursive Elimination Schemes.

Inductive MultiAssetParam :=
| Assets (param : FA2EntryPoints)
| Admin (param : MultiTokenAdmin)
| Tokens (param : TokenManager).

Global Instance MultiAssetParam_serializable : Serializable MultiAssetParam :=
Derive Serializable MultiAssetParam_rect<Assets, Admin, Tokens>.

Record Setup := {
    admin_addr : Address;
    minter_addr : Address;
    tokens : list TokenMetadata;
    meta_data_uri : N
}.

Global Instance Setup_serializable : Serializable Setup :=
Derive Serializable Setup_rect<Build_Setup>.

Definition main (ctx : ContractCallContext) (param : MultiAssetParam) (s : MultiAssetStorage) : option Return :=
    match param with
    | Admin p => multi_token_admin_main ctx p s
    | Tokens p =>
        do _ <- fail_if_not_minter ctx s.(fa2_admin) ;
        do tpl <- token_manager p s.(fa2_assets) ;
        let new_s := s<| fa2_assets:= fst tpl |> in
        Some (new_s, snd tpl)
    | Assets p =>
        do _ <- fail_if_paused s.(fa2_admin) p ;
        do tpl <- fa2_main ctx p s.(fa2_assets) ;
        let new_s := s<| fa2_assets := fst tpl |> in
        Some (new_s, snd tpl)
    end.

Definition fa2_receive (chain : Chain) (ctx : ContractCallContext) (state: MultiAssetStorage) (msg_opt : option MultiAssetParam) : option Return :=
    do msg <- msg_opt ;
    main ctx msg state.    


Definition fa2_init (chain : Chain) (ctx: ContractCallContext) (setup: Setup) : option MultiAssetStorage :=
    let admin := setup.(admin_addr) in
    let minter := setup.(minter_addr) in
    let tokens := setup.(tokens) in
    let meta_data_uri := setup.(meta_data_uri) in
    let meta := FMap.update EmptyString (Some meta_data_uri) FMap.empty in
    let token_metadata := fold_right (fun (token_metadata : TokenMetadata) (acc : TokenMetaDataStorage) => FMap.update token_metadata.(tm_token_id) (Some token_metadata) acc) FMap.empty tokens in
    let supply := fold_right (fun (token_metadata : TokenMetadata) (acc : TokenTotalSupply) => FMap.update token_metadata.(tm_token_id) (Some 0) acc) FMap.empty tokens in
    Some ({|
        fa2_admin := {|
            tas_admin := admin ;
            tas_pending_admin := None ;
            tas_paused := FMap.empty ;
            tas_minter := minter
        |} ;
        fa2_assets := {|
            ledger := FMap.empty ;
            operators := FMap.empty ;
            token_metadata := token_metadata ;
            token_total_supply := supply
        |} ;
        metadata := meta
    |}).

(** The FA2 Contract **)
Definition FA2_contract : Contract Setup MultiAssetParam MultiAssetStorage :=
    build_contract fa2_init fa2_receive.

(**----------------- Admin Proofs -----------------**)

Lemma create_token_creates_new_token {ctx chain prev_state next_state token_id token_info tMetaData} :
    tMetaData = {|
        tm_token_id := token_id ;
        tm_token_info := token_info
    |} ->
    fa2_receive chain ctx prev_state (Some (Admin (Create_token tMetaData))) = Some (next_state, []) ->
    FMap.find token_id next_state.(fa2_assets).(token_metadata) = Some tMetaData.
Proof.
    intros. contract_simpl fa2_receive fa2_init. unfold create_token in H1. cbn in H1.
    destruct (FMap.find token_id (token_metadata (fa2_assets prev_state))) in H1; try easy.
    inversion H1. cbn. setoid_rewrite FMap.find_add. reflexivity.
Qed.

Lemma set_new_admin_functionally_correct {ctx chain prev_state next_state new_admin} :
    fa2_receive chain ctx prev_state (Some (Admin (Token_admin (Set_admin new_admin)))) = Some (next_state, []) ->
    next_state.(fa2_admin).(tas_pending_admin) = Some new_admin.
Proof.
    intros. contract_simpl fa2_receive fa2_init. easy.
Qed.


Lemma set_new_minter_functionally_correct {ctx chain prev_state next_state new_minter} :
    fa2_receive chain ctx prev_state (Some (Admin (Token_admin (Set_minter new_minter)))) = Some (next_state, []) ->
    next_state.(fa2_admin).(tas_minter) = new_minter.
Proof.
    intros. contract_simpl fa2_receive fa2_init. easy.
Qed.

Lemma confirm_admin_functionally_correct {ctx chain prev_state next_state} :
    fa2_receive chain ctx prev_state (Some (Admin (Token_admin (Confirm_admin)))) = Some (next_state, []) ->
    next_state.(fa2_admin).(tas_pending_admin) = None /\ next_state.(fa2_admin).(tas_admin) = ctx.(ctx_from).
Proof.
    intros. contract_simpl fa2_receive fa2_init. unfold confirm_new_admin in H. 
    destruct (tas_pending_admin (fa2_admin prev_state)); try easy.
    destruct (address_eqb ctx.(ctx_from) a) in H; try easy.
    inversion H. easy.
Qed.

Lemma pause_functionally_correct {ctx chain prev_state next_state tokens token_id} :
    tokens = [{|
        pp_token_id := token_id;
        pp_paused := true
    |}] ->
    fa2_receive chain ctx prev_state (Some (Admin (Token_admin (Pause tokens)))) = Some (next_state, []) ->
    FMap.find token_id next_state.(fa2_admin).(tas_paused) = Some tt.
Proof.
    intros. contract_simpl fa2_receive fa2_init.
    cbn. apply FMap.find_add.
Qed.

Lemma unpause_functionally_correct {ctx chain prev_state next_state tokens token_id} :
    tokens = [{|
        pp_token_id := token_id;
        pp_paused := false
    |}] ->
    fa2_receive chain ctx prev_state (Some (Admin (Token_admin (Pause tokens)))) = Some (next_state, []) ->
    FMap.find token_id next_state.(fa2_admin).(tas_paused) = None.
Proof.
    intros. contract_simpl fa2_receive fa2_init.
    cbn. apply FMap.find_remove.
Qed.

(**----------------- Assets Proofs -----------------**)
Lemma balance_of_callbacks_with_balance_of {p chain ctx state req_addr req_token_id req acts} :
    req = 
    {|
        owner := req_addr ;
        bal_req_token_id := req_token_id
    |} ->
    p.(bal_requests) = [req] ->
    fa2_receive chain ctx state (Some (Assets (Balance_of (p)))) = Some (state, acts) ->
    acts = [act_call p.(bal_callback) 0 (serialize [{|request := req; balance:=(get_balance_amt (req.(owner), req.(bal_req_token_id)) state.(fa2_assets).(ledger)) |}])].
Proof.
    intros. contract_simpl fa2_receive fa2_init. rewrite H0 in H1. cbn in H1. destruct (FMap.find req_token_id (token_metadata (fa2_assets state))).
    - inversion H1. reflexivity.
    - discriminate.
Qed.

(** Checks if the total supply stays the same after transfer **)
Lemma transfer_preserves_total_supply {prev_state next_state acts chain ctx transfers} :
    fa2_receive chain ctx prev_state (Some (Assets (FA2_Transfer transfers))) = Some (next_state, acts) ->
    prev_state.(fa2_assets).(token_total_supply) = next_state.(fa2_assets).(token_total_supply).
Proof.
    intros. contract_simpl fa2_receive fa2_init. reflexivity.
Qed. 

(** If inc_balance on other addr own_addr balance does not change **)
Lemma inc_balance_other_preservces_own {x y ledger amount token_id' token_id} :
    x <> y ->
    FMap.find (x, token_id') ledger = FMap.find (x, token_id') (inc_balance y token_id amount ledger).
Proof.
    intros. unfold inc_balance. destruct (get_balance_amt (y, token_id) ledger + amount =? 0).
    - setoid_rewrite FMap.find_remove_ne; try easy.
    - cbn. setoid_rewrite FMap.find_add_ne; try easy.
Qed. 

(**Check if transfer actually moves assets from one user to another**)
Lemma transfer_is_functionally_correct {chain ctx prev_state next_state acts fromAddr toAddr amount token_id} :
    fromAddr <> toAddr ->
    fa2_receive chain ctx prev_state (Some (Assets (FA2_Transfer [{|
        from_ := fromAddr ;
        txs := [{|
            to_ := toAddr ;
            dst_token_id := token_id ;
            amount := amount
        |}]
    |}]))) = Some (next_state, acts) ->
    get_balance_amt (fromAddr, token_id) next_state.(fa2_assets).(ledger) = get_balance_amt (fromAddr, token_id) prev_state.(fa2_assets).(ledger) - amount /\
    get_balance_amt (toAddr, token_id) next_state.(fa2_assets).(ledger) = get_balance_amt (toAddr, token_id) prev_state.(fa2_assets).(ledger) + amount.
Proof.
    intros. contract_simpl fa2_receive fa2_init. split.
    - unfold get_balance_amt. 
        destruct (FMap.find (fromAddr, token_id) (ledger (fa2_assets prev_state))) eqn: E.
            * setoid_rewrite E. setoid_rewrite E. destruct (n-amount).
                -- cbn. rewrite <- inc_balance_other_preservces_own; try easy. setoid_rewrite FMap.find_remove. easy.
                -- cbn. rewrite <- inc_balance_other_preservces_own; try easy. setoid_rewrite FMap.find_add. easy.
            * setoid_rewrite E. setoid_rewrite E. cbn. rewrite <- inc_balance_other_preservces_own; try easy.
            setoid_rewrite FMap.find_remove. easy.
    - unfold get_balance_amt. destruct (FMap.find (fromAddr, token_id) (ledger (fa2_assets prev_state))) eqn: E;
        do 2 setoid_rewrite E.
        + destruct (n-amount).
            * unfold inc_balance. cbn. destruct (FMap.find (toAddr, token_id) (ledger (fa2_assets prev_state))) eqn: E1.
                -- unfold get_balance_amt. setoid_rewrite FMap.find_remove_ne; try easy. setoid_rewrite E1.
                    destruct (n0+amount) eqn: E2.
                    --- cbn. setoid_rewrite FMap.find_remove. easy.
                    --- cbn. setoid_rewrite FMap.find_add. setoid_rewrite FMap.find_remove_ne; try easy.
                        setoid_rewrite E1. assumption.
                -- unfold get_balance_amt. setoid_rewrite FMap.find_remove_ne; try easy. setoid_rewrite E1.
                    destruct (0+amount) eqn: E2.
                    --- cbn. setoid_rewrite FMap.find_remove. easy.
                    --- cbn. setoid_rewrite FMap.find_add. setoid_rewrite FMap.find_remove_ne; try easy.
                        setoid_rewrite E1. assumption.
            * cbn. unfold inc_balance. cbn. destruct (FMap.find (toAddr, token_id) (ledger (fa2_assets prev_state))) eqn: E1.
                -- unfold get_balance_amt. setoid_rewrite FMap.find_add_ne; try easy. setoid_rewrite E1.
                    destruct (n0+amount) eqn: E2.
                    --- cbn. setoid_rewrite FMap.find_remove. easy.
                    --- cbn. setoid_rewrite FMap.find_add. setoid_rewrite FMap.find_add_ne; try easy.
                        setoid_rewrite E1. assumption.
                -- unfold get_balance_amt. setoid_rewrite FMap.find_add_ne; try easy. setoid_rewrite E1.
                    destruct (0+amount) eqn: E2.
                    --- cbn. setoid_rewrite FMap.find_remove. easy.
                    --- cbn. setoid_rewrite FMap.find_add. setoid_rewrite FMap.find_add_ne; try easy.
                        setoid_rewrite E1. assumption.
        + unfold inc_balance. cbn. destruct (FMap.find (toAddr, token_id) (ledger (fa2_assets prev_state))) eqn: E1.
            * unfold get_balance_amt. setoid_rewrite FMap.find_remove_ne; try easy. setoid_rewrite FMap.find_remove_ne; try easy.
                setoid_rewrite E1. destruct (n + amount) eqn: E2.
                -- cbn. setoid_rewrite FMap.find_remove. easy.
                -- cbn. setoid_rewrite FMap.find_add. setoid_rewrite E1. assumption.
            * unfold get_balance_amt. setoid_rewrite FMap.find_remove_ne; try easy. setoid_rewrite FMap.find_remove_ne; try easy.
                setoid_rewrite E1. destruct (0 + amount) eqn: E2.
                -- cbn. setoid_rewrite FMap.find_remove. easy.
                -- cbn. setoid_rewrite FMap.find_add. setoid_rewrite E1. assumption.
Qed.

(** Check that transfer to selv changes nothing **)
Lemma transfer_to_self_changes_nothing {chain ctx prev_state next_state acts fromAddr toAddr amount token_id} :
    fromAddr = toAddr ->
    fa2_receive chain ctx prev_state (Some (Assets (FA2_Transfer [{|
        from_ := fromAddr ;
        txs := [{|
            to_ := toAddr ;
            dst_token_id := token_id ;
            amount := amount
        |}]
    |}]))) = Some (next_state, acts) ->
    get_balance_amt (fromAddr, token_id) next_state.(fa2_assets).(ledger) = get_balance_amt (fromAddr, token_id) prev_state.(fa2_assets).(ledger).
Proof.
    intros. contract_simpl fa2_receive fa2_init. unfold get_balance_amt. destruct (FMap.find (toAddr, token_id) (ledger (fa2_assets prev_state))) eqn: E;
    do 2 setoid_rewrite E.
    - unfold get_balance_amt in H3. setoid_rewrite E in H3. destruct (n-amount) eqn: E2; cbn.
        + unfold inc_balance. unfold get_balance_amt. setoid_rewrite FMap.find_remove. setoid_rewrite FMap.find_remove.
            cbn. destruct (0+amount) eqn: E3; cbn.
            * setoid_rewrite FMap.find_remove. rewrite <- E2 in E3. easy.
            * setoid_rewrite FMap.find_add. apply N.ltb_ge in H3. destruct n; easy.
        + unfold inc_balance. unfold get_balance_amt. setoid_rewrite FMap.find_add.
            setoid_rewrite FMap.find_add. destruct (N.pos p + amount) eqn: E3; cbn.
            * setoid_rewrite FMap.find_remove. easy.
            * setoid_rewrite FMap.find_add. easy.
    - unfold inc_balance. cbn. unfold get_balance_amt. setoid_rewrite FMap.find_remove. setoid_rewrite FMap.find_remove.
        destruct (0 + amount) eqn: E2; cbn.
        + setoid_rewrite FMap.find_remove; easy.
        + setoid_rewrite FMap.find_add. unfold get_balance_amt in H3. setoid_rewrite E in H3. 
            apply N.ltb_ge in H3. easy.
Qed.

(**----------------- TokenManager Proofs -----------------**)
Lemma mint_functionally_correct {chain ctx prev_state owner token_id amount next_state acts old_value v} :
    fa2_receive chain ctx prev_state (Some (Tokens (MintTokens [{|
        mint_burn_owner := owner ;
        mint_burn_token_id := token_id ;
        mint_burn_amount := amount
        |}]))) = Some (next_state, acts) ->
    FMap.find token_id (prev_state.(fa2_assets).(token_total_supply)) = Some old_value ->
    FMap.find token_id (next_state.(fa2_assets).(token_total_supply)) = Some v -> 
    old_value + amount = v /\
    get_balance_amt (owner, token_id) prev_state.(fa2_assets).(ledger) + amount = get_balance_amt (owner, token_id) next_state.(fa2_assets).(ledger).
Proof.
    intros. cbn in H. contract_simpl fa2_receive fa2_init. cbn in H1. split.
    - setoid_rewrite FMap.find_add in H1. setoid_rewrite H0 in H. inversion H1. easy.
    - unfold inc_balance. cbn. destruct (get_balance_amt (owner, token_id) (ledger (fa2_assets prev_state)) + amount) eqn: E; 
        cbn; unfold get_balance_amt.
        + setoid_rewrite FMap.find_remove. easy.
        + setoid_rewrite FMap.find_add. easy.
Qed.

Lemma burn_functionally_correct {chain ctx prev_state owner token_id amount next_state acts old_value v} :
    fa2_receive chain ctx prev_state (Some (Tokens (BurnTokens [{|
        mint_burn_owner := owner ;
        mint_burn_token_id := token_id ;
        mint_burn_amount := amount
        |}]))) = Some (next_state, acts) ->
    FMap.find token_id (prev_state.(fa2_assets).(token_total_supply)) = Some old_value ->
    FMap.find token_id (next_state.(fa2_assets).(token_total_supply)) = Some v -> 
    old_value - amount = v /\
    get_balance_amt (owner, token_id) prev_state.(fa2_assets).(ledger) - amount = get_balance_amt (owner, token_id) next_state.(fa2_assets).(ledger).
Proof.
    intros. cbn in H. contract_simpl fa2_receive fa2_init. cbn in H1. split.
    - setoid_rewrite FMap.find_add in H1. setoid_rewrite H0 in H. inversion H1. easy.
    - unfold inc_balance. cbn. destruct (get_balance_amt (owner, token_id) (ledger (fa2_assets prev_state)) - amount) eqn: E; 
        cbn; unfold get_balance_amt.
        + setoid_rewrite FMap.find_remove. easy.
        + setoid_rewrite FMap.find_add. easy.
Qed.

Lemma only_minter_can_burn {chain ctx prev_state burnList} :
    (ctx.(ctx_from) =? prev_state.(fa2_admin).(tas_minter))%address = false ->
    fa2_receive chain ctx prev_state (Some (Tokens (BurnTokens burnList))) = None.
Proof.
    intros. contract_simpl fa2_receive fa2_init. unfold fail_if_not_minter. rewrite H. reflexivity.
Qed.

Lemma cant_burn_more_than_supply {chain ctx prev_state owner token_id amount v} :
    FMap.find token_id (prev_state.(fa2_assets).(token_total_supply)) = Some v -> 
    v < amount ->
    fa2_receive chain ctx prev_state (Some (Tokens (BurnTokens [{|
    mint_burn_owner := owner ;
    mint_burn_token_id := token_id ;
    mint_burn_amount := amount
    |}]))) = None.
Proof.
    intros. contract_simpl fa2_receive fa2_init. unfold fail_if_not_minter. destruct address_eqb; try easy.
    destruct (get_balance_amt (owner, token_id) (ledger (fa2_assets prev_state)) <? amount); try easy. cbn.
    setoid_rewrite H. destruct (v <? amount) eqn: E; try easy. rewrite N.ltb_ge in E. easy.
Qed.

(**----------------- FA2_Multi_Asset -----------------**)
Definition sum_tx (txs : list MintBurnTx) (id : token_id): Z :=
    fold_right 
    (fun (tx : MintBurnTx) (acc : Z) => 
        (
            if tx.(mint_burn_token_id) =? id
            then (acc + (Z.of_N tx.(mint_burn_amount)))%Z
            else 0%Z
        )
        )
    0%Z txs.

Definition mint_or_burn (id : token_id) (msg : option MultiAssetParam) : Z :=
    match msg with
    | Some m =>
        match m with
        | Tokens (param) =>
            match param with 
            | MintTokens mint_param => sum_tx mint_param id
            | BurnTokens mint_param => (sum_tx mint_param id) * (-1)
            end
        | _ => 0
        end
    | _ => 0
    end.

Lemma init_total_supply_correct {chain ctx setup state fa2_token_id total_supply} :
    FMap.find fa2_token_id state.(fa2_assets).(token_total_supply) = Some total_supply ->
    fa2_init chain ctx setup = Some state ->
    total_supply = 0.
Proof.
    intros. contract_simpl fa2_receive fa2_init. induction tokens.
    - cbn in H. setoid_rewrite FMap.find_empty in H. inversion H.
    - cbn in *. destruct (fa2_token_id =? (tm_token_id a)) eqn:E.
        + rewrite N.eqb_eq in E. rewrite E in H. setoid_rewrite FMap.find_add in H. inversion H. reflexivity.
        + rewrite N.eqb_neq in E. setoid_rewrite FMap.find_add_ne in H; try easy.
Qed.


Lemma assets_endpoint_does_not_change_minter {prev_state next_state acts chain ctx param} :
    fa2_receive chain ctx prev_state (Some (Assets param)) = Some (next_state, acts) ->
    prev_state.(fa2_admin).(tas_minter) = next_state.(fa2_admin).(tas_minter).
Proof.
    intros; now contract_simpl fa2_receive fa2_init.
Qed. 

Lemma balance_of_preserves_total_supply {prev_state next_state acts chain ctx param} :
    fa2_receive chain ctx prev_state (Some (Assets (Balance_of (param)))) = Some (next_state, acts) ->
    prev_state.(fa2_assets).(token_total_supply) = next_state.(fa2_assets).(token_total_supply).
Proof.
    intros. contract_simpl fa2_receive fa2_init.
Qed. 

Lemma update_operators_preserves_total_supply {prev_state next_state acts chain ctx param} :
    fa2_receive chain ctx prev_state (Some (Assets (Update_operators (param)))) = Some (next_state, acts) ->
    prev_state.(fa2_assets).(token_total_supply) = next_state.(fa2_assets).(token_total_supply).
Proof.
    intros. contract_simpl fa2_receive fa2_init.
Qed. 

Lemma assets_endpoint_preserves_total_supply {prev_state next_state acts chain ctx param} :
    fa2_receive chain ctx prev_state (Some (Assets param)) = Some (next_state, acts) ->
    prev_state.(fa2_assets).(token_total_supply) = next_state.(fa2_assets).(token_total_supply).
Proof.
    intros. contract_simpl fa2_receive fa2_init. destruct param.
    - inversion H1. destruct (transfer ctx transfers default_operator_validator (fa2_assets prev_state)) in H2.
     now inversion H2.

Qed. 

Lemma set_admin_preserves_total_supply {prev_state next_state acts chain ctx addr} :
    fa2_receive chain ctx prev_state (Some (Admin (Token_admin (Set_admin addr)))) = Some (next_state, acts) ->
    prev_state.(fa2_assets).(token_total_supply) = next_state.(fa2_assets).(token_total_supply).
Proof.
    intros. contract_simpl fa2_receive fa2_init.
Qed.

Lemma set_admin_does_not_change_minter {prev_state next_state chain ctx addr acts} :
    fa2_receive chain ctx prev_state (Some (Admin (Token_admin (Set_admin addr)))) = Some (next_state, acts) ->
    prev_state.(fa2_admin).(tas_minter) = next_state.(fa2_admin).(tas_minter).
Proof.
    intros. contract_simpl fa2_receive fa2_init. unfold set_admin.
    cbn. unfold fail_if_not_admin in H. destruct_address_eq; try easy.
Qed. 

Lemma fa2_correct : forall bstate caddr fa2_token_id total_supply (trace: ChainTrace empty_state bstate),
    env_contracts bstate caddr = Some (FA2_contract : WeakContract) ->
    exists cstate depinfo inc_calls,
        contract_state bstate caddr = Some cstate /\
        deployment_info Setup trace caddr = Some depinfo /\
        incoming_calls MultiAssetParam trace caddr = Some inc_calls /\
        (
        FMap.find fa2_token_id cstate.(fa2_assets).(token_total_supply) = Some total_supply ->
        sumZ (fun callInfo => mint_or_burn fa2_token_id callInfo.(call_msg)) (filter (callFrom cstate.(fa2_admin).(tas_minter)) inc_calls) = Z.of_N total_supply
        ).
Proof.
    contract_induction;
    intros; auto.
    - intros. cbn in *. eapply init_total_supply_correct in init_some; now eauto.
    - unfold callFrom. unfold receive in receive_some. simpl in *. destruct msg; try easy. destruct m. destruct param. 
        + erewrite <- transfer_preserves_total_supply in H; eauto. erewrite <- assets_endpoint_does_not_change_minter; eauto.
        destruct_address_eq; now apply IH.
        + erewrite <- balance_of_preserves_total_supply in H; eauto. erewrite <- assets_endpoint_does_not_change_minter; eauto.
        destruct_address_eq; now apply IH.
        + erewrite <- update_operators_preserves_total_supply in H; eauto. erewrite <- assets_endpoint_does_not_change_minter; eauto.  
        destruct_address_eq; now apply IH.
        + destruct param. destruct tokenAdmin.
            -- erewrite <- set_admin_preserves_total_supply in H; eauto. erewrite <- set_admin_does_not_change_minter; eauto.
            destruct_address_eq; now apply IH.
            -- 
End FA2_Multi_Asset.