Require Import Blockchain.
From ConCert.Examples Require Import FA2Interface.
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

Definition main (ctx : ContractCallContext) (param : MultiAssetParam) (s : MultiAssetStorage) : option Return :=
    match param with
    | Admin p => multi_token_admin_main ctx p s
    | Tokens p =>
        do _ <- fail_if_not_minter ctx s.(admin) ;
        do tpl <- token_manager p s.(assets) ;
        let new_s := s<| assets:= fst tpl |> in
        Some (new_s, snd tpl)
    | Assets p =>
        do _ <- fail_if_paused s.(admin) p ;
        do tpl <- fa2_main ctx p s.(assets) ;
        let new_s := s<| assets := fst tpl |> in
        Some (new_s, snd tpl)
    end.

Definition fa2_receive (chain : Chain) (ctx : ContractCallContext) (state: MultiAssetStorage) (msg_opt : option MultiAssetParam) : option Return :=
    do msg <- msg_opt ;
    main ctx msg state.    

Definition fa2_init (chain : Chain) (ctx: ContractCallContext) (setup: ((Address * Address) * ((list TokenMetadata) * N))) : option MultiAssetStorage :=
    let (t1,t2) := setup in
    let (admin, minter) := t1 in
    let (tokens, meta_data_uri) := t2 in
    let meta := FMap.update EmptyString (Some meta_data_uri) FMap.empty in
    let token_metadata := fold_right (fun (token_metadata : TokenMetadata) (acc : TokenMetaDataStorage) => FMap.update token_metadata.(tm_token_id) (Some token_metadata) acc) FMap.empty tokens in
    let supply := fold_right (fun (token_metadata : TokenMetadata) (acc : TokenTotalSupply) => FMap.update token_metadata.(tm_token_id) (Some 0) acc) FMap.empty tokens in
    Some ({|
        admin := {|
            tas_admin := admin ;
            tas_pending_admin := None ;
            tas_paused := FMap.empty ;
            tas_minter := minter
        |} ;
        assets := {|
            ledger := FMap.empty ;
            operators := FMap.empty ;
            token_metadata := token_metadata ;
            token_total_supply := supply
        |} ;
        metadata := meta
    |}).

(** The FA2 Contract **)
Definition FA2_contract : Contract ((Address * Address) * ((list TokenMetadata) * N)) MultiAssetParam MultiAssetStorage :=
    build_contract fa2_init fa2_receive.

(** Checks if the total supply stays the same after transfer **)
Lemma transfer_preserves_total_supply {prev_state next_state acts chain ctx transfers} :
    fa2_receive chain ctx prev_state (Some (Assets (FA2_Transfer transfers))) = Some (next_state, acts) ->
    prev_state.(assets).(token_total_supply) = next_state.(assets).(token_total_supply).
Proof.
    intros. contract_simpl fa2_receive fa2_init. reflexivity.
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
    acts = [act_call p.(bal_callback) 0 (serialize [{|request := req; balance:=(get_balance_amt (req.(owner), req.(bal_req_token_id)) state.(assets).(ledger)) |}])].
Proof.
    intros. contract_simpl fa2_receive fa2_init. rewrite H0 in H1. cbn in H1. destruct (FMap.find req_token_id (token_metadata (assets state))).
    - inversion H1. reflexivity.
    - discriminate.
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
    get_balance_amt (fromAddr, token_id) next_state.(assets).(ledger) = get_balance_amt (fromAddr, token_id) prev_state.(assets).(ledger) - amount /\
    get_balance_amt (toAddr, token_id) next_state.(assets).(ledger) = get_balance_amt (toAddr, token_id) prev_state.(assets).(ledger) + amount.
Proof.
    intros. contract_simpl fa2_receive fa2_init. split.
        - unfold get_balance_amt. 
            destruct (FMap.find (fromAddr, token_id) (ledger (assets prev_state))) eqn: E.
                * setoid_rewrite E. setoid_rewrite E. destruct (n-amount).
                    -- cbn. rewrite <- inc_balance_other_preservces_own; try easy. setoid_rewrite FMap.find_remove. easy.
                    -- cbn. rewrite <- inc_balance_other_preservces_own; try easy. setoid_rewrite FMap.find_add. easy.
                * setoid_rewrite E. setoid_rewrite E. cbn. rewrite <- inc_balance_other_preservces_own; try easy.
                setoid_rewrite FMap.find_remove. easy.
        - unfold get_balance_amt. destruct (FMap.find (fromAddr, token_id) (ledger (assets prev_state))) eqn: E;
            do 2 setoid_rewrite E.
            + destruct (n-amount).
                * unfold inc_balance. cbn. destruct (FMap.find (toAddr, token_id) (ledger (assets prev_state))) eqn: E1.
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
                * cbn. unfold inc_balance. cbn. destruct (FMap.find (toAddr, token_id) (ledger (assets prev_state))) eqn: E1.
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
            + unfold inc_balance. cbn. destruct (FMap.find (toAddr, token_id) (ledger (assets prev_state))) eqn: E1.
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
    get_balance_amt (fromAddr, token_id) next_state.(assets).(ledger) = get_balance_amt (fromAddr, token_id) prev_state.(assets).(ledger).
Proof.
    intros. contract_simpl fa2_receive fa2_init. unfold get_balance_amt. destruct (FMap.find (toAddr, token_id) (ledger (assets prev_state))) eqn: E;
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
Lemma mint_functionally_correct {chain ctx prev_state owner token_id amount next_state acts} :
    fa2_receive chain ctx prev_state (Some (Tokens (MintTokens [{|
        mint_burn_owner := owner ;
        mint_burn_token_id := token_id ;
        mint_burn_amount := amount
        |}]))) = Some (next_state, acts) ->
    do old_value <- FMap.find token_id (prev_state.(assets).(token_total_supply)) ;
        do v <- FMap.find token_id (next_state.(assets).(token_total_supply)) ;
        old_value + amount = v.


End FA2_Multi_Asset.