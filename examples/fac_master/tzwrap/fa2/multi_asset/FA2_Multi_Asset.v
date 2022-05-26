Require Import Blockchain.
From ConCert.Examples Require Import FA2Interface.
From ConCert.Utils Require Import Extras.
From ConCert.Execution Require Import InterContractCommunication.
Require Import Automation.
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

Lemma assets_endpoint_preserves_total_supply {prev_state next_state acts chain ctx param} :
    fa2_receive chain ctx prev_state (Some (Assets param)) = Some (next_state, acts) ->
    prev_state.(fa2_assets).(token_total_supply) = next_state.(fa2_assets).(token_total_supply).
Proof.
    intros. contract_simpl fa2_receive fa2_init. destruct param.
    - inversion H1; destruct (transfer ctx transfers default_operator_validator (fa2_assets prev_state)) in H2; try easy; now inversion H2.
    - inversion H1; destruct (get_balance balanceOf (ledger (fa2_assets prev_state)) (token_metadata (fa2_assets prev_state))) in H2; try easy; now inversion H2.
    - inversion H1; destruct (fa2_update_operators ctx updates (operators (fa2_assets prev_state))) in H2; try easy; now inversion H2.
Qed. 

Lemma assets_endpoint_preserves_metadata {prev_state next_state acts chain ctx param} :
    fa2_receive chain ctx prev_state (Some (Assets param)) = Some (next_state, acts) ->
    prev_state.(fa2_assets).(token_metadata) = next_state.(fa2_assets).(token_metadata).
Proof.
    intros. contract_simpl fa2_receive fa2_init. destruct param.
    - inversion H1; destruct (transfer ctx transfers default_operator_validator (fa2_assets prev_state)) in H2; try easy; now inversion H2.
    - inversion H1; destruct (get_balance balanceOf (ledger (fa2_assets prev_state)) (token_metadata (fa2_assets prev_state))) in H2; try easy; now inversion H2.
    - inversion H1; destruct (fa2_update_operators ctx updates (operators (fa2_assets prev_state))) in H2; try easy; now inversion H2.
Qed.

Lemma token_metadata_always_same {prev_state next_state acts chain ctx param fa2_token_id metadata} :
    FMap.find fa2_token_id prev_state.(fa2_assets).(token_metadata) = Some metadata ->
    fa2_receive chain ctx prev_state (Some (Admin param)) = Some (next_state, acts) ->
    FMap.find fa2_token_id prev_state.(fa2_assets).(token_metadata) = FMap.find fa2_token_id next_state.(fa2_assets).(token_metadata).
Proof.
    intros. destruct param. destruct tokenAdmin;
    try contract_simpl fa2_receive fa2_init.
    contract_simpl fa2_receive fa2_init. unfold create_token in H1.
    destruct (FMap.find (tm_token_id tokenMetaData) (token_metadata (fa2_assets prev_state))) eqn:E; try easy.
    inversion H1. now setoid_rewrite FMap.find_add_ne.
Qed.

Lemma token_admin_endpoint_preserves_total_supply {prev_state next_state acts chain ctx param fa2_token_id supply metadata} :
    FMap.find fa2_token_id prev_state.(fa2_assets).(token_total_supply) = Some supply ->
    FMap.find fa2_token_id prev_state.(fa2_assets).(token_metadata) = Some metadata ->
    fa2_receive chain ctx prev_state (Some (Admin param)) = Some (next_state, acts) ->
    FMap.find fa2_token_id prev_state.(fa2_assets).(token_total_supply) = FMap.find fa2_token_id next_state.(fa2_assets).(token_total_supply).
Proof.
    intros. destruct param. destruct tokenAdmin;
    try contract_simpl fa2_receive fa2_init.
    contract_simpl fa2_receive fa2_init. unfold create_token in H2.
    destruct (FMap.find (tm_token_id tokenMetaData) (token_metadata (fa2_assets prev_state))) eqn:E; try easy.
    inversion H2; setoid_rewrite FMap.find_add_ne; easy.
Qed.

Lemma token_admin_endpoint_preserves_metadata {prev_state next_state acts chain ctx param fa2_token_id supply metadata} :
    FMap.find fa2_token_id prev_state.(fa2_assets).(token_total_supply) = Some supply ->
    FMap.find fa2_token_id prev_state.(fa2_assets).(token_metadata) = Some metadata ->
    fa2_receive chain ctx prev_state (Some (Admin param)) = Some (next_state, acts) ->
    FMap.find fa2_token_id prev_state.(fa2_assets).(token_metadata) = FMap.find fa2_token_id next_state.(fa2_assets).(token_metadata).
Proof.
    intros. destruct param. destruct tokenAdmin;
    try contract_simpl fa2_receive fa2_init.
    contract_simpl fa2_receive fa2_init. unfold create_token in H2.
    destruct (FMap.find (tm_token_id tokenMetaData) (token_metadata (fa2_assets prev_state))) eqn: E; try easy.
    inversion H2; setoid_rewrite FMap.find_add_ne; easy.  
Qed.

Lemma create_new_token_changes_nothing_else {prev_state next_state acts chain ctx fa2_token_id new_token_id info_map} :
    new_token_id <> fa2_token_id ->
    let new_token_metadata := {|
        tm_token_id := new_token_id ;
        tm_token_info := info_map 
    |} in
    fa2_receive chain ctx prev_state (Some (Admin (Create_token new_token_metadata))) = Some (next_state, acts) ->
    FMap.find fa2_token_id prev_state.(fa2_assets).(token_total_supply) = FMap.find fa2_token_id next_state.(fa2_assets).(token_total_supply) /\
    FMap.find fa2_token_id prev_state.(fa2_assets).(token_metadata) = FMap.find fa2_token_id next_state.(fa2_assets).(token_metadata).
Proof.
    intros. split. 
    - contract_simpl fa2_receive fa2_init. unfold create_token in H1.
    destruct (FMap.find (tm_token_id new_token_metadata) (token_metadata (fa2_assets prev_state))) eqn:E; try easy.
    inversion H1. now setoid_rewrite FMap.find_add_ne.
    - contract_simpl fa2_receive fa2_init. unfold create_token in H1.
    destruct (FMap.find (tm_token_id new_token_metadata) (token_metadata (fa2_assets prev_state))) eqn:E; try easy.
    inversion H1. now setoid_rewrite FMap.find_add_ne.
Qed.

(* If a new token is created the total supply of that token should be 0 *)
Lemma create_new_token_means_zero_supply {prev_state next_state acts chain ctx fa2_token_id info_map} :
    let new_token_metadata := {|
        tm_token_id := fa2_token_id ;
        tm_token_info := info_map 
    |} in
    fa2_receive chain ctx prev_state (Some (Admin (Create_token new_token_metadata))) = Some (next_state, acts) ->
    FMap.find fa2_token_id next_state.(fa2_assets).(token_total_supply) = Some 0.
Proof.
    intros. contract_simpl fa2_receive fa2_init.
    unfold create_token in H0. destruct (FMap.find (tm_token_id new_token_metadata) (token_metadata (fa2_assets prev_state))) eqn:E; try easy.
    inversion H0. now setoid_rewrite FMap.find_add.
Qed.

(* If a new token is created the total supply of that token should be 0 *)
Lemma create_new_token_means_zero_supply_2 {prev_state next_state acts chain ctx fa2_token_id info_map} :
    let new_token_metadata := {|
        tm_token_id := fa2_token_id ;
        tm_token_info := info_map 
    |} in
    fa2_receive chain ctx prev_state (Some (Admin (Create_token new_token_metadata))) = Some (next_state, acts) ->
    FMap.find fa2_token_id prev_state.(fa2_assets).(token_metadata) = None.
Proof.
    intros. contract_simpl fa2_receive fa2_init.
    unfold create_token in H0. destruct (FMap.find (tm_token_id new_token_metadata) (token_metadata (fa2_assets prev_state))) eqn:E. easy.
    easy.
Qed.

Lemma set_admin_preserves_total_supply {prev_state next_state chain ctx addr acts} :
    fa2_receive chain ctx prev_state (Some (Admin (Token_admin (Set_admin addr)))) = Some (next_state, acts) ->
    prev_state.(fa2_assets).(token_total_supply) = next_state.(fa2_assets).(token_total_supply).
Proof.
    intros. contract_simpl fa2_receive fa2_init.
Qed. 

Lemma confirm_admin_preserves_total_supply {prev_state next_state chain ctx acts} :
    fa2_receive chain ctx prev_state (Some (Admin (Token_admin Confirm_admin))) = Some (next_state, acts) ->
    prev_state.(fa2_assets).(token_total_supply) = next_state.(fa2_assets).(token_total_supply).
Proof.
    intros. contract_simpl fa2_receive fa2_init.
Qed. 

Lemma pause_preserves_total_supply {prev_state next_state chain ctx acts param} :
    fa2_receive chain ctx prev_state (Some (Admin (Token_admin (Pause param)))) = Some (next_state, acts) ->
    prev_state.(fa2_assets).(token_total_supply) = next_state.(fa2_assets).(token_total_supply).
Proof.
    intros. contract_simpl fa2_receive fa2_init.
Qed.

Lemma set_minter_preserves_total_supply {prev_state next_state chain ctx acts addr} :
    fa2_receive chain ctx prev_state (Some (Admin (Token_admin (Set_minter addr)))) = Some (next_state, acts) ->
    prev_state.(fa2_assets).(token_total_supply) = next_state.(fa2_assets).(token_total_supply).
Proof.
    intros. contract_simpl fa2_receive fa2_init.
Qed. 

Lemma set_admin_preserves_metadata {prev_state next_state chain ctx addr acts} :
    fa2_receive chain ctx prev_state (Some (Admin (Token_admin (Set_admin addr)))) = Some (next_state, acts) ->
    prev_state.(fa2_assets).(token_metadata) = next_state.(fa2_assets).(token_metadata).
Proof.
    intros. contract_simpl fa2_receive fa2_init.
Qed. 

Lemma confirm_admin_preserves_metadata {prev_state next_state chain ctx acts} :
    fa2_receive chain ctx prev_state (Some (Admin (Token_admin Confirm_admin))) = Some (next_state, acts) ->
    prev_state.(fa2_assets).(token_metadata) = next_state.(fa2_assets).(token_metadata).
Proof.
    intros. contract_simpl fa2_receive fa2_init.
Qed. 

Lemma pause_preserves_metadata {prev_state next_state chain ctx acts param} :
    fa2_receive chain ctx prev_state (Some (Admin (Token_admin (Pause param)))) = Some (next_state, acts) ->
    prev_state.(fa2_assets).(token_metadata) = next_state.(fa2_assets).(token_metadata).
Proof.
    intros. contract_simpl fa2_receive fa2_init.
Qed. 

Lemma set_minter_preserves_metadata {prev_state next_state chain ctx acts addr} :
    fa2_receive chain ctx prev_state (Some (Admin (Token_admin (Set_minter addr)))) = Some (next_state, acts) ->
    prev_state.(fa2_assets).(token_metadata) = next_state.(fa2_assets).(token_metadata).
Proof.
    intros. contract_simpl fa2_receive fa2_init.
Qed. 

Lemma empty_mint_preserves_total_supply {prev_state next_state chain ctx acts} :
    fa2_receive chain ctx prev_state (Some (Tokens (MintTokens []))) = Some (next_state, acts) ->
    prev_state.(fa2_assets).(token_total_supply) = next_state.(fa2_assets).(token_total_supply).
Proof.
    intros. contract_simpl fa2_receive fa2_init. easy.
Qed.

Lemma update_none_is_none {txs} :
let update := fun (supplies_opt : option TokenTotalSupply) (tx : MintBurnTx) =>
        do supplies <- supplies_opt ;
        do ts <- FMap.find tx.(mint_burn_token_id) supplies ;
        let new_s := ts + tx.(mint_burn_amount) in
        Some (FMap.update tx.(mint_burn_token_id) (Some new_s) supplies)
    in
    fold_left update txs None = None.
Proof.
    intros. induction txs.
    - cbn. easy.
    - cbn. easy.
Qed.

Lemma update_app {txs ts a} :
    let update := fun (supplies_opt : option TokenTotalSupply) (tx : MintBurnTx) =>
        do supplies <- supplies_opt ;
        do ts <- FMap.find tx.(mint_burn_token_id) supplies ;
        let new_s := ts + tx.(mint_burn_amount) in
        Some (FMap.update tx.(mint_burn_token_id) (Some new_s) supplies)
    in
    fold_left update (a :: txs) ts =
    fold_left update txs (update ts a).
Proof.
    intros. cbn in *. induction txs.
    - cbn. easy.
    - destruct ts; try easy.
Qed.

Lemma update_app2 : forall (update : option TokenTotalSupply -> MintBurnTx -> option TokenTotalSupply) txs ts a,
    fold_left update (a :: txs) ts =
    fold_left update txs (update ts a).
Proof.
    intros. cbn in *. induction txs.
    - cbn. easy.
    - destruct ts; try easy.
Qed.

Lemma update_comm : forall txs t a1 a2,
    let update := fun (supplies_opt : option TokenTotalSupply) (tx : MintBurnTx) =>
        do supplies <- supplies_opt ;
        do ts <- FMap.find tx.(mint_burn_token_id) supplies ;
        let new_s := ts + tx.(mint_burn_amount) in
        Some (FMap.update tx.(mint_burn_token_id) (Some new_s) supplies)
    in
    fold_left update txs (update (update t a1) a2) =
    fold_left update txs (update (update t a2) a1).
Proof.
    intros.
    destruct t eqn:T; try easy. rename t0 into ts. 
    setoid_rewrite <- (update_app2 update [] (update (Some ts) a1) a2). 
    setoid_rewrite <- (update_app2 update [a2] (Some ts) a1).
    setoid_rewrite <- (update_app2 update [] (update (Some ts) a2) a1). 
    setoid_rewrite <- (update_app2 update [a1] (Some ts) a2).
    cbn.
    destruct (FMap.find (mint_burn_token_id a1)) eqn:E; 
    destruct (FMap.find (mint_burn_token_id a2)) eqn:E2;
    destruct (mint_burn_token_id a1 =? mint_burn_token_id a2) eqn:E3.
    - apply N.eqb_eq in E3. setoid_rewrite E3. setoid_rewrite E3 in E.
    setoid_rewrite E3 in E2. setoid_rewrite FMap.find_add in E2.
    inversion E2.
    setoid_rewrite E. setoid_rewrite E3.
    setoid_rewrite FMap.find_add. f_equal.
    setoid_rewrite E3.
    setoid_rewrite FMap.add_add.
    easy.
    - apply N.eqb_neq in E3.
    setoid_rewrite FMap.find_add_ne in E2; try easy.
    setoid_rewrite E2.
    setoid_rewrite FMap.find_add_ne; try easy.
    setoid_rewrite E.
    f_equal.
    now rewrite FMap.add_commute.
    - apply N.eqb_eq in E3. setoid_rewrite E3 in E. setoid_rewrite E3 in E2. setoid_rewrite FMap.find_add in E2. easy.
    - apply N.eqb_neq in E3.
    setoid_rewrite FMap.find_add_ne in E2; try easy.
    now setoid_rewrite E2.
    - apply N.eqb_eq in E3. setoid_rewrite E3 in E. setoid_rewrite E in E2. easy.
    - apply N.eqb_neq in E3. 
    setoid_rewrite FMap.find_add_ne; try easy.
    now setoid_rewrite E.
    - easy.
    - easy.
Qed.

Lemma update_app_not_none {a txs ts} :
let update := fun (supplies_opt : option TokenTotalSupply) (tx : MintBurnTx) =>
        do supplies <- supplies_opt ;
        do ts <- FMap.find tx.(mint_burn_token_id) supplies ;
        let new_s := ts + tx.(mint_burn_amount) in
        Some (FMap.update tx.(mint_burn_token_id) (Some new_s) supplies)
    in
    fold_left update (a :: txs) ts <> None ->
    fold_left update (txs) ts <> None.
Proof.
    intros. generalize dependent ts. induction txs.
    - intros. cbn in H. destruct (ts) eqn:E; try easy.  
    - intros. rewrite update_app2 in H. rewrite update_app2 in H.
        unfold update in H.
        rewrite update_comm in H.
        rewrite <- update_app in H.
        apply IHtxs in H.
        rewrite <- update_app in H.
        easy.
Qed.

(*
Lemma never_added_to_state {id txs ts prev_state} :
    FMap.find id (token_total_supply (fa2_assets prev_state)) = None ->
    mint_update_total_supply (txs) (token_total_supply (fa2_assets prev_state)) = Some ts ->
    FMap.find id ts = None.
Proof.
    intros. generalize dependent prev_state. generalize dependent ts. induction txs. 
    - intros. cbn in *. inversion H0. easy.
    - intros. unfold mint_update_total_supply in H0. rewrite update_app2 in H0.
    unfold mint_update_total_supply in IHtxs. rewrite update_assoc in IHtxs.
*)
    

Lemma some_is_not_none {A} : forall (x : option A) (y : A),
    x = Some y ->
    x <> None.
Proof.
    easy.
Qed.

Lemma mint_app_is_some {prev_state a txs ts} :
    mint_update_total_supply (a :: txs) (token_total_supply (fa2_assets prev_state)) = Some ts ->
    exists t, mint_update_total_supply (txs) (token_total_supply (fa2_assets prev_state)) = Some t.
Proof.
    intros. apply some_is_not_none in H. unfold mint_update_total_supply in H.
    apply update_app_not_none in H. unfold not in H.
    destruct (fold_left
    (fun (supplies_opt : option TokenTotalSupply) (tx : MintBurnTx) =>
     do supplies <- supplies_opt;
     do ts <- FMap.find (mint_burn_token_id tx) supplies;
     Some
       (FMap.update (mint_burn_token_id tx)
          (Some (ts + mint_burn_amount tx)) supplies)) txs
    (Some (token_total_supply (fa2_assets prev_state)))) eqn:E.
    - easy. 
    - apply H in E. easy.
Qed. 

Lemma mint_app_is_some_supply {prev_state txs a t0 fa2_token_id new_supply} :
FMap.find fa2_token_id
       (token_total_supply
          (fa2_assets
             (setter_from_getter_MultiAssetStorage_fa2_assets
                (fun _ : MultiTokenStorage =>
                 setter_from_getter_MultiTokenStorage_token_total_supply
                   (fun _ : TokenTotalSupply => t0)
                   (setter_from_getter_MultiTokenStorage_ledger
                      (fun _ : Ledger =>
                       mint_update_balances (a :: txs)
                         (ledger (fa2_assets prev_state)))
                      (fa2_assets prev_state))) prev_state))) =
     Some new_supply ->
     
exists supply t, FMap.find fa2_token_id
     (token_total_supply
        (fa2_assets
           (setter_from_getter_MultiAssetStorage_fa2_assets
              (fun _ : MultiTokenStorage =>
               setter_from_getter_MultiTokenStorage_token_total_supply
                 (fun _ : TokenTotalSupply => t)
                 (setter_from_getter_MultiTokenStorage_ledger
                    (fun _ : Ledger =>
                     mint_update_balances (txs)
                       (ledger (fa2_assets prev_state)))
                    (fa2_assets prev_state))) prev_state))) =
   Some supply.
Proof. Admitted.


Lemma mint_preserves_metadata {prev_state next_state chain ctx acts p} :
    fa2_receive chain ctx prev_state (Some (Tokens (MintTokens p))) = Some (next_state, acts) ->
    prev_state.(fa2_assets).(token_metadata) = next_state.(fa2_assets).(token_metadata).
Proof.
    intros. contract_simpl fa2_receive fa2_init. easy.
Qed.
    
Lemma mint_correct {prev_state next_state chain ctx acts fa2_token_id txs old_supply new_supply} :
    fa2_receive chain ctx prev_state (Some (Tokens (MintTokens txs))) = Some (next_state, acts) ->
    FMap.find fa2_token_id prev_state.(fa2_assets).(token_total_supply) = Some old_supply ->
    FMap.find fa2_token_id next_state.(fa2_assets).(token_total_supply) = Some new_supply ->
    let delta_supply := sumN (fun (txs : MintBurnTx) => txs.(mint_burn_amount)) (filter (fun tx => tx.(mint_burn_token_id) =? fa2_token_id) txs) in
    new_supply = old_supply + delta_supply.
Proof.
    intros. contract_simpl fa2_receive fa2_init. generalize dependent t0. generalize dependent new_supply. induction txs.
    - intros. cbn in *. inversion H3. now assert (old_supply = new_supply).
    - intros. destruct (mint_burn_token_id a =? fa2_token_id) eqn:E.
        -- cbn in delta_supply. destruct (mint_burn_token_id a =? fa2_token_id) eqn:E2 in delta_supply.
            --- apply mint_app_is_some in H3.
                apply mint_app_is_some_supply in H1. inversion H1. admit.
            --- admit.
        -- admit.
             
            Admitted.
            
            
        (*
            --- easy.
        -- cbn in delta_supply. destruct (FMap.find (mint_burn_token_id a) (token_total_supply (fa2_assets prev_state))) eqn:E2;
        destruct (mint_burn_token_id a =? fa2_token_id) eqn:E3 in delta_supply; try easy.
            --- unfold mint_update_total_supply in H3. apply mint_app_is_some in H3. inversion H3. apply IHtxs in H1; try easy.
            admit. 
            --- cbn in *. setoid_rewrite E2 in H3. rewrite update_none_is_none in H3. easy.  
*)




    (*
        - intros. apply (update_one_correct a txs prev_state fa2_token_id old_supply new_supply delta_supply t0) in H3; try easy.
    destruct (mint_burn_token_id a =? fa2_token_id) eqn:E.
    -- cbn in H3. setoid_rewrite E in H3. assert (sumN (fun txs : MintBurnTx => mint_burn_amount txs)
        (a :: filter (fun tx : MintBurnTx => mint_burn_token_id tx =? fa2_token_id) txs) = 
        sumN (fun txs : MintBurnTx => mint_burn_amount txs)
        (a :: filter (fun tx : MintBurnTx => mint_burn_token_id tx =? fa2_token_id) txs)). easy. apply H3 in H. unfold delta_supply. cbn. rewrite E. apply H.
    -- cbn in H3. setoid_rewrite E in H3. assert (sumN (fun txs : MintBurnTx => mint_burn_amount txs)
    (filter (fun tx : MintBurnTx => mint_burn_token_id tx =? fa2_token_id)
       txs) =
  sumN (fun txs : MintBurnTx => mint_burn_amount txs)
    (filter (fun tx : MintBurnTx => mint_burn_token_id tx =? fa2_token_id)
       txs)). easy. apply H3 in H. unfold delta_supply. cbn. rewrite E. apply H.
    *)



    
    

    
    


    
    
        

        




    


Lemma set_admin_does_not_change_minter {prev_state next_state chain ctx addr acts} :
    fa2_receive chain ctx prev_state (Some (Admin (Token_admin (Set_admin addr)))) = Some (next_state, acts) ->
    prev_state.(fa2_admin).(tas_minter) = next_state.(fa2_admin).(tas_minter).
Proof.
    intros. contract_simpl fa2_receive fa2_init. unfold set_admin.
    cbn. unfold fail_if_not_admin in H. destruct_address_eq; try easy.
Qed. 

Lemma confirm_admin_does_not_change_minter {prev_state next_state chain ctx acts} :
    fa2_receive chain ctx prev_state (Some (Admin (Token_admin Confirm_admin))) = Some (next_state, acts) ->
    prev_state.(fa2_admin).(tas_minter) = next_state.(fa2_admin).(tas_minter).
Proof.
    intros. contract_simpl fa2_receive fa2_init.
    unfold confirm_new_admin in H. destruct (tas_pending_admin (fa2_admin prev_state)) in H; try easy;
    destruct_address_eq; try easy; now inversion H.
Qed.

Lemma pause_does_not_change_minter {prev_state next_state chain ctx param acts} :
    fa2_receive chain ctx prev_state (Some (Admin (Token_admin (Pause param)))) = Some (next_state, acts) ->
    prev_state.(fa2_admin).(tas_minter) = next_state.(fa2_admin).(tas_minter).
Proof.
    intros. contract_simpl fa2_receive fa2_init. unfold fail_if_not_admin in H;
    destruct_address_eq; try easy; now inversion H.
Qed. 

Lemma no_metadata_no_supply : forall bstate caddr fa2_token_id (trace: ChainTrace empty_state bstate),
env_contracts bstate caddr = Some (FA2_contract : WeakContract) ->
exists cstate depinfo inc_calls,
        contract_state bstate caddr = Some cstate /\
        deployment_info Setup trace caddr = Some depinfo /\
        incoming_calls MultiAssetParam trace caddr = Some inc_calls /\
        (
            FMap.find fa2_token_id cstate.(fa2_assets).(token_metadata) = None ->
            FMap.find fa2_token_id cstate.(fa2_assets).(token_total_supply) = None
        ).
Proof. 
    contract_induction; try easy.
    - intros. unfold init in init_some. cbn in *. unfold fa2_init in init_some.
        cbn in *. inversion init_some; try easy. subst. cbn in *.
        induction (tokens setup); try easy.
        cbn in *. destruct (tm_token_id a =? fa2_token_id) eqn: E.
        + apply N.eqb_eq in E. subst. cbn in *. setoid_rewrite FMap.find_add in H. easy.
        + apply N.eqb_neq in E. setoid_rewrite FMap.find_add_ne in H; try easy. apply IHl in H; try easy.
            setoid_rewrite FMap.find_add_ne; try easy.
    - intros. unfold callFrom in *. unfold receive in receive_some. simpl in *. destruct msg; try easy; destruct m; destruct param.
        + erewrite <- assets_endpoint_preserves_metadata in H; eauto.
            apply IH in H. erewrite <- assets_endpoint_preserves_total_supply; eauto. 
        + erewrite <- assets_endpoint_preserves_metadata in H; eauto.
            apply IH in H. erewrite <- assets_endpoint_preserves_total_supply; eauto. 
            + erewrite <- assets_endpoint_preserves_metadata in H; eauto.
            apply IH in H. erewrite <- assets_endpoint_preserves_total_supply; eauto.
         


Lemma fa2_no_mint_before_token_created : forall bstate caddr fa2_token_id (trace: ChainTrace empty_state bstate),
    env_contracts bstate caddr = Some (FA2_contract : WeakContract) ->
    exists cstate depinfo inc_calls,
            contract_state bstate caddr = Some cstate /\
            deployment_info Setup trace caddr = Some depinfo /\
            incoming_calls MultiAssetParam trace caddr = Some inc_calls /\
            (
                FMap.find fa2_token_id cstate.(fa2_assets).(token_metadata) = None ->
                sumZ (fun callInfo => mint_or_burn fa2_token_id callInfo.(call_msg)) inc_calls = 0%Z
            ).
Proof.
    contract_induction; try easy.
    - intros. unfold callFrom in *. unfold receive in receive_some. simpl in *. destruct msg; try easy; destruct m; destruct param.
        -- erewrite <- assets_endpoint_preserves_metadata in H; eauto.
        -- erewrite <- assets_endpoint_preserves_metadata in H; eauto.
        -- erewrite <- assets_endpoint_preserves_metadata in H; eauto.
        -- destruct tokenAdmin.
            --- erewrite <- set_admin_preserves_metadata in H; eauto.
            --- erewrite <- confirm_admin_preserves_metadata in H; eauto.
            --- erewrite <- pause_preserves_metadata in H; eauto.
            --- erewrite <- set_minter_preserves_metadata in H; eauto.
        -- destruct tokenMetaData. destruct (tm_token_id =? fa2_token_id) eqn:E.
            --- cbn in receive_some. unfold create_token in receive_some.
            apply N.eqb_eq in E. subst. cbn in *.
            destruct (FMap.find fa2_token_id (token_metadata (fa2_assets prev_state))); try easy.
            --- rewrite N.eqb_neq in E. eapply create_new_token_changes_nothing_else in receive_some; eauto. inversion receive_some.
            setoid_rewrite H1 in IH. apply IH in H. cbn. easy.
        -- erewrite <- mint_preserves_metadata in H; eauto. apply IH in H as H2. rewrite H2.
        cbn in receive_some. destruct (fail_if_not_minter ctx (fa2_admin prev_state)); try easy.
        unfold mint_update_total_supply in receive_some. Admitted.
        

        


Lemma fa2_correct : forall bstate caddr fa2_token_id (trace: ChainTrace empty_state bstate),
    env_contracts bstate caddr = Some (FA2_contract : WeakContract) ->
    exists cstate depinfo inc_calls,
        contract_state bstate caddr = Some cstate /\
        deployment_info Setup trace caddr = Some depinfo /\
        incoming_calls MultiAssetParam trace caddr = Some inc_calls /\
        (
        let total_supply_opt := FMap.find fa2_token_id cstate.(fa2_assets).(token_total_supply) in
        let metadata_opt := FMap.find fa2_token_id cstate.(fa2_assets).(token_metadata) in
        match total_supply_opt with
        | Some total_supply =>
            match metadata_opt with
            | Some metadata =>
                sumZ (fun callInfo => mint_or_burn fa2_token_id callInfo.(call_msg)) inc_calls = Z.of_N total_supply
            | None => True
            end
        | None =>
            match metadata_opt with
            | Some metadata => True
            | None => True
            end
        end
        ).
Proof.
    contract_induction;
    intros; try easy.
    - intros. cbn in *. destruct (FMap.find fa2_token_id (token_total_supply (fa2_assets result))) eqn:E; destruct (FMap.find fa2_token_id (token_metadata (fa2_assets result))) eqn:E2; try easy.
        + eapply init_total_supply_correct in init_some; now eauto.
    - unfold callFrom in *. unfold receive in receive_some. simpl in *. destruct msg; try easy; destruct m; destruct param.
        + erewrite <- assets_endpoint_preserves_total_supply; eauto. erewrite <- assets_endpoint_preserves_metadata; eauto.
        + erewrite <- assets_endpoint_preserves_total_supply; eauto. erewrite <- assets_endpoint_preserves_metadata; eauto.
        + erewrite <- assets_endpoint_preserves_total_supply; eauto. erewrite <- assets_endpoint_preserves_metadata; eauto.
        + destruct tokenAdmin.
            -- erewrite <- set_admin_preserves_total_supply; eauto. erewrite <- set_admin_preserves_metadata; eauto.
            -- erewrite <- confirm_admin_preserves_total_supply; eauto. erewrite <- confirm_admin_preserves_metadata; eauto.
            -- erewrite <- pause_preserves_total_supply; eauto. erewrite <- pause_preserves_metadata; eauto.
            -- erewrite <- set_minter_preserves_total_supply; eauto. erewrite <- set_minter_preserves_metadata; eauto.
        + destruct tokenMetaData. destruct (fa2_token_id =? tm_token_id) eqn:E.
        destruct (FMap.find fa2_token_id (token_total_supply (fa2_assets new_state))) eqn:E2;
        destruct (FMap.find fa2_token_id (token_metadata (fa2_assets new_state))) eqn:E3; try easy.
            ++ cbn. apply create_new_token_means_zero_supply in receive_some as H.
            apply N.eqb_eq in E. subst. rewrite H in E2. inversion E2. admit.

            ++ destruct_address_eq; cbn.
            -- rewrite N.eqb_neq in E. eapply create_new_token_changes_nothing_else in receive_some; eauto. inversion receive_some.
            rewrite <- H0. rewrite <- H. destruct_address_eq; now apply IH. (* Other token is created*)

        + induction p. 
            -- erewrite <- empty_mint_preserves_total_supply; eauto. erewrite <- mint_preserves_metadata; eauto.
            -- destruct a eqn:E. destruct (mint_burn_token_id =? fa2_token_id) eqn:E2.
                --- apply N.eqb_eq in E2. destruct_address_eq.
                    ---- admit.
                    ---- rewrite <- E in receive_some. admit.
                --- destruct_address_eq.
                    ---- cbn. rewrite E2. cbn in *. apply IH.    
                        
  
    

(*

(* Assuming the minter address never changes. The total supply of a token will always be equal to the sum of burn and mints received. *)
Lemma fa2_correct2 : forall bstate caddr fa2_token_id total_supply metadata (trace: ChainTrace empty_state bstate),
    env_contracts bstate caddr = Some (FA2_contract : WeakContract) ->
    exists cstate depinfo inc_calls,
        contract_state bstate caddr = Some cstate /\
        deployment_info Setup trace caddr = Some depinfo /\
        incoming_calls MultiAssetParam trace caddr = Some inc_calls /\
        (
        forall state, state.(fa2_admin).(tas_minter) = depinfo.(deployment_setup).(minter_addr) -> (* Minter is never changed *)
        FMap.find fa2_token_id state.(fa2_assets).(token_metadata) = Some metadata ->
        FMap.find fa2_token_id cstate.(fa2_assets).(token_total_supply) = Some total_supply -> (* Token is created *)
        FMap.find fa2_token_id cstate.(fa2_assets).(token_metadata) = Some metadata -> (* Token is created *)
        sumZ (fun callInfo => mint_or_burn fa2_token_id callInfo.(call_msg)) (filter (callFrom state.(fa2_admin).(tas_minter)) inc_calls) = Z.of_N total_supply
        ).
Proof.
    contract_induction;
    intros. now apply IH in H.
    - intros. cbn in *. eapply init_total_supply_correct in init_some; now eauto.
    - unfold callFrom. apply IH in H; try easy.
    - unfold callFrom. unfold receive in receive_some. simpl in *. destruct msg. try easy; destruct m. admit. admit.

            -- erewrite <- set_admin_preserves_total_supply in H0; eauto. destruct_address_eq; now apply IH in H.
            -- erewrite <- confirm_admin_preserves_total_supply in H0; eauto. destruct_address_eq; now apply IH in H.
            -- erewrite <- pause_preserves_total_supply in H0; eauto. destruct_address_eq; now apply IH in H.
            -- erewrite <- set_minter_preserves_total_supply in H0; eauto. destruct_address_eq; now apply IH in H.
            --   
        

Qed.

*)

(*
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
    - unfold callFrom. unfold receive in receive_some. simpl in *. destruct msg. try easy; destruct m. destruct param; try
        erewrite <- assets_endpoint_preserves_total_supply in H; eauto; erewrite <- assets_endpoint_does_not_change_minter; eauto;
        destruct_address_eq; now apply IH.
        + destruct param. destruct tokenAdmin.
        -- erewrite <- set_admin_preserves_total_supply in H; eauto. erewrite <- set_admin_does_not_change_minter; eauto.
        destruct_address_eq; now apply IH.
        -- erewrite <- confirm_admin_preserves_total_supply in H; eauto. erewrite <- confirm_admin_does_not_change_minter; eauto.
        destruct_address_eq; now apply IH.
        -- erewrite <- pause_preserves_total_supply in H; eauto. erewrite <- pause_does_not_change_minter; eauto.
        destruct_address_eq; now apply IH.
        -- erewrite <- set_minter_preserves_total_supply in H; eauto. destruct ().      
*)
End FA2_Multi_Asset.