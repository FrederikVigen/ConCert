(** * FA2 Multi Asset *)
(** This is the main file for Tokens Contract

    The ligo implementation can be found at
    https://github.com/bender-labs/wrap-tz-contracts/blob/master/ligo/fa2/multi_asset/fa2_multi_asset.mligo
*)

Require Import Blockchain.
From ConCert.Examples Require Import FA2Interface.
From ConCert.Utils Require Import Extras.
From ConCert.Execution Require Import InterContractCommunication.
Require Import Automation.
Require Import FA2Interface_Wrap.
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

(** * Types *)
Section FA2_Multi_Asset.
Context {BaseTypes : ChainBase}.
Set Nonrecursive Elimination Schemes.

(** ** Entrypoint params *)
Inductive MultiAssetParam :=
| Assets (param : FA2EntryPoints)
| Admin (param : MultiTokenAdmin)
| Tokens (param : TokenManager).

(* begin hide *)
Global Instance MultiAssetParam_serializable : Serializable MultiAssetParam :=
Derive Serializable MultiAssetParam_rect<Assets, Admin, Tokens>.
(* end hide *)

(** ** Setup type *)
Record Setup := {
    admin_addr : Address;
    minter_addr : Address;
    tokens : list token_metadata;
    meta_data_uri : N
}.

(* begin hide *)
Global Instance Setup_serializable : Serializable Setup :=
Derive Serializable Setup_rect<Build_Setup>.
(* end hide *)

(** * Implementation *)
(** ** Main entry point *)
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
    let token_metadata_new := fold_right (fun (token_metadata' : token_metadata) (acc : TokenMetaDataStorage) => FMap.update token_metadata'.(metadata_token_id) (Some token_metadata') acc) FMap.empty tokens in
    let supply := fold_right (fun (token_metadata' : token_metadata) (acc : TokenTotalSupply) => FMap.update token_metadata'.(metadata_token_id) (Some 0) acc) FMap.empty tokens in
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
            mts_token_metadata := token_metadata_new ;
            token_total_supply := supply
        |} ;
        metadata := meta
    |}).

(** The FA2 Contract **)
Definition FA2_contract : Contract Setup MultiAssetParam MultiAssetStorage :=
    build_contract fa2_init fa2_receive.

(**----------------- Admin Proofs -----------------**)

(** * Proofs *)
(** ** Create token correct *)
Lemma create_token_creates_new_token {ctx chain prev_state next_state token_id token_info tMetaData} :
    tMetaData = {|
        metadata_token_id := token_id ;
        metadata_token_info := token_info
    |} ->
    fa2_receive chain ctx prev_state (Some (Admin (Create_token tMetaData))) = Some (next_state, []) ->
    FMap.find token_id next_state.(fa2_assets).(mts_token_metadata) = Some tMetaData.
Proof.
    intros. 
    contract_simpl fa2_receive fa2_init. 
    unfold create_token in H1. cbn in H1.
    destruct (FMap.find token_id (mts_token_metadata (fa2_assets prev_state))) in H1; try easy.
    inversion H1. cbn. 
    setoid_rewrite FMap.find_add. reflexivity.
Qed.

(** ** Set new admin correct *)
Lemma set_new_admin_functionally_correct {ctx chain prev_state next_state new_admin} :
    fa2_receive chain ctx prev_state (Some (Admin (Token_admin (Set_admin new_admin)))) = Some (next_state, []) ->
    next_state.(fa2_admin).(tas_pending_admin) = Some new_admin.
Proof.
    intros. 
    contract_simpl fa2_receive fa2_init. 
    easy.
Qed.

(** ** Set new minter correct *)
Lemma set_new_minter_functionally_correct {ctx chain prev_state next_state new_minter} :
    fa2_receive chain ctx prev_state (Some (Admin (Token_admin (Set_minter new_minter)))) = Some (next_state, []) ->
    next_state.(fa2_admin).(tas_minter) = new_minter.
Proof.
    intros. 
    contract_simpl fa2_receive fa2_init. 
    easy.
Qed.

(** ** Confirm admin correct *)
Lemma confirm_admin_functionally_correct {ctx chain prev_state next_state} :
    fa2_receive chain ctx prev_state (Some (Admin (Token_admin (Confirm_admin)))) = Some (next_state, []) ->
    next_state.(fa2_admin).(tas_pending_admin) = None /\ next_state.(fa2_admin).(tas_admin) = ctx.(ctx_from).
Proof.
    intros. 
    contract_simpl fa2_receive fa2_init. 
    unfold confirm_new_admin in H. 
    destruct (tas_pending_admin (fa2_admin prev_state)); try easy.
    destruct (address_eqb ctx.(ctx_from) a) in H; try easy.
    inversion H. 
    easy.
Qed.

(** ** Pause correct *)
Lemma pause_functionally_correct {ctx chain prev_state next_state tokens token_id} :
    tokens = [{|
        pp_token_id := token_id;
        pp_paused := true
    |}] ->
    fa2_receive chain ctx prev_state (Some (Admin (Token_admin (Pause tokens)))) = Some (next_state, []) ->
    FMap.find token_id next_state.(fa2_admin).(tas_paused) = Some tt.
Proof.
    intros. 
    contract_simpl fa2_receive fa2_init.
    cbn. 
    apply FMap.find_add.
Qed.

(** ** Unpause correct *)
Lemma unpause_functionally_correct {ctx chain prev_state next_state tokens token_id} :
    tokens = [{|
        pp_token_id := token_id;
        pp_paused := false
    |}] ->
    fa2_receive chain ctx prev_state (Some (Admin (Token_admin (Pause tokens)))) = Some (next_state, []) ->
    FMap.find token_id next_state.(fa2_admin).(tas_paused) = None.
Proof.
    intros. 
    contract_simpl fa2_receive fa2_init.
    cbn. 
    apply FMap.find_remove.
Qed.

(**----------------- Assets Proofs -----------------**)
(** ** Balance of callback correct *)
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
    intros. 
    contract_simpl fa2_receive fa2_init. 
    rewrite H0 in H1. cbn in H1. 
    destruct (FMap.find req_token_id (mts_token_metadata (fa2_assets state))).
    - inversion H1. reflexivity.
    - discriminate.
Qed.

(** ** Transfer preserves total supply *)
Lemma transfer_preserves_total_supply {prev_state next_state acts chain ctx transfers} :
    fa2_receive chain ctx prev_state (Some (Assets (FA2_Transfer transfers))) = Some (next_state, acts) ->
    prev_state.(fa2_assets).(token_total_supply) = next_state.(fa2_assets).(token_total_supply).
Proof.
    intros. 
    contract_simpl fa2_receive fa2_init. 
    reflexivity.
Qed. 

(** ** Inc on one balance preserves others *)
Lemma inc_balance_other_preservces_own {x y ledger amount token_id' token_id} :
    x <> y ->
    FMap.find (x, token_id') ledger = FMap.find (x, token_id') (inc_balance y token_id amount ledger).
Proof.
    intros. 
    unfold inc_balance. 
    destruct (get_balance_amt (y, token_id) ledger + amount =? 0).
    - setoid_rewrite FMap.find_remove_ne; try easy.
    - cbn. setoid_rewrite FMap.find_add_ne; try easy.
Qed. 

(** ** Transfer correct *)
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
    intros. 
    contract_simpl fa2_receive fa2_init. 
    split.
    - unfold get_balance_amt. 
        destruct (FMap.find (fromAddr, token_id) (ledger (fa2_assets prev_state))) eqn: E.
            * setoid_rewrite E. setoid_rewrite E. destruct (n-amount).
                -- cbn. 
                   rewrite <- inc_balance_other_preservces_own; 
                   try easy. 
                   setoid_rewrite FMap.find_remove. easy.
                -- cbn. 
                   rewrite <- inc_balance_other_preservces_own; 
                   try easy. 
                   setoid_rewrite FMap.find_add. easy.
            * setoid_rewrite E. 
              setoid_rewrite E. 
              cbn. rewrite <- inc_balance_other_preservces_own; try easy.
            setoid_rewrite FMap.find_remove. easy.
    - unfold get_balance_amt. 
      destruct (FMap.find (fromAddr, token_id) (ledger (fa2_assets prev_state))) eqn: E;
        do 2 setoid_rewrite E.
        + destruct (n-amount).
            * unfold inc_balance. cbn. 
              destruct (FMap.find (toAddr, token_id) (ledger (fa2_assets prev_state))) eqn: E1.
                -- unfold get_balance_amt. 
                   setoid_rewrite FMap.find_remove_ne; try easy. 
                   setoid_rewrite E1.
                    destruct (n0+amount) eqn: E2.
                    --- cbn. 
                        setoid_rewrite FMap.find_remove. easy.
                    --- cbn. 
                        setoid_rewrite FMap.find_add. 
                        setoid_rewrite FMap.find_remove_ne; try easy.
                        setoid_rewrite E1. 
                        assumption.
                -- unfold get_balance_amt. 
                   setoid_rewrite FMap.find_remove_ne; 
                   try easy. setoid_rewrite E1.
                    destruct (0+amount) eqn: E2.
                    --- cbn. 
                        setoid_rewrite FMap.find_remove. easy.
                    --- cbn. 
                        setoid_rewrite FMap.find_add. 
                        setoid_rewrite FMap.find_remove_ne; try easy.
                        setoid_rewrite E1. assumption.
            * cbn. unfold inc_balance. cbn. 
              destruct (FMap.find (toAddr, token_id) (ledger (fa2_assets prev_state))) eqn: E1.
                -- unfold get_balance_amt. 
                   setoid_rewrite FMap.find_add_ne; try easy. 
                   setoid_rewrite E1.
                    destruct (n0+amount) eqn: E2.
                    --- cbn. setoid_rewrite FMap.find_remove. easy.
                    --- cbn. setoid_rewrite FMap.find_add. 
                        setoid_rewrite FMap.find_add_ne; try easy.
                        setoid_rewrite E1. assumption.
                -- unfold get_balance_amt. 
                   setoid_rewrite FMap.find_add_ne; try easy. 
                   setoid_rewrite E1.
                    destruct (0+amount) eqn: E2.
                    --- cbn. setoid_rewrite FMap.find_remove. easy.
                    --- cbn. setoid_rewrite FMap.find_add. 
                        setoid_rewrite FMap.find_add_ne; try easy.
                        setoid_rewrite E1. assumption.
        + unfold inc_balance. cbn. 
          destruct (FMap.find (toAddr, token_id) (ledger (fa2_assets prev_state))) eqn: E1.
            * unfold get_balance_amt. 
              setoid_rewrite FMap.find_remove_ne; try easy. 
              setoid_rewrite FMap.find_remove_ne; try easy.
              setoid_rewrite E1. 
              destruct (n + amount) eqn: E2.
                -- cbn. setoid_rewrite FMap.find_remove. easy.
                -- cbn. setoid_rewrite FMap.find_add. 
                   setoid_rewrite E1. assumption.
            * unfold get_balance_amt. 
              setoid_rewrite FMap.find_remove_ne; try easy. 
              setoid_rewrite FMap.find_remove_ne; try easy.
                setoid_rewrite E1. destruct (0 + amount) eqn: E2.
                -- cbn. setoid_rewrite FMap.find_remove. easy.
                -- cbn. setoid_rewrite FMap.find_add. 
                setoid_rewrite E1. assumption.
Qed.

(** ** Transfer to self changes nothing *)
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
    intros. 
    contract_simpl fa2_receive fa2_init. 
    unfold get_balance_amt. 
    destruct (FMap.find (toAddr, token_id) (ledger (fa2_assets prev_state))) eqn: E;
    do 2 setoid_rewrite E.
    - unfold get_balance_amt in H3. 
      setoid_rewrite E in H3. 
      destruct (n-amount) eqn: E2; cbn.
        + unfold inc_balance. 
          unfold get_balance_amt. 
          setoid_rewrite FMap.find_remove. 
          setoid_rewrite FMap.find_remove.
            cbn. destruct (0+amount) eqn: E3; cbn.
            * setoid_rewrite FMap.find_remove. 
              rewrite <- E2 in E3. easy.
            * setoid_rewrite FMap.find_add. 
              apply N.ltb_ge in H3. 
              destruct n; easy.
        + unfold inc_balance. 
          unfold get_balance_amt. 
          setoid_rewrite FMap.find_add.
            setoid_rewrite FMap.find_add. 
            destruct (N.pos p + amount) eqn: E3; cbn.
            * setoid_rewrite FMap.find_remove. easy.
            * setoid_rewrite FMap.find_add. easy.
    - unfold inc_balance. cbn. 
      unfold get_balance_amt. 
      setoid_rewrite FMap.find_remove. 
      setoid_rewrite FMap.find_remove.
        destruct (0 + amount) eqn: E2; cbn.
        + setoid_rewrite FMap.find_remove; easy.
        + setoid_rewrite FMap.find_add. 
          unfold get_balance_amt in H3. 
          setoid_rewrite E in H3. 
          apply N.ltb_ge in H3. easy.
Qed.

(**----------------- TokenManager Proofs -----------------**)
(** ** Mint correct *)
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
    intros. 
    cbn in H. 
    contract_simpl fa2_receive fa2_init. cbn in H1. split.
    - setoid_rewrite FMap.find_add in H1. 
      setoid_rewrite H0 in H. 
      inversion H1. easy.
    - unfold inc_balance. cbn. 
      destruct (get_balance_amt (owner, token_id) (ledger (fa2_assets prev_state)) + amount) eqn: E; 
        cbn; unfold get_balance_amt.
        + setoid_rewrite FMap.find_remove. easy.
        + setoid_rewrite FMap.find_add. easy.
Qed.

(** ** Burn correct *)
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
    intros. 
    cbn in H. contract_simpl fa2_receive fa2_init. 
    cbn in H1. split.
    - setoid_rewrite FMap.find_add in H1. 
      setoid_rewrite H0 in H. 
      inversion H1. easy.
    - unfold inc_balance. cbn. 
      destruct (get_balance_amt (owner, token_id) (ledger (fa2_assets prev_state)) - amount) eqn: E; 
        cbn; unfold get_balance_amt.
        + setoid_rewrite FMap.find_remove. easy.
        + setoid_rewrite FMap.find_add. easy.
Qed.

(** ** Only minter can mint and burn *)
Lemma only_minter_can_mint_and_burn {chain ctx prev_state p} :
    (ctx.(ctx_from) =? prev_state.(fa2_admin).(tas_minter))%address = false ->
    fa2_receive chain ctx prev_state (Some (Tokens p)) = None.
Proof.
    intros; 
    contract_simpl fa2_receive fa2_init;
    unfold fail_if_not_minter;
    now rewrite H.
Qed.

(** ** Can't burn more than supply *)
Lemma cant_burn_more_than_supply {chain ctx prev_state owner token_id amount v} :
    FMap.find token_id (prev_state.(fa2_assets).(token_total_supply)) = Some v -> 
    v < amount ->
    fa2_receive chain ctx prev_state (Some (Tokens (BurnTokens [{|
    mint_burn_owner := owner ;
    mint_burn_token_id := token_id ;
    mint_burn_amount := amount
    |}]))) = None.
Proof.
    intros. 
    contract_simpl fa2_receive fa2_init. 
    unfold fail_if_not_minter. 
    destruct address_eqb; try easy.
    destruct (get_balance_amt (owner, token_id) (ledger (fa2_assets prev_state)) <? amount); try easy. cbn.
    setoid_rewrite H. destruct (v <? amount) eqn: E; 
    try easy. rewrite N.ltb_ge in E. easy.
Qed.

(** ** Init total supply correct *)
Lemma init_total_supply_correct {chain ctx setup state fa2_token_id total_supply} :
    FMap.find fa2_token_id state.(fa2_assets).(token_total_supply) = Some total_supply ->
    fa2_init chain ctx setup = Some state ->
    total_supply = 0.
Proof.
    intros. 
    contract_simpl fa2_receive fa2_init. 
    induction tokens.
    - cbn in *. 
      setoid_rewrite FMap.find_empty in H. 
      inversion H.
    - cbn in *. destruct (fa2_token_id =? (metadata_token_id a)) eqn:E.
        + rewrite N.eqb_eq in E. 
          subst. 
          setoid_rewrite FMap.find_add in H. easy.
        + rewrite N.eqb_neq in E. 
          setoid_rewrite FMap.find_add_ne in H; try easy.
Qed.

(**----------------- FA2_Multi_Asset -----------------**)
(** * Safety proofs *)
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

(** ** Assets endpoint does not change minter *)
Lemma assets_endpoint_does_not_change_minter {prev_state next_state acts chain ctx param} :
    fa2_receive chain ctx prev_state (Some (Assets param)) = Some (next_state, acts) ->
    prev_state.(fa2_admin).(tas_minter) = next_state.(fa2_admin).(tas_minter).
Proof.
    intros; now contract_simpl fa2_receive fa2_init.
Qed. 

(** ** Assets endpoint preserves total supply *)
Lemma assets_endpoint_preserves_total_supply {prev_state next_state acts chain ctx param} :
    fa2_receive chain ctx prev_state (Some (Assets param)) = Some (next_state, acts) ->
    prev_state.(fa2_assets).(token_total_supply) = next_state.(fa2_assets).(token_total_supply).
Proof.
    intros. 
    contract_simpl fa2_receive fa2_init. 
    destruct param.
    - inversion H1; 
      destruct (transfer ctx transfers default_operator_validator (fa2_assets prev_state)) in H2; 
      try easy; now inversion H2.
    - inversion H1; 
      destruct (get_balance balanceOf (ledger (fa2_assets prev_state)) (mts_token_metadata (fa2_assets prev_state))) in H2; 
      try easy; now inversion H2.
    - inversion H1; 
      destruct (fa2_update_operators ctx updates (operators (fa2_assets prev_state))) in H2; 
      try easy; now inversion H2.
Qed. 

(** ** Assets endpoint preserves metadata *)
Lemma assets_endpoint_preserves_metadata {prev_state next_state acts chain ctx param} :
    fa2_receive chain ctx prev_state (Some (Assets param)) = Some (next_state, acts) ->
    prev_state.(fa2_assets).(mts_token_metadata) = next_state.(fa2_assets).(mts_token_metadata).
Proof.
    intros. 
    contract_simpl fa2_receive fa2_init. cbn. 
    destruct param.
    - inversion H1. 
      destruct (transfer ctx transfers default_operator_validator (fa2_assets prev_state)) in H2;
     now inversion H2.
    - inversion H1. 
      destruct (get_balance balanceOf (ledger (fa2_assets prev_state))
    (mts_token_metadata (fa2_assets prev_state))); try easy.
    - inversion H1. 
      destruct (fa2_update_operators ctx updates (operators (fa2_assets prev_state))); try easy.
Qed.        

(** ** Token metadata for a token does not change for admin endpoint *)
Lemma token_metadata_always_same {prev_state next_state acts chain ctx param fa2_token_id metadata} :
    FMap.find fa2_token_id prev_state.(fa2_assets).(mts_token_metadata) = Some metadata ->
    fa2_receive chain ctx prev_state (Some (Admin param)) = Some (next_state, acts) ->
    FMap.find fa2_token_id prev_state.(fa2_assets).(mts_token_metadata) = FMap.find fa2_token_id next_state.(fa2_assets).(mts_token_metadata).
Proof.
    intros. 
    destruct param. 
    destruct tokenAdmin;
    try contract_simpl fa2_receive fa2_init.
    contract_simpl fa2_receive fa2_init. unfold create_token in H1.
    destruct (FMap.find (metadata_token_id tokenMetaData) (mts_token_metadata (fa2_assets prev_state))) eqn:E; try easy.
    inversion H1. 
    now setoid_rewrite FMap.find_add_ne.
Qed.

(** ** Admin endpoint preserves total supply *)
Lemma token_admin_endpoint_preserves_total_supply {prev_state next_state acts chain ctx param fa2_token_id supply metadata} :
    FMap.find fa2_token_id prev_state.(fa2_assets).(token_total_supply) = Some supply ->
    FMap.find fa2_token_id prev_state.(fa2_assets).(mts_token_metadata) = Some metadata ->
    fa2_receive chain ctx prev_state (Some (Admin param)) = Some (next_state, acts) ->
    FMap.find fa2_token_id prev_state.(fa2_assets).(token_total_supply) = FMap.find fa2_token_id next_state.(fa2_assets).(token_total_supply).
Proof.
    intros. 
    destruct param. 
    destruct tokenAdmin;
    try contract_simpl fa2_receive fa2_init.
    contract_simpl fa2_receive fa2_init. unfold create_token in H2.
    destruct (FMap.find (metadata_token_id tokenMetaData) (mts_token_metadata (fa2_assets prev_state))) eqn:E; try easy.
    inversion H2; 
    setoid_rewrite FMap.find_add_ne; easy.
Qed.

(** ** Admin endpoint preserves metadata *)
Lemma token_admin_endpoint_preserves_metadata {prev_state next_state acts chain ctx param fa2_token_id supply metadata} :
    FMap.find fa2_token_id prev_state.(fa2_assets).(token_total_supply) = Some supply ->
    FMap.find fa2_token_id prev_state.(fa2_assets).(mts_token_metadata) = Some metadata ->
    fa2_receive chain ctx prev_state (Some (Admin param)) = Some (next_state, acts) ->
    FMap.find fa2_token_id prev_state.(fa2_assets).(mts_token_metadata) = FMap.find fa2_token_id next_state.(fa2_assets).(mts_token_metadata).
Proof.
    intros. 
    destruct param. 
    destruct tokenAdmin;
    try contract_simpl fa2_receive fa2_init.
    contract_simpl fa2_receive fa2_init. 
    unfold create_token in H2.
    destruct (FMap.find (metadata_token_id tokenMetaData) (mts_token_metadata (fa2_assets prev_state))) eqn: E; try easy.
    inversion H2; 
    setoid_rewrite FMap.find_add_ne; easy.  
Qed.

(** ** Creating a new token preserves total supply and metadata of others *)
Lemma create_new_token_changes_nothing_else {prev_state next_state acts chain ctx fa2_token_id new_token_id info_map} :
    new_token_id <> fa2_token_id ->
    let new_token_metadata := {|
        metadata_token_id := new_token_id ;
        metadata_token_info := info_map 
    |} in
    fa2_receive chain ctx prev_state (Some (Admin (Create_token new_token_metadata))) = Some (next_state, acts) ->
    FMap.find fa2_token_id prev_state.(fa2_assets).(token_total_supply) = FMap.find fa2_token_id next_state.(fa2_assets).(token_total_supply) /\
    FMap.find fa2_token_id prev_state.(fa2_assets).(mts_token_metadata) = FMap.find fa2_token_id next_state.(fa2_assets).(mts_token_metadata).
Proof.
    intros. 
    split. 
    - contract_simpl fa2_receive fa2_init. 
      unfold create_token in H1.
      destruct (FMap.find (metadata_token_id new_token_metadata) (mts_token_metadata (fa2_assets prev_state))) eqn:E; try easy.
      inversion H1. 
      now setoid_rewrite FMap.find_add_ne.
    - contract_simpl fa2_receive fa2_init. 
      unfold create_token in H1.
      destruct (FMap.find (metadata_token_id new_token_metadata) (mts_token_metadata (fa2_assets prev_state))) eqn:E; try easy.
      inversion H1. now setoid_rewrite FMap.find_add_ne.
Qed.

(** ** Newly created token has zero total supply *)
Lemma create_new_token_means_zero_supply {prev_state next_state acts chain ctx fa2_token_id info_map} :
    let new_token_metadata := {|
        metadata_token_id := fa2_token_id ;
        metadata_token_info := info_map 
    |} in
    fa2_receive chain ctx prev_state (Some (Admin (Create_token new_token_metadata))) = Some (next_state, acts) ->
    FMap.find fa2_token_id next_state.(fa2_assets).(token_total_supply) = Some 0.
Proof.
    intros. contract_simpl fa2_receive fa2_init.
    unfold create_token in H0. 
    destruct (FMap.find (metadata_token_id new_token_metadata) (mts_token_metadata (fa2_assets prev_state))) eqn:E; try easy.
    inversion H0. 
    now setoid_rewrite FMap.find_add.
Qed.

(** ** Set admin preserves total supply *)
Lemma set_admin_preserves_total_supply {prev_state next_state chain ctx addr acts} :
    fa2_receive chain ctx prev_state (Some (Admin (Token_admin (Set_admin addr)))) = Some (next_state, acts) ->
    prev_state.(fa2_assets).(token_total_supply) = next_state.(fa2_assets).(token_total_supply).
Proof.
    intros. 
    contract_simpl fa2_receive fa2_init.
Qed. 

(** ** Confirm admin preserves total supply *)
Lemma confirm_admin_preserves_total_supply {prev_state next_state chain ctx acts} :
    fa2_receive chain ctx prev_state (Some (Admin (Token_admin Confirm_admin))) = Some (next_state, acts) ->
    prev_state.(fa2_assets).(token_total_supply) = next_state.(fa2_assets).(token_total_supply).
Proof.
    intros. 
    contract_simpl fa2_receive fa2_init.
Qed. 

(** ** Pause preserves total supply *)
Lemma pause_preserves_total_supply {prev_state next_state chain ctx acts param} :
    fa2_receive chain ctx prev_state (Some (Admin (Token_admin (Pause param)))) = Some (next_state, acts) ->
    prev_state.(fa2_assets).(token_total_supply) = next_state.(fa2_assets).(token_total_supply).
Proof.
    intros. 
    contract_simpl fa2_receive fa2_init.
Qed.

(** ** Set minter preserves total supply *)
Lemma set_minter_preserves_total_supply {prev_state next_state chain ctx acts addr} :
    fa2_receive chain ctx prev_state (Some (Admin (Token_admin (Set_minter addr)))) = Some (next_state, acts) ->
    prev_state.(fa2_assets).(token_total_supply) = next_state.(fa2_assets).(token_total_supply).
Proof.
    intros. 
    contract_simpl fa2_receive fa2_init.
Qed. 

(** ** Set admin preserves metadata *)
Lemma set_admin_preserves_metadata {prev_state next_state chain ctx addr acts} :
    fa2_receive chain ctx prev_state (Some (Admin (Token_admin (Set_admin addr)))) = Some (next_state, acts) ->
    prev_state.(fa2_assets).(mts_token_metadata) = next_state.(fa2_assets).(mts_token_metadata).
Proof.
    intros. 
    contract_simpl fa2_receive fa2_init.
Qed. 

(** ** Confirm admin preserves metadata *)
Lemma confirm_admin_preserves_metadata {prev_state next_state chain ctx acts} :
    fa2_receive chain ctx prev_state (Some (Admin (Token_admin Confirm_admin))) = Some (next_state, acts) ->
    prev_state.(fa2_assets).(mts_token_metadata) = next_state.(fa2_assets).(mts_token_metadata).
Proof.
    intros. 
    contract_simpl fa2_receive fa2_init.
Qed. 

(** ** Pause preserves metadata *)
Lemma pause_preserves_metadata {prev_state next_state chain ctx acts param} :
    fa2_receive chain ctx prev_state (Some (Admin (Token_admin (Pause param)))) = Some (next_state, acts) ->
    prev_state.(fa2_assets).(mts_token_metadata) = next_state.(fa2_assets).(mts_token_metadata).
Proof.
    intros. 
    contract_simpl fa2_receive fa2_init.
Qed. 

(** ** Set minter preserves metadata *)
Lemma set_minter_preserves_metadata {prev_state next_state chain ctx acts addr} :
    fa2_receive chain ctx prev_state (Some (Admin (Token_admin (Set_minter addr)))) = Some (next_state, acts) ->
    prev_state.(fa2_assets).(mts_token_metadata) = next_state.(fa2_assets).(mts_token_metadata).
Proof.
    intros. 
    contract_simpl fa2_receive fa2_init.
Qed. 

(** ** Empty mint preserves total supply *)
Lemma empty_mint_preserves_total_supply {prev_state next_state chain ctx acts} :
    fa2_receive chain ctx prev_state (Some (Tokens (MintTokens []))) = Some (next_state, acts) ->
    prev_state.(fa2_assets).(token_total_supply) = next_state.(fa2_assets).(token_total_supply).
Proof.
    intros. 
    contract_simpl fa2_receive fa2_init. easy.
Qed.

(** ** Various helper lemmas *)
Lemma burn_update_none_is_none {txs} :
    let update := fun (supplies_opt : option TokenTotalSupply) (tx: MintBurnTx) =>
        do supplies <- supplies_opt ;    
        do ts <- FMap.find tx.(mint_burn_token_id) supplies ;
        do new_s <- sub ts tx.(mint_burn_amount) ;
        Some (FMap.update tx.(mint_burn_token_id) (Some new_s) supplies)
    in
    fold_left update txs None = None.
Proof.
    intros. induction txs.
    - cbn. easy.
    - cbn. easy.
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
    - apply N.eqb_eq in E3. 
      setoid_rewrite E3 in E. 
      setoid_rewrite E3 in E2. 
      setoid_rewrite FMap.find_add in E2. easy.
    - apply N.eqb_neq in E3.
      setoid_rewrite FMap.find_add_ne in E2; try easy.
      now setoid_rewrite E2.
    - apply N.eqb_eq in E3. 
      setoid_rewrite E3 in E.
      setoid_rewrite E in E2. easy.
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
    intros. 
    generalize dependent ts. 
    induction txs.
    - intros. 
      cbn in H. 
      destruct (ts) eqn:E; try easy.  
    - intros. 
      rewrite update_app2 in H. 
      rewrite update_app2 in H.
      unfold update in H.
      rewrite update_comm in H.
      rewrite <- update_app in H.
      apply IHtxs in H.
      rewrite <- update_app in H.
      easy.
Qed.

(** ** Mint preserves metadata *)
Lemma mint_preserves_metadata {prev_state next_state chain ctx acts p} :
    fa2_receive chain ctx prev_state (Some (Tokens (MintTokens p))) = Some (next_state, acts) ->
    prev_state.(fa2_assets).(mts_token_metadata) = next_state.(fa2_assets).(mts_token_metadata).
Proof.
    intros. contract_simpl fa2_receive fa2_init. easy.
Qed.

(** ** Burn preserves metadata *)
Lemma burn_preserves_metadata {prev_state next_state chain ctx acts p} :
    fa2_receive chain ctx prev_state (Some (Tokens (BurnTokens p))) = Some (next_state, acts) ->
    prev_state.(fa2_assets).(mts_token_metadata) = next_state.(fa2_assets).(mts_token_metadata).
Proof.
    intros. contract_simpl fa2_receive fa2_init. easy.
Qed.

(** ** Set admin does not change minter *)
Lemma set_admin_does_not_change_minter {prev_state next_state chain ctx addr acts} :
    fa2_receive chain ctx prev_state (Some (Admin (Token_admin (Set_admin addr)))) = Some (next_state, acts) ->
    prev_state.(fa2_admin).(tas_minter) = next_state.(fa2_admin).(tas_minter).
Proof.
    intros. contract_simpl fa2_receive fa2_init. unfold set_admin.
    cbn. unfold fail_if_not_admin in H. destruct_address_eq; try easy.
Qed. 

(** ** Confirm admin does not change minter *)
Lemma confirm_admin_does_not_change_minter {prev_state next_state chain ctx acts} :
    fa2_receive chain ctx prev_state (Some (Admin (Token_admin Confirm_admin))) = Some (next_state, acts) ->
    prev_state.(fa2_admin).(tas_minter) = next_state.(fa2_admin).(tas_minter).
Proof.
    intros. contract_simpl fa2_receive fa2_init.
    unfold confirm_new_admin in H. destruct (tas_pending_admin (fa2_admin prev_state)) in H; try easy;
    destruct_address_eq; try easy; now inversion H.
Qed.

(** ** Pause does not change minter *)
Lemma pause_does_not_change_minter {prev_state next_state chain ctx param acts} :
    fa2_receive chain ctx prev_state (Some (Admin (Token_admin (Pause param)))) = Some (next_state, acts) ->
    prev_state.(fa2_admin).(tas_minter) = next_state.(fa2_admin).(tas_minter).
Proof.
    intros. contract_simpl fa2_receive fa2_init. 
    unfold fail_if_not_admin in H;
    destruct_address_eq; 
    try easy; now inversion H.
Qed. 

(** ** If no metadata exists for token, then no supply exists *)
Lemma no_metadata_no_supply : forall bstate caddr fa2_token_id (trace: ChainTrace empty_state bstate),
env_contracts bstate caddr = Some (FA2_contract : WeakContract) ->
exists cstate ,
        contract_state bstate caddr = Some cstate /\
        (
            FMap.find fa2_token_id cstate.(fa2_assets).(mts_token_metadata) = None ->
            FMap.find fa2_token_id cstate.(fa2_assets).(token_total_supply) = None
        ).
Proof. 
    contract_induction; try easy.
    - intros. 
      unfold init in init_some. 
      cbn in *. unfold fa2_init in init_some.
      cbn in *. 
      inversion init_some; try easy. subst. cbn in *.
      induction (tokens setup); try easy.
      cbn in *. destruct (metadata_token_id a =? fa2_token_id) eqn: E.
      + apply N.eqb_eq in E. 
        subst. cbn in *. 
        setoid_rewrite FMap.find_add in H. easy.
      + apply N.eqb_neq in E. 
        setoid_rewrite FMap.find_add_ne in H; 
        try easy. apply IHl in H; try easy.
        setoid_rewrite FMap.find_add_ne; try easy.
    - intros. 
      unfold receive in receive_some. 
      simpl in *. destruct msg; try easy; 
      destruct m; destruct param.
     + erewrite <- assets_endpoint_preserves_metadata in H; eauto.
       apply IH in H. 
       erewrite <- assets_endpoint_preserves_total_supply; eauto. 
     + erewrite <- assets_endpoint_preserves_metadata in H; eauto.
       apply IH in H. 
       erewrite <- assets_endpoint_preserves_total_supply; eauto. 
     + erewrite <- assets_endpoint_preserves_metadata in H; eauto.
       apply IH in H. erewrite <- assets_endpoint_preserves_total_supply; eauto.
     + destruct tokenAdmin.
        * erewrite <- set_admin_preserves_metadata in H; eauto.
          erewrite <- set_admin_preserves_total_supply; eauto.
        * erewrite <- confirm_admin_preserves_metadata in H; eauto.
          erewrite <- confirm_admin_preserves_total_supply; eauto.
        * erewrite <- pause_preserves_metadata in H; eauto.
          erewrite <- pause_preserves_total_supply; eauto.
        * erewrite <- set_minter_preserves_metadata in H; eauto.
          erewrite <- set_minter_preserves_total_supply; eauto.
     + destruct tokenMetaData. 
       destruct (metadata_token_id =? fa2_token_id) eqn: E.
        * apply N.eqb_eq in E. subst. cbn in *. 
          unfold create_token in receive_some. cbn in *.
          destruct (FMap.find fa2_token_id (mts_token_metadata (fa2_assets prev_state))) eqn: E1; try easy.
          inversion receive_some. subst. cbn in *. setoid_rewrite FMap.find_add in H. easy.
        * rewrite N.eqb_neq in E. 
          eapply create_new_token_changes_nothing_else in receive_some; eauto. 
          inversion receive_some. setoid_rewrite <- H1 in H. apply IH in H. easy.
    + erewrite <- mint_preserves_metadata in H; 
      eauto. apply IH in H. cbn in *.
      destruct (fail_if_not_minter ctx (fa2_admin prev_state)); try easy. 
      generalize dependent (token_total_supply (fa2_assets prev_state)).
      generalize dependent (ledger (fa2_assets prev_state)). 
      unfold mint_update_total_supply. 
      induction p; intros; cbn in *; try easy.
        * inversion receive_some. easy.
        * cbn in *. destruct (mint_burn_token_id a =? fa2_token_id) eqn: E2.
            -- apply N.eqb_eq in E2. subst. 
              setoid_rewrite H in receive_some. 
              rewrite update_none_is_none in receive_some. easy.
            -- destruct (FMap.find (mint_burn_token_id a) t0) eqn: E3.
                --- setoid_rewrite E3 in receive_some. 
                    setoid_rewrite <- (FMap.find_add_ne (mint_burn_token_id a) _ (n+ mint_burn_amount a) _) in H; easy.
                --- setoid_rewrite E3 in receive_some. 
                    rewrite update_none_is_none in receive_some. easy.
    + erewrite <- burn_preserves_metadata in H; eauto.
      apply IH in H. cbn in *.
      destruct (fail_if_not_minter ctx (fa2_admin prev_state)); try easy. 
      destruct (burn_update_balances p (ledger (fa2_assets prev_state))); try easy. 
      generalize dependent (token_total_supply (fa2_assets prev_state)).
      generalize dependent (ledger (fa2_assets prev_state)). 
      unfold burn_update_total_supply. induction p; intros; try easy.
        * inversion receive_some. easy.
        * destruct (mint_burn_token_id a =? fa2_token_id) eqn: E2; try easy;
          destruct (burn_update_balances (a :: p) l); try easy; cbn in *.
          -- apply N.eqb_eq in E2. subst. 
             setoid_rewrite H0 in receive_some. cbn in *. 
             rewrite burn_update_none_is_none in receive_some. easy.
          -- apply N.eqb_eq in E2. subst. 
             setoid_rewrite H0 in receive_some. cbn in *. 
             rewrite burn_update_none_is_none in receive_some. easy.
          -- destruct (FMap.find (mint_burn_token_id a) t0) eqn: E3.
            --- setoid_rewrite E3 in receive_some. 
                destruct (n <? mint_burn_amount a) eqn: E4; cbn in *.
                ---- rewrite burn_update_none_is_none in receive_some. easy.
                ---- setoid_rewrite <- (FMap.find_add_ne (mint_burn_token_id a) _ (n - mint_burn_amount a) _) in H0; try easy.
            --- setoid_rewrite E3 in receive_some. rewrite burn_update_none_is_none in receive_some. easy.
          -- destruct (FMap.find (mint_burn_token_id a) t0) eqn: E3.
            --- setoid_rewrite E3 in receive_some. destruct (n <? mint_burn_amount a) eqn: E4; cbn in *.
                ---- rewrite burn_update_none_is_none in receive_some. easy.
                ---- setoid_rewrite <- (FMap.find_add_ne (mint_burn_token_id a) _ (n - mint_burn_amount a) _) in H0; try easy.
            --- setoid_rewrite E3 in receive_some. rewrite burn_update_none_is_none in receive_some. easy.
    - intros.
      simpl in receive_some.
      destruct msg in receive_some; try easy. 
      destruct m; destruct param.
      + erewrite <- assets_endpoint_preserves_metadata in H; eauto.
        apply IH in H. 
        erewrite <- assets_endpoint_preserves_total_supply; eauto. 
      + erewrite <- assets_endpoint_preserves_metadata in H; eauto.
        apply IH in H. 
        erewrite <- assets_endpoint_preserves_total_supply; eauto. 
      + erewrite <- assets_endpoint_preserves_metadata in H; eauto.
        apply IH in H. erewrite <- assets_endpoint_preserves_total_supply; eauto.
      + destruct tokenAdmin.
        * erewrite <- set_admin_preserves_metadata in H; eauto.
          erewrite <- set_admin_preserves_total_supply; eauto.
        * erewrite <- confirm_admin_preserves_metadata in H; eauto.
          erewrite <- confirm_admin_preserves_total_supply; eauto.
        * erewrite <- pause_preserves_metadata in H; eauto.
          erewrite <- pause_preserves_total_supply; eauto.
        * erewrite <- set_minter_preserves_metadata in H; eauto.
          erewrite <- set_minter_preserves_total_supply; eauto.
      + destruct tokenMetaData. destruct (metadata_token_id =? fa2_token_id) eqn: E.
        * apply N.eqb_eq in E. subst. cbn in *. 
          unfold create_token in receive_some. cbn in *.
          destruct (FMap.find fa2_token_id (mts_token_metadata (fa2_assets prev_state))) eqn: E1; try easy.
          inversion receive_some. subst. cbn in *. 
          setoid_rewrite FMap.find_add in H. easy.
        * rewrite N.eqb_neq in E. 
          eapply create_new_token_changes_nothing_else in receive_some; eauto. 
          inversion receive_some. 
          setoid_rewrite <- H1 in H. apply IH in H. easy.
      + erewrite <- mint_preserves_metadata in H; eauto. 
        apply IH in H. cbn in *.
        destruct (fail_if_not_minter ctx (fa2_admin prev_state)); try easy. 
        generalize dependent (token_total_supply (fa2_assets prev_state)).
        generalize dependent (ledger (fa2_assets prev_state)). 
        unfold mint_update_total_supply. 
        induction p; intros; cbn in *; try easy.
        * inversion receive_some. easy.
        * cbn in *. 
        destruct (mint_burn_token_id a =? fa2_token_id) eqn: E2.
        -- apply N.eqb_eq in E2. subst. 
           setoid_rewrite H in receive_some. 
           rewrite update_none_is_none in receive_some. easy.
        -- destruct (FMap.find (mint_burn_token_id a) t0) eqn: E3.
           --- setoid_rewrite E3 in receive_some. 
               setoid_rewrite <- (FMap.find_add_ne (mint_burn_token_id a) _ (n+ mint_burn_amount a) _) in H.
               ---- eapply IHp in H; try easy.
               ---- easy.
           --- setoid_rewrite E3 in receive_some. 
               rewrite update_none_is_none in receive_some. easy.
      + erewrite <- burn_preserves_metadata in H; 
        eauto. apply IH in H. cbn in *.
        destruct (fail_if_not_minter ctx (fa2_admin prev_state)); try easy. 
        destruct (burn_update_balances p (ledger (fa2_assets prev_state))); try easy. 
        generalize dependent (token_total_supply (fa2_assets prev_state)).
        generalize dependent (ledger (fa2_assets prev_state)). 
        unfold burn_update_total_supply. 
        induction p; intros; try easy.
        * inversion receive_some. easy.
        * destruct (mint_burn_token_id a =? fa2_token_id) eqn: E2; try easy;
          destruct (burn_update_balances (a :: p) l); try easy; cbn in *.
        -- apply N.eqb_eq in E2. subst. 
           setoid_rewrite H0 in receive_some. cbn in *. 
           rewrite burn_update_none_is_none in receive_some. easy.
        -- destruct (FMap.find (mint_burn_token_id a) t0) eqn: E3.
           --- setoid_rewrite E3 in receive_some. 
               destruct (n <? mint_burn_amount a) eqn: E4; cbn in *.
               ---- rewrite burn_update_none_is_none in receive_some. easy.
               ---- apply N.eqb_eq in E2. subst. 
                    rewrite H0 in E3. easy.
           --- setoid_rewrite E3 in receive_some. 
               rewrite burn_update_none_is_none in receive_some. easy.
        -- destruct (FMap.find (mint_burn_token_id a) t0) eqn: E3.
           --- setoid_rewrite E3 in receive_some. 
               destruct (n <? mint_burn_amount a) eqn: E4; cbn in *.
                ---- rewrite burn_update_none_is_none in receive_some. easy.
                ---- setoid_rewrite <- (FMap.find_add_ne (mint_burn_token_id a) _ (n - mint_burn_amount a) _) in H0; try easy.
            --- setoid_rewrite E3 in receive_some. 
                rewrite burn_update_none_is_none in receive_some. easy.
        -- destruct (FMap.find (mint_burn_token_id a) t0) eqn: E3.
        --- setoid_rewrite E3 in receive_some. 
            destruct (n <? mint_burn_amount a) eqn: E4; cbn in *.
            ---- rewrite burn_update_none_is_none in receive_some. easy.
            ---- setoid_rewrite <- (FMap.find_add_ne (mint_burn_token_id a) _ (n - mint_burn_amount a) _) in H0; try easy.
        --- setoid_rewrite E3 in receive_some. 
            rewrite burn_update_none_is_none in receive_some. easy.
    - intros. instantiate (AddBlockFacts := fun _ _ _ _ _ _ => True).
        instantiate (DeployFacts := fun _ ctx => True).
        instantiate (CallFacts := fun _ ctx _ _ => True).
        unset_all; subst.
        destruct_chain_step; auto.
        destruct_action_eval; auto.
Qed. 

(** ** Smaller version of [no_metadata_no_supply] *)
Lemma no_metadata_no_supply_small : forall bstate caddr fa2_token_id (trace: ChainTrace empty_state bstate),
env_contracts bstate caddr = Some (FA2_contract : WeakContract) ->
exists cstate, 
    (
    FMap.find fa2_token_id cstate.(fa2_assets).(mts_token_metadata) = None ->
    FMap.find fa2_token_id cstate.(fa2_assets).(token_total_supply) = None
    ).
Proof.
    intros. apply (no_metadata_no_supply _ _ fa2_token_id trace) in H. 
    destruct H as (cstate & H). exists cstate.
    inversion H. easy.
Qed.

(** ** Not mints to a token before it is created *)
Lemma fa2_no_mint_before_token_created : forall bstate caddr fa2_token_id (trace: ChainTrace empty_state bstate),
    env_contracts bstate caddr = Some (FA2_contract : WeakContract) ->
    exists cstate inc_calls,
            contract_state bstate caddr = Some cstate /\
            incoming_calls MultiAssetParam trace caddr = Some inc_calls /\
            (
                FMap.find fa2_token_id cstate.(fa2_assets).(mts_token_metadata) = None ->
                sumZ (fun callInfo => mint_or_burn fa2_token_id callInfo.(call_msg)) inc_calls = 0%Z
            ).
Proof.
    contract_induction; intros; auto.
    - unfold callFrom in *. 
      unfold receive in receive_some. 
      simpl in *. destruct msg; try easy; destruct m; destruct param.
        -- erewrite <- assets_endpoint_preserves_metadata in H; eauto.
        -- erewrite <- assets_endpoint_preserves_metadata in H; eauto.
        -- erewrite <- assets_endpoint_preserves_metadata in H; eauto.
        -- destruct tokenAdmin.
            --- erewrite <- set_admin_preserves_metadata in H; eauto.
            --- erewrite <- confirm_admin_preserves_metadata in H; eauto.
            --- erewrite <- pause_preserves_metadata in H; eauto.
            --- erewrite <- set_minter_preserves_metadata in H; eauto.
        -- destruct tokenMetaData. 
           destruct (metadata_token_id =? fa2_token_id) eqn:E.
            --- cbn in receive_some. 
                unfold create_token in receive_some.
            apply N.eqb_eq in E. 
            subst. cbn in *.
            destruct (FMap.find fa2_token_id (mts_token_metadata (fa2_assets prev_state))); try easy.
            --- rewrite N.eqb_neq in E. 
                eapply create_new_token_changes_nothing_else in receive_some; eauto. 
                inversion receive_some.
            setoid_rewrite H1 in IH. 
            apply IH in H. cbn. 
            easy.
        -- erewrite <- mint_preserves_metadata in H; eauto. 
           apply IH in H as H2. 
           rewrite H2.
           cbn in receive_some. destruct (fail_if_not_minter ctx (fa2_admin prev_state)); try easy.
           instantiate (CallFacts := fun _ _ prev_state _ => (FMap.find fa2_token_id prev_state.(fa2_assets).(mts_token_metadata) = None ->
           FMap.find fa2_token_id prev_state.(fa2_assets).(token_total_supply) = None)). unfold CallFacts in facts.
           apply facts in H.
           unfold mint_update_total_supply in receive_some. 
           unfold mint_or_burn. 
           induction p; try easy.
           cbn in *. destruct (mint_burn_token_id a =? fa2_token_id) eqn: E2; try easy.
           apply N.eqb_eq in E2. 
           subst. 
           setoid_rewrite H in receive_some.
           rewrite update_none_is_none in receive_some. 
           easy.
        -- erewrite <- burn_preserves_metadata in H; eauto. 
           apply IH in H as H2. cbn in *.
            destruct (fail_if_not_minter ctx (fa2_admin prev_state)); try easy. 
            destruct (burn_update_balances p (ledger (fa2_assets prev_state))); try easy.
            unfold burn_update_total_supply. induction p; intros; try easy.
            cbn in *.  destruct (mint_burn_token_id a =? fa2_token_id) eqn: E2; try easy.
            apply N.eqb_eq in E2. 
            subst. 
            unfold CallFacts in facts. 
            apply facts in H. setoid_rewrite H in receive_some.
            rewrite burn_update_none_is_none in receive_some. 
            easy.
    - unfold callFrom in *. 
      unfold receive in receive_some. simpl in *. 
      destruct msg; try easy; destruct m; destruct param.
        -- erewrite <- assets_endpoint_preserves_metadata in H; eauto.
        -- erewrite <- assets_endpoint_preserves_metadata in H; eauto.
        -- erewrite <- assets_endpoint_preserves_metadata in H; eauto.
        -- destruct tokenAdmin.
            --- erewrite <- set_admin_preserves_metadata in H; eauto.
            --- erewrite <- confirm_admin_preserves_metadata in H; eauto.
            --- erewrite <- pause_preserves_metadata in H; eauto.
            --- erewrite <- set_minter_preserves_metadata in H; eauto.
        -- destruct tokenMetaData. 
           destruct (metadata_token_id =? fa2_token_id) eqn:E.
            --- cbn in receive_some. 
                unfold create_token in receive_some.
            apply N.eqb_eq in E. 
            subst. cbn in *.
            destruct (FMap.find fa2_token_id (mts_token_metadata (fa2_assets prev_state))); try easy.
            --- rewrite N.eqb_neq in E. 
                eapply create_new_token_changes_nothing_else in receive_some; eauto. 
                inversion receive_some.
            setoid_rewrite H1 in IH. 
            apply IH in H. cbn. 
            easy.
        -- erewrite <- mint_preserves_metadata in H; eauto. 
           apply IH in H as H2. 
           rewrite H2. cbn in receive_some. 
           destruct (fail_if_not_minter ctx (fa2_admin prev_state)); try easy.
           unfold CallFacts in facts. 
           apply facts in H.
           unfold mint_update_total_supply in receive_some. 
           unfold mint_or_burn. induction p; try easy.
           cbn in *. destruct (mint_burn_token_id a =? fa2_token_id) eqn: E2; try easy.
           apply N.eqb_eq in E2. 
           subst. 
           setoid_rewrite H in receive_some.
           rewrite update_none_is_none in receive_some. 
           easy.
        -- erewrite <- burn_preserves_metadata in H; eauto. 
            apply IH in H as H2. cbn in *.
            destruct (fail_if_not_minter ctx (fa2_admin prev_state)); try easy. 
            destruct (burn_update_balances p (ledger (fa2_assets prev_state))); try easy.
            unfold burn_update_total_supply. induction p; intros; try easy.
            cbn in *.  destruct (mint_burn_token_id a =? fa2_token_id) eqn: E2; try easy.
            apply N.eqb_eq in E2. 
            subst. 
            unfold CallFacts in facts. 
            apply facts in H. 
            setoid_rewrite H in receive_some.
            rewrite burn_update_none_is_none in receive_some. 
            easy.
    - instantiate (AddBlockFacts := fun _ _ _ _ _ _ => True).
        instantiate (DeployFacts := fun _ _ => True).
        unset_all; subst.
        destruct_chain_step; auto.
        destruct_action_eval; auto.
        intros state' deployed' deployed_state'.
        rewrite deployed in deployed'.
        inversion deployed'.
        subst.
        destruct from_reachable as [trace].
        clear deployed'.
        specialize no_metadata_no_supply with (fa2_token_id := fa2_token_id) as (state & state_deployed & ?); eauto.
        rewrite state_deployed in deployed_state'. 
        inversion deployed_state'. 
        subst. 
        easy.
Qed.
End FA2_Multi_Asset.