Require Import Storage.
Require Import ZArith.
Require Import Fees.
Require Import Fees_Interface.
Require Import Blockchain.
Require Import Unwrap.
Require Import ContractAdmin.
Require Import Monads.
Require Import RecordUpdate.
Require Import Tokens_Lib.
Require Import ContractCommon.
Require Import Governance_Interface.
Require Import Governance.
Require Import Oracle_Interface.
Require Import Oracle.
Require Import Signer_Interface.
Require Import Signer.
Require Import Signer_Ops_Interface.
Require Import SignerOps.
Require Import Serializable.
Require Import Ethereum_Lib.
Require Import Containers.
Require Import String.
Require Import List.
Require Import Types.
From ConCert.Examples.FA2 Require Import FA2Interface.
From ConCert.Execution Require Import InterContractCommunication.
From ConCert.Utils Require Import Extras.
Require Import FA2_Multi_Asset.
Require Import FA2InterfaceOwn.
Import ListNotations.
Require Import Fees_Lib.
Require Import TokenAdmin.
Require Import FA2Types.

Section Main.

Context {BaseTypes : ChainBase}.
Set Nonrecursive Elimination Schemes.
Open Scope N_scope.

Inductive EntryPoints :=
    | Fees (fees_entrypoints : WithdrawalEntrypoint)
    | Unwrap (unwrap_entrypoints : UnwrapEntrypoints)
    | ContractAdmin (contract_admin_entrypoints : ContractAdminEntrypoints)
    | Governance (governance_entrypoints : GovernanceEntrypoints)
    | Oracle (oracle_entrypoints : OracleEntrypoint)
    | Signer (signer_entrypoints : SignerEntrypoints)
    | Signer_Ops (signer_ops_entrypoints : SignerOpsEntrypoint)
.

Record Setup := {
    quorum_contract : Address;
    meta_data_uri : N;
    setup_tokens : list EthAddress;
    nft_contracts : FMap EthAddress Address;
    fa2_contract : Address
}.

Global Instance EntryPoints_serializable : Serializable EntryPoints :=
    Derive Serializable EntryPoints_rect<Fees, Unwrap, ContractAdmin, Governance, Oracle, Signer, Signer_Ops>.

Global Instance Setup_serializable : Serializable Setup :=
    Derive Serializable Setup_rect<Build_Setup>.

Definition fail_if_paused (s : ContractAdminStorage) : option unit :=
    throwIf (s.(paused)).

Definition main (ctx: ContractCallContext) (p: EntryPoints) (s : State) : option ReturnType :=
    match p with
    | Signer p =>
        do _ <- fail_if_not_signer ctx s.(admin) ;
        do _ <- fail_if_paused s.(admin) ; 
        signer_main ctx p s
    | Unwrap p =>
        do _ <- fail_if_paused s.(admin);
        unwrap_main ctx p s
    | ContractAdmin p =>
        do _ <- fail_if_amount ctx;
        do res <- contract_admin_main ctx p s.(admin);
        Some (s<|admin:= snd res|>, fst res)
    | Governance p => 
        do _ <- fail_if_amount ctx ;
        do _ <- fail_if_not_governance ctx s.(governance) ;
        do res <- governance_main ctx p s.(governance) ;
        Some (s<|governance := snd res|>, fst res)
    | Fees p => 
        do _ <- fail_if_amount ctx;
        fees_main ctx s p
    | Oracle p =>
        do _ <- fail_if_amount ctx ;
        do _ <- fail_if_not_oracle ctx s.(admin) ;
        oracle_main ctx p s
    | Signer_Ops p => 
        do _ <- fail_if_amount ctx ;
        do _ <- fail_if_not_signer ctx s.(admin) ; 
        signer_ops_main ctx p s
    end.

Definition minter_receive (chain : Chain) (ctx : ContractCallContext) (state : State) (msg_opt : option EntryPoints) : option ReturnType :=
    do msg <- msg_opt ;
    main ctx msg state.

Definition minter_init (chain : Chain) (ctx : ContractCallContext) (setup : Setup) : option State :=
    let meta := FMap.update EmptyString (Some setup.(meta_data_uri)) FMap.empty in
    let fungible_tokens := fold_left (
        fun (acc : (N * FMap EthAddress TokenAddress)) (eth_contract : EthAddress) =>
        ((fst acc) + 1, FMap.update eth_contract (Some (setup.(fa2_contract), fst acc)) (snd acc))
    ) setup.(setup_tokens) (0, FMap.empty) in
    Some {| 
        admin := {| 
            administrator := ctx.(ctx_from);
            pending_admin := None;
            oracle := setup.(quorum_contract);
            signer := setup.(quorum_contract);
            paused := false
        |};
        assets := {|
            erc20tokens := snd fungible_tokens;
            erc721tokens := setup.(nft_contracts);
            mints := FMap.empty
        |};
        fees := {|
            fees_storage_signers := FMap.empty;
            fees_storage_tokens := FMap.empty;
            fees_storage_xtz := FMap.empty
        |};
        governance := {|
            contract := ctx.(ctx_from);
            staking_address := ctx.(ctx_from);
            dev_pool_address := ctx.(ctx_from);
            erc20_wrapping_fees := 15;
            erc20_unwrapping_fees := 15;
            erc721_wrapping_fees := 500000;
            erc721_unwrapping_fees := 500000;
            fees_share_rec := {|
                dev_pool := 10;
                signers := 50;
                staking := 40
            |}
        |};
        storage_metadata := meta
    |}.

(* The minter contract *)
Definition minter_contract : Contract Setup EntryPoints State :=
    build_contract minter_init minter_receive.

(**----------------- Signer Proofs -----------------**)
Lemma mint_erc20_functionally_correct {chain ctx prev_state next_state erc20Address event_id
    owner amount acts token_address v new_v n feesVal} : 
    minter_receive chain ctx prev_state (Some (Signer 
        (Mint_erc20 {|
            erc20 := erc20Address;
            event_id_erc20 := event_id;
            owner_erc20 := owner;
            amount_erc20 :=amount
        |}))) = Some (next_state, acts) ->
    prev_state.(governance).(erc20_wrapping_fees) = n ->
    FMap.find erc20Address prev_state.(assets).(erc20tokens) = Some token_address ->
    FMap.find (ctx.(ctx_contract_address), token_address) prev_state.(fees).(fees_storage_tokens) = Some v ->
    FMap.find (ctx.(ctx_contract_address), token_address) next_state.(fees).(fees_storage_tokens) = Some new_v ->
    feesVal = (amount * n / 10000) ->
    v + feesVal = new_v /\
    (* Amount to mint to owner *)
    let mintToOwner := {|
        mint_burn_owner := owner;
        mint_burn_token_id := snd token_address;
        mint_burn_amount := amount - feesVal
    |} in
    (* Fees to mint to contract itself *)
    let mintFees := {|
        mint_burn_owner := ctx.(ctx_contract_address);
        mint_burn_token_id := snd token_address;
        mint_burn_amount := feesVal
    |} in
    (* If no fees to mint, dont include it in the actions *)
    if 0 <?  feesVal then
      acts = [act_call (fst token_address) 0 (serialize (MintTokens [mintToOwner ; mintFees]))]
    else 
     acts = [act_call (fst token_address) 0 (serialize (MintTokens [mintToOwner]))].
Proof.
    intros. 
    generalize dependent H4. 
    contract_simpl minter_receive minter_init. 
    intro. cbn in *. 
    split.
    -   unfold get_fa2_token_id in H9. 
        setoid_rewrite H9 in H1. 
        inversion H1. 
        subst. 
        unfold Fees_Lib.token_balance in H2.
        setoid_rewrite FMap.find_add in H3. 
        unfold Fees_Lib.token_balance in H3.
        setoid_rewrite H2 in H3. 
        cbn in *. 
        unfold Fees_Lib.bps_of in H3. 
        now inversion H3.
    -   unfold get_fa2_token_id in H9. 
        setoid_rewrite H9 in H1. 
        inversion H1. 
        destruct feesVal;
        unfold bps_of in *; 
        rewrite <- H8; now cbn.
Qed.

Lemma add_erc20_functionally_correct {chain ctx prev_state next_state eth_contract token_address acts ta} : 
    minter_receive chain ctx prev_state (Some (Signer 
        (Add_erc20 {|
            eth_contract_erc20 := eth_contract;
            token_address := token_address;
        |}))) = Some (next_state, acts) ->
    FMap.find eth_contract next_state.(assets).(erc20tokens) = Some ta ->
    ta = token_address.
Proof.
    intros. contract_simpl minter_receive minter_init. cbn in *. setoid_rewrite FMap.find_add in H0. easy.
Qed.

Lemma mint_erc721_functionally_correct {chain ctx prev_state next_state erc721Address event_id
    owner amount acts token_address v new_v n token_id contract_address } : 
    minter_receive chain ctx prev_state (Some (Signer 
        (Mint_erc721 {|
            erc721 := erc721Address;
            event_id_erc721 := event_id;
            owner_erc721 := owner;
            token_id_erc721 := token_id
        |}))) = Some (next_state, acts) ->
    ctx.(ctx_amount) = amount ->
    prev_state.(governance).(erc721_wrapping_fees) = n ->
    FMap.find erc721Address prev_state.(assets).(erc721tokens) = Some token_address ->
    ctx.(ctx_contract_address) = contract_address ->
    FMap.find contract_address prev_state.(fees).(fees_storage_xtz) = Some v ->
    FMap.find contract_address next_state.(fees).(fees_storage_xtz) = Some new_v ->
    v + (Z.to_N amount) = new_v /\
    (*Amount to mint to owner*)
    let mintBurnToOwner := {|
        mint_burn_owner := owner;
        mint_burn_token_id := token_id;
        mint_burn_amount := 1
    |} in
    acts = [act_call token_address 0 (serialize (MintTokens [mintBurnToOwner]))].
Proof.
    intros. contract_simpl minter_receive minter_init. cbn in *. split.
    - setoid_rewrite FMap.find_add in H5. setoid_rewrite H4 in H5. inversion H5. easy.
    - unfold get_nft_contract in H10. easy.
Qed.

Lemma add_erc721_functionally_correct {chain ctx prev_state next_state eth_contract token_contract acts tc} : 
    minter_receive chain ctx prev_state (Some (Signer 
        (Add_erc721 {|
            eth_contract_erc721 := eth_contract;
            token_contract := token_contract;
        |}))) = Some (next_state, acts) ->
    FMap.find eth_contract next_state.(assets).(erc721tokens) = Some tc ->
    tc = token_contract.
Proof.
    intros. contract_simpl minter_receive minter_init. cbn in *. setoid_rewrite FMap.find_add in H0. easy.
Qed.

(**----------------- ContractAdmin Proofs -----------------**)
Lemma set_administrator_correct {chain ctx prev_state next_state n} : 
    minter_receive chain ctx prev_state (Some (ContractAdmin (SetAdministrator n))) = Some (next_state, []) ->
    next_state.(admin).(administrator) = n.
Proof.
    intros. contract_simpl minter_receive minter_init. easy.
Qed.

Lemma set_signer_correct {chain ctx prev_state next_state n} : 
    minter_receive chain ctx prev_state (Some (ContractAdmin (SetSigner n))) = Some (next_state, []) ->
    next_state.(admin).(signer) = n.
Proof.
    intros. contract_simpl minter_receive minter_init. easy.
Qed.

Lemma set_oracle_correct {chain ctx prev_state next_state n} : 
    minter_receive chain ctx prev_state (Some (ContractAdmin (SetOracle n))) = Some (next_state, []) ->
    next_state.(admin).(oracle) = n.
Proof.
    intros. contract_simpl minter_receive minter_init. easy.
Qed.

Lemma confirm_new_admin_correct {chain ctx addr prev_state next_state} :
    prev_state.(admin).(pending_admin) = Some addr ->
    minter_receive chain ctx prev_state (Some (ContractAdmin (ConfirmMinterAdmin))) = Some (next_state, []) ->
    next_state.(admin).(pending_admin) = None ->
    next_state.(admin).(administrator) = addr.
Proof.
    intros. contract_simpl minter_receive minter_init. cbn in *. unfold confirm_new_minter_admin in H3.
    rewrite H in H3. generalize dependent H3. destruct_address_eq; intros; cbn in *; try easy.
    rewrite <- e in H3. inversion H3. easy.
Qed.

Lemma pause_contract_correct {chain ctx prev_state next_state b} :
    minter_receive chain ctx prev_state (Some (ContractAdmin (PauseContract b))) = Some (next_state, []) ->
    next_state.(admin).(paused) = b.
Proof.
    intros. contract_simpl minter_receive minter_init. easy.
Qed.

(**----------------- Fees Proofs -----------------**)
Lemma Withdraw_all_tokens_is_functionally_correct {chain ctx prev_state p next_state ops token_id amount} :
    minter_receive chain ctx prev_state (Some (Fees (Withdraw_all_tokens p))) = Some (next_state, ops) ->
    p.(wtp_tokens) = [token_id] ->
    token_balance prev_state.(fees).(fees_storage_tokens) ctx.(ctx_from) (p.(wtp_fa2_tokens), token_id) = amount ->
    token_balance next_state.(fees).(fees_storage_tokens) ctx.(ctx_from) (p.(wtp_fa2_tokens), token_id) = 0 /\
    (if amount =? 0 then ops = [] else 
    ops = [act_call ctx.(ctx_contract_address) (N_to_amount 0) (serialize (
        {|
            from_ := p.(wtp_fa2_tokens);
            txs := [{|
                to_ := ctx.(ctx_from);
                dst_token_id := token_id;
                amount := amount
            |}]
        |}
    ))]).
Proof.
    intros. contract_simpl minter_receive minter_init. unfold generate_tokens_transfer in H.
    unfold generate_tx_destinations in H. rewrite H0 in H. cbn in H. rewrite H1 in H. 
    destruct (amount =? 0) eqn:E in H; cbn in H; inversion H; split; 
    try rewrite N.eqb_eq in E; try rewrite E; try easy.
        + cbn. rewrite E in H1. apply H1. 
        + unfold token_balance. setoid_rewrite FMap.find_remove. reflexivity.
Qed.

Lemma Withdraw_tokens_is_functionally_correct {chain ctx prev_state p next_state ops amount} :
    minter_receive chain ctx prev_state (Some (Fees (Withdraw_token p))) = Some (next_state, ops) ->
    token_balance prev_state.(fees).(fees_storage_tokens) ctx.(ctx_from) (p.(fa2_token), p.(wtp_token_id)) = amount ->
    token_balance next_state.(fees).(fees_storage_tokens) ctx.(ctx_from) (p.(fa2_token), p.(wtp_token_id)) = amount - p.(wtp_amount) /\
    ops = [act_call ctx.(ctx_contract_address) (N_to_amount 0) (serialize (
        {|
            from_ := p.(fa2_token);
            txs := [{|
                to_ := ctx.(ctx_from);
                dst_token_id := p.(wtp_token_id);
                amount := p.(wtp_amount)
            |}]
        |}))].
Proof.
    intros. contract_simpl minter_receive minter_init. split. 
    - destruct (token_balance (fees_storage_tokens (fees prev_state)) (ctx_from ctx) (fa2_token p, wtp_token_id p) - wtp_amount p) eqn:E; cbn.
        + unfold token_balance. setoid_rewrite FMap.find_remove. reflexivity.
        + unfold token_balance. setoid_rewrite FMap.find_add. reflexivity.
    - unfold transfer_operation. cbn. reflexivity.
Qed.

Lemma Withdraw_all_xtz_is_functionally_correct {chain ctx prev_state next_state ops amount} :
    minter_receive chain ctx prev_state (Some (Fees (Withdraw_all_xtz))) = Some (next_state, ops) ->
    xtz_balance prev_state.(fees).(fees_storage_xtz) ctx.(ctx_from) = amount ->
    xtz_balance next_state.(fees).(fees_storage_xtz) ctx.(ctx_from) = 0 /\
    (if amount =? 0 then ops = [] else 
        ops = [act_transfer ctx.(ctx_from) (N_to_amount amount)]). 
Proof.
    intros. contract_simpl minter_receive minter_init. 
    destruct (xtz_balance (fees_storage_xtz (fees prev_state)) (ctx_from ctx) =? 0) eqn:E. 
    - cbn. inversion H2. cbn. rewrite N.eqb_eq in E; try easy.
    - cbn. destruct (throwIf (address_is_contract (ctx_from ctx))); try easy. inversion H2. cbn.
      rewrite N.sub_diag. cbn. unfold xtz_balance. setoid_rewrite FMap.find_remove; try easy.
Qed.

Lemma Withdraw_xtz_is_functionally_correct {chain ctx prev_state next_state ops amount n} :
    minter_receive chain ctx prev_state (Some (Fees (Withdraw_xtz n))) = Some (next_state, ops) ->
    xtz_balance prev_state.(fees).(fees_storage_xtz) ctx.(ctx_from) = amount ->
    xtz_balance next_state.(fees).(fees_storage_xtz) ctx.(ctx_from) = amount-n /\
    (if amount =? 0 then ops = [] else 
        ops = [act_transfer ctx.(ctx_from) (N_to_amount n)]). 
Proof.
    intros. contract_simpl minter_receive minter_init.
    split.
    - destruct (xtz_balance (fees_storage_xtz (fees prev_state)) (ctx_from ctx)) eqn:E. 
        + cbn in H2. inversion H2. cbn. apply E.
        + cbn in *. destruct (throwIf (address_is_contract (ctx_from ctx))); 
          try easy. inversion H2. cbn. unfold xtz_balance. destruct n0 eqn:E2.
            * cbn. setoid_rewrite FMap.find_add. reflexivity.
            * destruct (Pos.sub_mask p0 p1); cbn.
                -- setoid_rewrite FMap.find_remove. reflexivity.
                -- setoid_rewrite FMap.find_add.  reflexivity.
                -- setoid_rewrite FMap.find_remove. reflexivity.
    - destruct (xtz_balance (fees_storage_xtz (fees prev_state)) (ctx_from ctx) =? 0) eqn:E in H2.
        + inversion H2. now rewrite E.
        + destruct (throwIf (address_is_contract (ctx_from ctx))); try easy. inversion H2. now rewrite E.
Qed.

(**----------------- Unwrap Proofs -----------------**)

(* Fees ledger should be updated correctly and correct burn and mint calls should be made *)
Lemma unwrap_erc20_functionally_correct {chain ctx prev_state next_state eth_address amount fees_amount erc20_dest acts token_address v new_v} :
    (minter_receive chain ctx prev_state (Some (Unwrap (unwrap_erc20_entrypoint ({|
        erc_20 := eth_address;
        up_amount := amount;
        up_fees := fees_amount;
        up_erc20_destination := erc20_dest
    |})))) = Some (next_state, acts)) ->
    get_fa2_token_id eth_address prev_state.(assets).(erc20tokens) = Some token_address ->
    ((FMap.find (ctx.(ctx_contract_address), token_address) (prev_state.(fees).(fees_storage_tokens)) = Some v ->
    FMap.find (ctx.(ctx_contract_address), token_address) (next_state.(fees).(fees_storage_tokens)) = Some new_v ->
    new_v = fees_amount + v)
    /\
    (* Burn call for burning the amount + fees from the caller of the unwrap *)
    (let burnTokensParams := {|
            mint_burn_owner:= ctx.(ctx_from);
            mint_burn_token_id := snd token_address;
            mint_burn_amount := amount + fees_amount
    |} in
    (* Mint call for minting fees to the contract itself *)
    let mintTokensParams :=  {|
            mint_burn_owner := ctx.(ctx_contract_address);
            mint_burn_token_id := snd token_address;
            mint_burn_amount := fees_amount
    |} in
    let burn := act_call (fst token_address) 0 (serialize (BurnTokens [burnTokensParams])) in
    (* If fees are zero no call to mint fees should be made *)
    if fees_amount =? 0
    then acts = [burn]
    else acts = [burn] ++ [act_call (fst token_address) 0 (serialize (MintTokens [mintTokensParams]))])).
Proof.
    intros. contract_simpl minter_receive minter_init. unfold unwrap_erc20 in H. cbn in *.
    setoid_rewrite H0 in H. split.
    (* Fees ledger correct *)
    - intros. cbn in *. unfold Fees_Lib.token_balance in H. rewrite H3 in H. destruct (token_address) eqn:E2 in H.
    destruct (Fees_Lib.check_fees_high_enough fees_amount (Fees_Lib.bps_of amount (erc20_unwrapping_fees (governance prev_state)))) in H; try easy.
    inversion H. rewrite <- H6 in H4. cbn in H4. rewrite E2 in H4. setoid_rewrite FMap.find_add in H4.
    inversion H2. easy.
    (* Acts correct *)
    - intros. destruct (token_address) eqn:E2 in H. destruct (Fees_Lib.check_fees_high_enough fees_amount (Fees_Lib.bps_of amount (erc20_unwrapping_fees (governance prev_state)))) in H; try easy. 
    destruct fees_amount eqn:E3; cbn in *; 
    try inversion H; rewrite E2; easy. 
Qed.

(* Fees ledger should be updated correctly and correct burn and mint calls should be made *)
Lemma unwrap_erc721_functionally_correct {chain ctx prev_state next_state eth_address erc721_dest acts token_id token_addr v new_v} :
    minter_receive chain ctx prev_state (Some (Unwrap (unwrap_erc721_entrypoint ({|
        erc_721 := eth_address;
        up_token_id := token_id;
        up_erc721_destination := erc721_dest
    |})))) = Some (next_state, acts) ->
    get_nft_contract eth_address prev_state.(assets).(erc721tokens) = Some token_addr ->
    ((FMap.find ctx.(ctx_contract_address) (prev_state.(fees).(fees_storage_xtz)) = Some v ->
    FMap.find ctx.(ctx_contract_address) (next_state.(fees).(fees_storage_xtz)) = Some new_v ->
    new_v = v + (Z.to_N (ctx.(ctx_amount))))
    /\
    (* Call to burn the NFT from the owner *)
    let burnTokensParams := {|
            mint_burn_owner := ctx.(ctx_from);
            mint_burn_token_id := token_id;
            mint_burn_amount := 1
        |} in
    let burn := act_call token_addr 0 (serialize (BurnTokens [burnTokensParams])) in
    acts = [burn]
    ).
Proof.
    intros. contract_simpl minter_receive minter_init. cbn in *.
    setoid_rewrite FMap.find_add. split. 
    - intros. rewrite H in H4. inversion H4. easy.
    - easy.
Qed.

(* UNWRAP SAFETY PROPERTIES *)
(* If fees are below required. Unwrap should fail *)
Lemma unwrap_erc20_fees_below_min {chain ctx prev_state eth_address amount fees_amount erc20_dest} :
    fees_amount < Fees_Lib.bps_of amount prev_state.(governance).(erc20_unwrapping_fees) ->
    minter_receive chain ctx prev_state (Some (Unwrap (unwrap_erc20_entrypoint ({|
        erc_20 := eth_address;
        up_amount := amount;
        up_fees := fees_amount;
        up_erc20_destination := erc20_dest
    |})))) = None.
Proof.
    intros. contract_simpl minter_receive minter_init. destruct (fail_if_paused (admin prev_state)); try easy.
    destruct (fail_if_amount ctx); try easy. unfold unwrap_erc20. cbn in *. destruct (get_fa2_token_id eth_address (erc20tokens (assets prev_state))); try easy.
    destruct t. unfold Fees_Lib.check_fees_high_enough. unfold throwIf. rewrite <- N.ltb_lt in H. rewrite H. reflexivity.
Qed.
    
(* If fees are below required. Unwrap should fail *)
Lemma unwrap_erc721_fees_below_min {chain ctx prev_state eth_address erc721_dest token_id} :
    Z.to_N ctx.(ctx_amount) < prev_state.(governance).(erc721_unwrapping_fees) ->
    minter_receive chain ctx prev_state (Some (Unwrap (unwrap_erc721_entrypoint ({|
        erc_721 := eth_address;
        up_token_id := token_id;
        up_erc721_destination := erc721_dest
    |})))) = None.
Proof.
    intros. contract_simpl minter_receive minter_init. destruct (fail_if_paused (admin prev_state)); try easy.
    unfold Fees_Lib.check_nft_fees_high_enough. unfold throwIf. rewrite <- N.ltb_lt in H. rewrite H. reflexivity.
Qed.


(**----------------- SignerOps Proofs -----------------**)

(* The new signer gets updated correctly *)
Lemma signer_ops_functionally_correct {chain ctx prev_state next_state signer addr} :
    minter_receive chain ctx prev_state (Some (Signer_Ops (set_payment_address {| sparam_signer:= signer; payment_address:=addr |}))) = Some(next_state, []) ->
    FMap.find signer next_state.(fees).(fees_storage_signers) = Some addr.
Proof.
    intros. contract_simpl minter_receive minter_init. cbn.
    rewrite FMap.find_add. reflexivity.
Qed.

(**----------------- Minter FA2 Safety Proofs -----------------**)
(* 
Definition sum_tx (txs : list MintBurnTx) (id : token_id): Z :=
    fold_left 
    (fun (acc : Z) (tx : MintBurnTx) => 
        (
            if tx.(mint_burn_token_id) =? id
            then (acc + (Z.of_N tx.(mint_burn_amount)))%Z
            else 0%Z
        )
        )
    txs 0%Z.

Definition mint_or_burn (msg : FA2_Multi_Asset.MultiAssetParam) (id : token_id) : Z :=
    match msg with
    | Tokens (param) =>
        match param with 
        | MintTokens mint_param => sum_tx mint_param id
        | BurnTokens mint_param => (sum_tx mint_param id) * (-1)
        end
    | _ => 0
    end.

Definition mint_or_burn_tx (id : token_id) (tx : Tx) : Z :=
    match tx.(tx_body) with
    | tx_call (Some msg_serialized) =>
    match @deserialize MultiAssetParam MultiAssetParam_serializable msg_serialized with
    | Some msg => mint_or_burn msg id
    | _ => 0
    end
    | _ => 0
    end.

Lemma minter_correct : forall bstate caddr_main erc20 fa2_address fa2_token_id (trace : ChainTrace empty_state bstate),
    env_contracts bstate caddr_main = Some (minter_contract : WeakContract) ->
    exists (state_main : State) depinfo_main,
        contract_state bstate caddr_main = Some state_main /\
        deployment_info Setup trace caddr_main = Some depinfo_main /\
        (
        get_fa2_token_id erc20 state_main.(assets).(erc20tokens) = Some (fa2_address, fa2_token_id) ->
        filter (actTo fa2_address) (outgoing_acts bstate caddr_main) = [] ->
        exists total,
        sumZ (mint_or_burn_tx fa2_token_id) (filter (txCallTo fa2_address) (outgoing_txs trace caddr_main)) = total
        ).
Proof.
    contract_induction;
    intros; auto.
    -  exists 0%Z. easy.
    - eexists. Admitted.


Lemma fa2_correct : forall bstate fa2_address fa2_token_id total_supply (trace: ChainTrace empty_state bstate),
    env_contracts bstate fa2_address = Some (FA2_contract : WeakContract) ->
    exists (state_fa2 : MultiAssetStorage) depinfo_fa2,
        contract_state bstate fa2_address = Some state_fa2 /\
        deployment_info FA2_Multi_Asset.Setup trace fa2_address = Some depinfo_fa2 /\ 
        (
        FMap.find fa2_token_id state_fa2.(fa2_assets).(token_total_supply) = Some total_supply ->
        sumZ (mint_or_burn_tx fa2_token_id) (incoming_txs trace fa2_address) = Z.of_N total_supply
        ).
Proof.
    contract_induction.
    

Lemma fa2_correct : forall bstate fa2_address (trace : ChainTrace empty_state bstate),
    env_contracts bstate fa2_address = Some (FA2_contract : WeakContract) ->
    exists (state_fa2 : MultiAssetStorage) depinfo_fa2,
        contract_state bstate fa2_address = Some state_fa2 /\
        deployment_info FA2_Multi_Asset.Setup trace fa2_address = Some depinfo_fa2.
Proof.
Admitted.
    
    

Lemma minter_fa2_synced_spec : forall bstate caddr_main erc20 fa2_address fa2_token_id token_supply (trace : ChainTrace empty_state bstate),
    env_contracts bstate caddr_main = Some (minter_contract : WeakContract) ->
    env_contracts bstate fa2_address = Some (FA2_contract : WeakContract) ->
    exists state_main state_fa2 depinfo_main depinfo_lqt,
    contract_state bstate caddr_main = Some state_main /\
    contract_state bstate fa2_address = Some (state_fa2 : MultiAssetStorage) /\
    deployment_info Setup trace caddr_main = Some depinfo_main /\
    deployment_info FA2_Multi_Asset.Setup trace fa2_address = Some depinfo_lqt /\
    (get_fa2_token_id erc20 state_main.(assets).(erc20tokens) = Some (fa2_address, fa2_token_id) ->
    state_fa2.(fa2_admin).(tas_minter) = caddr_main ->
    filter (actTo fa2_address) (outgoing_acts bstate caddr_main) = [] ->
    FMap.find fa2_token_id state_fa2.(fa2_assets).(token_total_supply) = Some token_supply ->
    sumZ (mint_or_burn_tx fa2_token_id) (outgoing_txs trace caddr_main) = Z.of_N token_supply
    ).
Proof.
    intros ? ? ? ? ? ? ? minter_deployed fa2_deployed.
    apply (minter_correct _ _ trace) in minter_deployed as minter.
    destruct minter as (state_main & depinfo_main & deployed_state_main & dep_info_main).
    apply (fa2_correct _ _ trace) in fa2_deployed as fa2.
    destruct fa2 as (state_fa2 & depinfo_fa2 & deployed_state_fa2 & dep_info_fa2).
    do 4 eexists.
    repeat split; eauto.
    intros. unfold mint_or_burn_tx.



    

    
    
     *)


End Main. 