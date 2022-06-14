(** * The main entrypoint contract of the Minter Contract *)
(** This file calls all sub parts of the minter contract, also located in this folder.
    All proofs for the sub parts(Fees, Contract Admin, Signer, SignerOps, Governance, Oracle) of the contracts are located in this file aswell
    The file this file has been translated from can be found here:
    https://github.com/bender-labs/wrap-tz-contracts/blob/1655949e61b05a1c25cc00dcb8c1da9d91799f31/ligo/minter/main.mligo
*)

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
Require Import Signer_Ops.
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
Require Import FA2Interface_Wrap.
Import ListNotations.
Require Import Fees_Lib.
Require Import TokenAdmin.
Require Import FA2Types.

Section Main.
Context {BaseTypes : ChainBase}.
Set Nonrecursive Elimination Schemes.
Open Scope N_scope.

(** ** The Main Entrypoints of the Minter Contract*)
Inductive EntryPoints :=
    | Fees (fees_entrypoints : WithdrawalEntrypoint)
    | Unwrap (unwrap_entrypoints : UnwrapEntrypoints)
    | ContractAdmin (contract_admin_entrypoints : ContractAdminEntrypoints)
    | Governance (governance_entrypoints : GovernanceEntrypoints)
    | Oracle (oracle_entrypoints : OracleEntrypoint)
    | Signer (signer_entrypoints : SignerEntrypoints)
    | Signer_Ops (signer_ops_entrypoints : SignerOpsEntrypoint)
.

(** ** The Class needed for init to be run *)
Record Setup := {
    quorum_contract : Address;
    meta_data_uri : N;
    setup_tokens : list EthAddress;
    nft_contracts : FMap EthAddress Address;
    fa2_contract : Address
}.

(* begin hide *)
Global Instance EntryPoints_serializable : Serializable EntryPoints :=
    Derive Serializable EntryPoints_rect<Fees, Unwrap, ContractAdmin, Governance, Oracle, Signer, Signer_Ops>.

Global Instance Setup_serializable : Serializable Setup :=
    Derive Serializable Setup_rect<Build_Setup>.

(* end hide *)

(** ** Function to fail if the minter is paused *)
Definition fail_if_paused (s : ContractAdminStorage) : option unit :=
    throwIf (s.(paused)).

(** ** The Main entrypoint function for the whole Minter Contract *)
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

(** ** Receive function used to connect the main function to the context state*)
Definition minter_receive (chain : Chain) (ctx : ContractCallContext) (state : State) (msg_opt : option EntryPoints) : option ReturnType :=
    do msg <- msg_opt ;
    main ctx msg state.

(** ** The init function run when initializing or deploying the Minter Contract*)
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

(** ** The type definition of the minter contract *)
Definition minter_contract : Contract Setup EntryPoints State :=
    build_contract minter_init minter_receive.

(** * Signer Proofs *)
(** All of the Signer proofs are in this section, the definition of the contract part can be found in the Signer.v and Signer_Interface.v *)

(** ** Functional correctness of minting erc20 functionality *)
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

(** ** Functional correctness of adding new erc20 token *)
Lemma add_erc20_functionally_correct {chain ctx prev_state next_state eth_contract token_address acts ta} : 
    minter_receive chain ctx prev_state (Some (Signer 
        (Add_erc20 {|
            eth_contract_erc20 := eth_contract;
            token_address := token_address;
        |}))) = Some (next_state, acts) ->
    FMap.find eth_contract next_state.(assets).(erc20tokens) = Some ta ->
    ta = token_address.
Proof.
    intros. 
    contract_simpl minter_receive minter_init. 
    setoid_rewrite FMap.find_add in H0. 
    cbn in H0. easy.
Qed.

(** ** Functional correctness of minting erc 721 *)
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
    intros. 
    contract_simpl minter_receive minter_init. 
    split.
    - setoid_rewrite FMap.find_add in H5. 
      setoid_rewrite H4 in H5. 
      inversion H5. 
      easy.
    - unfold get_nft_contract in H10. 
      easy.
Qed.

(** ** Functional correctness of adding erc721 tokens *)
Lemma add_erc721_functionally_correct {chain ctx prev_state next_state eth_contract token_contract acts tc} : 
    minter_receive chain ctx prev_state (Some (Signer 
        (Add_erc721 {|
            eth_contract_erc721 := eth_contract;
            token_contract := token_contract;
        |}))) = Some (next_state, acts) ->
    FMap.find eth_contract next_state.(assets).(erc721tokens) = Some tc ->
    tc = token_contract.
Proof.
    intros. 
    contract_simpl minter_receive minter_init. 
    setoid_rewrite FMap.find_add in H0. 
    cbn in H0. 
    easy.
Qed.

(** * Contract Admin Proofs *)
(** All of the contract admin proofs, the definitions can be found in ContractAdmin.v *)
(** ** Set administrator correct *)
Lemma set_administrator_correct {chain ctx prev_state next_state n} : 
    minter_receive chain ctx prev_state (Some (ContractAdmin (SetAdministrator n))) = Some (next_state, []) ->
    next_state.(admin).(administrator) = n.
Proof.
    intros. 
    contract_simpl minter_receive minter_init. 
    easy.
Qed.

(** ** Set signer correct *)
Lemma set_signer_correct {chain ctx prev_state next_state n} : 
    minter_receive chain ctx prev_state (Some (ContractAdmin (SetSigner n))) = Some (next_state, []) ->
    next_state.(admin).(signer) = n.
Proof.
    intros. 
    contract_simpl minter_receive minter_init. 
    easy.
Qed.

(** ** Set Oracle correct *)
Lemma set_oracle_correct {chain ctx prev_state next_state n} : 
    minter_receive chain ctx prev_state (Some (ContractAdmin (SetOracle n))) = Some (next_state, []) ->
    next_state.(admin).(oracle) = n.
Proof.
    intros. 
    contract_simpl minter_receive minter_init. 
    easy.
Qed.

(** ** Confirm new admin correct *)
Lemma confirm_new_admin_correct {chain ctx addr prev_state next_state} :
    prev_state.(admin).(pending_admin) = Some addr ->
    minter_receive chain ctx prev_state (Some (ContractAdmin (ConfirmMinterAdmin))) = Some (next_state, []) ->
    next_state.(admin).(pending_admin) = None ->
    next_state.(admin).(administrator) = addr.
Proof.
    intros. 
    contract_simpl minter_receive minter_init. 
    unfold confirm_new_minter_admin in H3.
    rewrite H in H3. 
    generalize dependent H3. 
    destruct_address_eq; intros; cbn in *; try easy.
    rewrite <- e in H3. 
    inversion H3. 
    easy.
Qed.

(** ** Pause contract correct *)
Lemma pause_contract_correct {chain ctx prev_state next_state b} :
    minter_receive chain ctx prev_state (Some (ContractAdmin (PauseContract b))) = Some (next_state, []) ->
    next_state.(admin).(paused) = b.
Proof.
    intros. 
    contract_simpl minter_receive minter_init.
    easy.
Qed.

(** * Fees proofs *)
(** All of the fees proofs, the definition of the functionality can be found in the Fees_Interface.v Fees_Lib.v Fees.v*)

(** ** Withdraw all tokens correct *)
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
    intros. 
    contract_simpl minter_receive minter_init.
    unfold generate_tokens_transfer in H.
    unfold generate_tx_destinations in H. 
    rewrite H0 in H. cbn in H. 
    rewrite H1 in H. 
    destruct (amount =? 0) eqn:E in H; inversion H; split; 
    try rewrite N.eqb_eq in E; try rewrite E; try easy.
        + rewrite E in H1.
          apply H1. 
        + unfold token_balance. 
          setoid_rewrite FMap.find_remove. 
          reflexivity.
Qed.

(** ** Withdraw tokens correct *)
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
    intros. 
    contract_simpl minter_receive minter_init.
    split. 
    - destruct (token_balance (fees_storage_tokens (fees prev_state)) (ctx_from ctx) (fa2_token p, wtp_token_id p) - wtp_amount p) eqn:E.
        + unfold token_balance. 
          setoid_rewrite FMap.find_remove. 
          reflexivity.
        + unfold token_balance. 
          setoid_rewrite FMap.find_add. 
          reflexivity.
    - unfold transfer_operation. 
      reflexivity.
Qed.

(** ** Withdraw all xtz correct *)
Lemma Withdraw_all_xtz_is_functionally_correct {chain ctx prev_state next_state ops amount} :
    minter_receive chain ctx prev_state (Some (Fees (Withdraw_all_xtz))) = Some (next_state, ops) ->
    xtz_balance prev_state.(fees).(fees_storage_xtz) ctx.(ctx_from) = amount ->
    xtz_balance next_state.(fees).(fees_storage_xtz) ctx.(ctx_from) = 0 /\
    (if amount =? 0 then ops = [] else 
        ops = [act_transfer ctx.(ctx_from) (N_to_amount amount)]). 
Proof.
    intros. 
    contract_simpl minter_receive minter_init. 
    destruct (xtz_balance (fees_storage_xtz (fees prev_state)) (ctx_from ctx) =? 0) eqn:E. 
    - inversion H2.
      rewrite N.eqb_eq in E; try easy.
    - destruct (throwIf (address_is_contract (ctx_from ctx))); try easy.
      inversion H2.
      rewrite N.sub_diag.
      unfold xtz_balance.
      setoid_rewrite FMap.find_remove; try easy.
Qed.

(** ** Withdraw xtz correct *)
Lemma Withdraw_xtz_is_functionally_correct {chain ctx prev_state next_state ops amount n} :
    minter_receive chain ctx prev_state (Some (Fees (Withdraw_xtz n))) = Some (next_state, ops) ->
    xtz_balance prev_state.(fees).(fees_storage_xtz) ctx.(ctx_from) = amount ->
    xtz_balance next_state.(fees).(fees_storage_xtz) ctx.(ctx_from) = amount-n /\
    (if amount =? 0 then ops = [] else 
        ops = [act_transfer ctx.(ctx_from) (N_to_amount n)]). 
Proof.
    intros. 
    contract_simpl minter_receive minter_init.
    split.
    - destruct (xtz_balance (fees_storage_xtz (fees prev_state)) (ctx_from ctx)) eqn:E. 
        + cbn in H2. 
          inversion H2. 
          apply E.
        + cbn in H2. destruct (throwIf (address_is_contract (ctx_from ctx))); 
          try easy. inversion H2. cbn.
          unfold xtz_balance. 
          destruct n0 eqn:E2.
            * setoid_rewrite FMap.find_add. 
              reflexivity.
            * destruct (Pos.sub_mask p0 p1).
                -- setoid_rewrite FMap.find_remove. 
                   reflexivity.
                -- setoid_rewrite FMap.find_add.  
                   reflexivity.
                -- setoid_rewrite FMap.find_remove. 
                   reflexivity.
    - destruct (xtz_balance (fees_storage_xtz (fees prev_state)) (ctx_from ctx) =? 0) eqn:E in H2;
        try destruct (throwIf (address_is_contract (ctx_from ctx))); try easy;
        inversion H2; now rewrite E.
Qed.

(** * Unwrap proofs *)
(** The definition of functionality can be found in the Unwrap.v file*)

(** ** Unwrap ERC20 correct *)
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
    intros. 
    contract_simpl minter_receive minter_init. 
    unfold unwrap_erc20 in H. cbn.
    setoid_rewrite H0 in H. 
    split; intros; cbn in H.
    (* Fees ledger correct *)
    - unfold Fees_Lib.token_balance in H.
      rewrite H3 in H. 
      destruct (token_address) eqn:E2 in H.
      destruct (Fees_Lib.check_fees_high_enough fees_amount (Fees_Lib.bps_of amount (erc20_unwrapping_fees (governance prev_state)))) in H; try easy.
      inversion H.
      rewrite <- H6 in H4. cbn in H4.
      rewrite E2 in H4. 
      setoid_rewrite FMap.find_add in H4.
      inversion H2. 
      easy.
    (* Acts correct *)
    - destruct (token_address) eqn:E2 in H.
      destruct (Fees_Lib.check_fees_high_enough fees_amount (Fees_Lib.bps_of amount (erc20_unwrapping_fees (governance prev_state)))) in H; try easy. 
      destruct fees_amount eqn:E3; cbn in *; 
      try inversion H; rewrite E2; easy. 
Qed.

(** ** Unwrap ERC721 correct *)
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
    intros. 
    contract_simpl minter_receive minter_init. cbn.
    setoid_rewrite FMap.find_add. 
    split; try easy.
    intros. 
    rewrite H in H4. 
    inversion H4.
    easy.
Qed.

(** ** Unwrap Safety Properties *)
(** ** Unwrap ERC20 fails if fees are below min *)
Lemma unwrap_erc20_fees_below_min {chain ctx prev_state eth_address amount fees_amount erc20_dest} :
    fees_amount < Fees_Lib.bps_of amount prev_state.(governance).(erc20_unwrapping_fees) ->
    minter_receive chain ctx prev_state (Some (Unwrap (unwrap_erc20_entrypoint ({|
        erc_20 := eth_address;
        up_amount := amount;
        up_fees := fees_amount;
        up_erc20_destination := erc20_dest
    |})))) = None.
Proof.
    intros. 
    contract_simpl minter_receive minter_init. 
    destruct (fail_if_paused (admin prev_state)); try easy.
    destruct (fail_if_amount ctx); try easy. 
    unfold unwrap_erc20. cbn. 
    destruct (get_fa2_token_id eth_address (erc20tokens (assets prev_state))); try easy.
    destruct t. 
    unfold Fees_Lib.check_fees_high_enough. 
    unfold throwIf. 
    rewrite <- N.ltb_lt in H. 
    rewrite H. 
    reflexivity.
Qed.
    
(** ** Unwrap ERC721 fails if fees are below min *)
Lemma unwrap_erc721_fees_below_min {chain ctx prev_state eth_address erc721_dest token_id} :
    Z.to_N ctx.(ctx_amount) < prev_state.(governance).(erc721_unwrapping_fees) ->
    minter_receive chain ctx prev_state (Some (Unwrap (unwrap_erc721_entrypoint ({|
        erc_721 := eth_address;
        up_token_id := token_id;
        up_erc721_destination := erc721_dest
    |})))) = None.
Proof.
    intros. 
    contract_simpl minter_receive minter_init.
    destruct (fail_if_paused (admin prev_state)); try easy.
    unfold Fees_Lib.check_nft_fees_high_enough.
    unfold throwIf.
    rewrite <- N.ltb_lt in H.
    rewrite H. 
    reflexivity.
Qed.


(** * SignerOps Proofs *)
(** The definition of functionality can be found in the SignerOps.v and SignerOps_Interface.v files*)

(** ** Signer Ops Correct *)
Lemma signer_ops_functionally_correct {chain ctx prev_state next_state signer addr} :
    minter_receive chain ctx prev_state (Some (Signer_Ops (set_payment_address {| sparam_signer:= signer; payment_address:=addr |}))) = Some(next_state, []) ->
    FMap.find signer next_state.(fees).(fees_storage_signers) = Some addr.
Proof.
    intros. 
    contract_simpl minter_receive minter_init. cbn.
    rewrite FMap.find_add. 
    reflexivity.
Qed.

End Main. 