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
Require Import FA2InterfaceOwn.
Import ListNotations.

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
    let fungible_tokens := fold_right (
        fun (eth_contract : EthAddress) (acc : (N * FMap EthAddress TokenAddress)) =>
        ((fst acc) + 1, FMap.update eth_contract (Some (setup.(fa2_contract), fst acc)) (snd acc))
    ) (0, FMap.empty) setup.(setup_tokens) in
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

(** The minter contract *)
Definition minter_contract : Contract Setup EntryPoints State :=
build_contract minter_init minter_receive.

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
    

End Main. 