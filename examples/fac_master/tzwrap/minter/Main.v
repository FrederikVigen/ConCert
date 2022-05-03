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

End Main.