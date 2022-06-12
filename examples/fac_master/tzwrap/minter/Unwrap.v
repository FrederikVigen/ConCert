(** * Unwrap endpoints *)
(** This is an implementation of the following file.
https://github.com/bender-labs/wrap-tz-contracts/blob/master/ligo/minter/unwrap.mligo.

*)
Require Import Tokens_Lib.
Require Import Fees_Lib.
Require Import Ethereum_Lib.
From Coq Require Import ZArith.
From ConCert.Examples Require Import FA2Interface.
Require Import FA2InterfaceOwn.
Require Import Storage.
Require Import Blockchain.
Require Import Monads.
Require Import List.
From ConCert.Execution Require Import Serializable.
Import ListNotations.
From Coq Require Import ZArith.

(** * Types *)
Section Unwrap.
Context {BaseTypes : ChainBase}.
Set Nonrecursive Elimination Schemes.
Open Scope N_scope.

Record UnwrapERC20Parameters : Type := 
    mkUnwrapERC20Parameters {
        erc_20 : EthAddress;
        up_amount : N;
        up_fees : N;
        up_erc20_destination : EthAddress;
    }.

Record UnwrapERC721Parameters : Type :=
    mkUnwrapERC721Parameters {
        erc_721 : EthAddress;
        up_token_id : token_id;
        up_erc721_destination : EthAddress;
    }.

Inductive UnwrapEntrypoints :=
    | unwrap_erc20_entrypoint (unwrap_erc20_params : UnwrapERC20Parameters)
    | unwrap_erc721_entrypoint (unwrap_erc721_params : UnwrapERC721Parameters).

(* begin hide *)
Global Instance UnwrapERC20Parameters_serializable : Serializable UnwrapERC20Parameters :=
    Derive Serializable UnwrapERC20Parameters_rect<mkUnwrapERC20Parameters>.

Global Instance UnwrapERC721Parameters_serializable : Serializable UnwrapERC721Parameters :=
    Derive Serializable UnwrapERC721Parameters_rect<mkUnwrapERC721Parameters>.

Global Instance UnwrapEntrypoints_serializable : Serializable UnwrapEntrypoints :=
    Derive Serializable UnwrapEntrypoints_rect<unwrap_erc20_entrypoint, unwrap_erc721_entrypoint>.
(* end hide *)

(** * Implementation *)
(** ** Unwrap ERC20 *)
Definition unwrap_erc20 (ctx : ContractCallContext) (p : UnwrapERC20Parameters) (s : State) : option ReturnType :=
    let governance := s.(governance) in
    let assets := s.(assets) in
    let fees_storage := s.(fees) in
    let token_address_opt := get_fa2_token_id p.(erc_20) assets.(erc20tokens) in
    match token_address_opt with
    | Some token_address => 
        let (contract_address, token_id) := token_address in
        let min_fees := bps_of p.(up_amount) governance.(erc20_unwrapping_fees) in
        do _ <- check_fees_high_enough p.(up_fees) min_fees ;
        let burnTokensParams := {|
            mint_burn_owner:= ctx.(ctx_from);
            mint_burn_token_id := token_id;
            mint_burn_amount := p.(up_amount) + p.(up_fees)
        |} in
        let burn := act_call contract_address 0 (serialize (BurnTokens [burnTokensParams])) in
        let ops := 
            if p.(up_fees) =? 0
            then [burn]
            else
            let mintTokensParams :=  {|
                mint_burn_owner := ctx.(ctx_contract_address);
                mint_burn_token_id := token_id;
                mint_burn_amount := p.(up_fees)
            |} in
            [burn] ++ [act_call contract_address 0 (serialize (MintTokens [mintTokensParams]))]
            in
        let new_ledger := inc_token_balance fees_storage.(fees_storage_tokens) ctx.(ctx_contract_address) token_address p.(up_fees) in
        Some ({|
            admin := s.(admin);
            assets := assets;
            governance := governance;
            fees := {|
                fees_storage_signers := s.(fees).(fees_storage_signers);
                fees_storage_tokens := new_ledger;
                fees_storage_xtz := s.(fees).(fees_storage_xtz);
            |};
            storage_metadata := s.(storage_metadata)
        |}, ops)
    | None => None
    end.

(** ** Unwrap ERC721 *)
Definition unwrap_erc721 (ctx : ContractCallContext) (p: UnwrapERC721Parameters) (s: State) : option ReturnType :=
    let governance := s.(governance) in
    let assets := s.(assets) in
    let fees_storage := s.(fees) in
    let amountN := Z.to_N ctx.(ctx_amount) in
    do ignore <- check_nft_fees_high_enough amountN governance.(erc721_unwrapping_fees) ;
    let contract_address_opt := get_nft_contract p.(erc_721) assets.(erc721tokens) in
    match contract_address_opt with
    | Some contract_address => 
        let burnTokensParams := {|
            mint_burn_owner := ctx.(ctx_from);
            mint_burn_token_id := p.(up_token_id);
            mint_burn_amount := 1
        |} in
        let burn := act_call contract_address 0 (serialize (BurnTokens [burnTokensParams])) in
        let new_ledger := inc_xtz_balance fees_storage.(fees_storage_xtz) ctx.(ctx_contract_address) amountN in 
        Some ({|
            admin := s.(admin);
            assets := assets;
            governance := governance;
            fees := {|
                fees_storage_signers := s.(fees).(fees_storage_signers);
                fees_storage_tokens := s.(fees).(fees_storage_tokens);
                fees_storage_xtz := new_ledger;
            |};
            storage_metadata := s.(storage_metadata)
        |}, [burn]) 
    | None => None
    end.

(** ** Main entrypoint *)
Definition unwrap_main (ctx : ContractCallContext) (p : UnwrapEntrypoints) (s : State) : option ReturnType :=
    match p with
    | unwrap_erc20_entrypoint p => 
        do _ <- fail_if_amount ctx ; 
        unwrap_erc20 ctx p s
    | unwrap_erc721_entrypoint p => 
        unwrap_erc721 ctx p s
    end.

End Unwrap.