(** * Signer *)
(** This is an implementation of the following file.
https://github.com/bender-labs/wrap-tz-contracts/blob/master/ligo/minter/signer.mligo.

Entrypoints used for minting and adding new assets

*)
Require Import Tokens_Lib.
Require Import Fees_Lib.
Require Import Signer_Interface.
Require Import Ethereum_Lib.
Require Import Types.
Require Import Blockchain.
Require Import ZArith.
Require Import NArith.
Require Import Storage.
From ConCert.Execution Require Import Containers.
Require Import List.
Import ListNotations.
Require Import RecordUpdate.
Require Import Serializable.
From ConCert.Execution Require Import Monads.
Require Import FA2Interface_Wrap.
From ConCert.Examples Require Import FA2Interface.

Section Signer.
Context {BaseTypes : ChainBase}.

Open Scope N.

(** ** Check if transaction has already been minted *)
Definition check_already_minted (tx_id : EthEventId) (mints: MintsType) : option unit := 
    let former_mint := FMap.find tx_id mints in
    match former_mint with
    | Some n => None
    | None => Some tt
    end.

(** ** Mint ERC20 *)
Definition mint_erc20 (ctx : ContractCallContext) (p : MintErc20Parameters) (s : State) : option ReturnType :=
    let assets_state := s.(assets) in
    let governance := s.(governance) in
    let fees_storage := s.(fees) in
    do _ <- check_already_minted p.(event_id_erc20) assets_state.(mints) ;
    do fees_ <- compute_fees p.(amount_erc20) governance.(erc20_wrapping_fees) ;
    do token_address <- get_fa2_token_id p.(erc20) assets_state.(erc20tokens) ;
    let user_mint := {|
        mint_burn_owner := p.(owner_erc20);
        mint_burn_token_id := snd token_address;
        mint_burn_amount := fst fees_
    |} in
    let fa2_txs := if 0 <? (snd fees_) then
        [user_mint; {|
            mint_burn_owner := ctx.(ctx_contract_address);
            mint_burn_token_id := snd token_address;
            mint_burn_amount := snd fees_
        |}]
    else [user_mint] in
    let new_ledger := inc_token_balance fees_storage.(fees_storage_tokens) ctx.(ctx_contract_address) token_address (snd fees_) in
    let mints_new := FMap.add p.(event_id_erc20) tt assets_state.(mints) in
    Some (s<|assets:= s.(assets)<|mints:=mints_new|>|><|fees:=s.(fees)<|fees_storage_tokens:= new_ledger|>|>, [act_call (fst token_address) 0 (serialize (MintTokens fa2_txs))]).

(** ** Mint ERC721 *)
Definition mint_erc721 (ctx : ContractCallContext) (p : MintErc721Parameters) (s : State) : option ReturnType :=
    let assets_state := s.(assets) in
    let governance := s.(governance) in
    let fees_storage := s.(fees) in
    do _ <- check_already_minted p.(event_id_erc721) assets_state.(mints) ;
    do _ <- check_nft_fees_high_enough (Z.to_N ctx.(ctx_amount)) governance.(erc721_wrapping_fees) ;
    do fa2_contract <- get_nft_contract p.(erc721) assets_state.(erc721tokens) ;
    let user_mint := {|
        mint_burn_owner := p.(owner_erc721);
        mint_burn_token_id := p.(token_id_erc721);
        mint_burn_amount := 1
    |} in
    let new_ledger := inc_xtz_balance (fees_storage.(fees_storage_xtz)) (ctx.(ctx_contract_address)) (Z.to_N ctx.(ctx_amount)) in
    let mints_new := FMap.add p.(event_id_erc721) tt assets_state.(mints) in
    Some (s<|assets:= s.(assets)<|mints:=mints_new|>|><|fees:=s.(fees)<|fees_storage_xtz:= new_ledger|>|>, [act_call fa2_contract 0 (serialize (MintTokens [user_mint]))]).

(** ** Add ERC20 *)
Definition add_erc20 (p : AddErc20Parameters) (s : AssetsStorage) : AssetsStorage := 
  let updated_tokens := FMap.update p.(eth_contract_erc20) (Some p.(token_address)) (s.(erc20tokens)) in
  s<|erc20tokens := updated_tokens|>.

(** ** Add ERC721 *)  
Definition add_erc721 (p : AddErc721Parameters) (s : AssetsStorage) : AssetsStorage := 
  let updated_tokens := FMap.update p.(eth_contract_erc721) (Some p.(token_contract)) (s.(erc721tokens)) in
  s<|erc721tokens := updated_tokens|>.

(** ** Signer main entrypoint *)
Definition signer_main (ctx : ContractCallContext)(p : SignerEntrypoints) (s : State) : option ReturnType :=
  match p with
  | Mint_erc20 param => 
    do _ <- fail_if_amount ctx ;
    mint_erc20 ctx param s
  | Add_erc20 param => 
    do _ <- fail_if_amount ctx ;
    Some (s<|assets:= add_erc20 param s.(assets)|>, [])
  | Mint_erc721 param => mint_erc721 ctx param s
  | Add_erc721 param =>
    do _ <- fail_if_amount ctx ;
    Some (s<|assets:= add_erc721 param s.(assets)|>, [])
  end.
End Signer.