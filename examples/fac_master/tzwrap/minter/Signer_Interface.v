Require Import Blockchain.
Require Import Ethereum_Lib.
Require Import Types.
Require Import ZArith.
Require Import Serializable.

Section Signer_Interface.
Set Nonrecursive Elimination Schemes.
Context {BaseTypes : ChainBase}.

Record MintErc20Parameters :=
    mkMintErc20Parameters { erc20 : EthAddress ;
            event_id_erc20 : EthEventId ;
            owner_erc20 : Address ;
            amount_erc20 : N}.

Record AddErc20Parameters := 
    mkAddErc20Parameters { eth_contract_erc20 : EthAddress ;
            token_address : TokenAddress}.

Record AddErc721Parameters := 
    mkAddErc721Parameters {eth_contract_erc721 : EthAddress ;
            token_contract : Address}.

Record MintErc721Parameters :=
    mkMintErc721Parameters { erc721 : EthAddress ;
            event_id_erc721 : EthEventId ;
            owner_erc721 : Address ;
            token_id_erc721 : N}.

Inductive SignerEntrypoints : Type :=
| Mint_erc20 (mint_erc20_parameters : MintErc20Parameters)
| Add_erc20 (add_erc20_parameters : AddErc20Parameters)
| Mint_erc721 (mint_erc721_parameters : MintErc721Parameters)
| Add_erc721 (add_erc721_parameters : AddErc721Parameters).


Global Instance MintErc20Parameters_serializable : Serializable MintErc20Parameters :=
    Derive Serializable MintErc20Parameters_rect<mkMintErc20Parameters>.

Global Instance AddErc20Parameters_serializable : Serializable AddErc20Parameters :=
    Derive Serializable AddErc20Parameters_rect<mkAddErc20Parameters>.

Global Instance AddErc721Parameters_serializable : Serializable AddErc721Parameters :=
    Derive Serializable AddErc721Parameters_rect<mkAddErc721Parameters>.

Global Instance MintErc721Parameters_serializable : Serializable MintErc721Parameters :=
    Derive Serializable MintErc721Parameters_rect<mkMintErc721Parameters>.

Global Instance SignerEntrypoints_serializable : Serializable SignerEntrypoints :=
    Derive Serializable SignerEntrypoints_rect<Mint_erc20, Add_erc20, Mint_erc721, Add_erc721>.

End Signer_Interface.