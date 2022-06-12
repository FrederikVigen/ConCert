From Coq Require Import ZArith.
Require Import Blockchain.
From ConCert.Examples.FA2 Require Import FA2Interface.
Require Import Types.
Require Import Serializable.
From ConCert.Utils Require Import RecordUpdate.
Require Import Containers.
Require Import String.


Section FA2InterfaceOwn.
Set Nonrecursive Elimination Schemes.
Context {BaseTypes : ChainBase}.
Open Scope N_scope.

Record MintBurnTx := mkMintBurnTx {
    mint_burn_owner: Address;
    mint_burn_token_id : token_id;
    mint_burn_amount: N;
}.

Global Instance MintBurnTx_serializeable : Serializable MintBurnTx :=
    Derive Serializable MintBurnTx_rect<mkMintBurnTx>.

Definition MintBurnTokensParam : Type := list MintBurnTx.

Inductive TokenManager := 
    | MintTokens (p : MintBurnTokensParam)
    | BurnTokens (p : MintBurnTokensParam).

Global Instance TokenManager_serializable : Serializable TokenManager :=
Derive Serializable TokenManager_rect<MintTokens, BurnTokens>.

Record PauseParam := mkPauseParam {
    pp_token_id : N;
    pp_paused : bool
}.

Inductive TokenAdmin :=
| Set_admin (addr : Address)
| Confirm_admin
| Pause (param : list PauseParam)
| Set_minter (addr : Address).

Global Instance PauseParam_serializable : Serializable PauseParam :=
Derive Serializable PauseParam_rect<mkPauseParam>.

Global Instance TokenAdmin_serializable : Serializable TokenAdmin :=
Derive Serializable TokenAdmin_rect<Set_admin, Confirm_admin, Pause, Set_minter>.

Definition ContractMetadata := FMap string N.

Record TokenMetadata := mkTokenMetadata {
    tm_token_id : token_id ;
    tm_token_info : FMap string N 
}.

Global Instance TokenMetadata_serializable : Serializable TokenMetadata :=
Derive Serializable TokenMetadata_rect<mkTokenMetadata>.

Definition TokenMetaDataStorage := FMap token_id TokenMetadata.

Inductive FA2EntryPoints :=
| FA2_Transfer (transfers : list transfer)
| Balance_of (balanceOf : balance_of_param)
| Update_operators (updates : list update_operator).

Global Instance FA2EntryPoints_serializable : Serializable FA2EntryPoints :=
Derive Serializable FA2EntryPoints_rect<FA2_Transfer, Balance_of, Update_operators>.

Inductive MultiTokenAdmin := 
| Token_admin (tokenAdmin : TokenAdmin)
| Create_token (tokenMetaData : TokenMetadata).

Global Instance MultiTokenAdmin_serializable : Serializable MultiTokenAdmin :=
Derive Serializable MultiTokenAdmin_rect<Token_admin, Create_token>.

End FA2InterfaceOwn.