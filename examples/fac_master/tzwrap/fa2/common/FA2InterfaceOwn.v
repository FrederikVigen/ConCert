From Coq Require Import ZArith.
Require Import Blockchain.
From ConCert.Execution Require Import FA2Interface.
Require Import Types.
Require Import Serializable.
From ConCert.Utils Require Import RecordUpdate.
Require Import Containers.
Require Import String.


Section FA2InterfaceOwn.
Set Nonrecursive Elimination Schemes.
Context {BaseTypes : ChainBase}.
Open Scope N_scope.

(*TODO: Missing entries in FA2Interface that we have had to build on our own*)

Record operator_param_own := {
  op_param_owner : Address;
  op_param_operator : Address;
  op_param_token_id : token_id;
}.

Inductive update_operator_own :=
  | add_operator : operator_param_own -> update_operator_own
  | remove_operator : operator_param_own -> update_operator_own.

Record TransferDestination := mkTransferDestination {
    to_ : Address;
    dst_token_id : N;
    amount : N;
}.

Record Transfer := mkTransfer {
    from_ : Address;
    txs : list TransferDestination;
}.

MetaCoq Run (make_setters TransferDestination). 
MetaCoq Run (make_setters Transfer). 

Global Instance TransferDestination_serializable : Serializable TransferDestination :=
    Derive Serializable TransferDestination_rect<mkTransferDestination>.

Global Instance Transfer_serializable : Serializable Transfer :=
Derive Serializable Transfer_rect<mkTransfer>.

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
| FA2_Transfer (transfers : list Transfer)
| Balance_of (balanceOf : balance_of_param)
| Update_operators (updates : list update_operator_own).

Inductive MultiTokenAdmin := 
| Token_admin (tokenAdmin : TokenAdmin)
| Create_token (tokenMetaData : TokenMetadata).

End FA2InterfaceOwn.