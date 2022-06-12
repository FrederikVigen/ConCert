(** * FA2Interface for TzWrap *)
(** This file contains the things from 
https://github.com/bender-labs/wrap-tz-contracts/blob/1655949e61b05a1c25cc00dcb8c1da9d91799f31/ligo/fa2/common/fa2_interface.mligo
that are not present in the standard FA2Interface*)

From Coq Require Import ZArith.
Require Import Blockchain.
From ConCert.Examples.FA2 Require Import FA2Interface.
Require Import Types.
Require Import Serializable.
From ConCert.Utils Require Import RecordUpdate.
Require Import Containers.
Require Import String.


Section FA2Interface_Wrap.
Set Nonrecursive Elimination Schemes.
Context {BaseTypes : ChainBase}.
Open Scope N_scope.

(** ** Record for mint/burn transaction*)
Record MintBurnTx := mkMintBurnTx {
    mint_burn_owner: Address;
    mint_burn_token_id : token_id;
    mint_burn_amount: N;
}.
(* begin hide *)
Global Instance MintBurnTx_serializeable : Serializable MintBurnTx :=
    Derive Serializable MintBurnTx_rect<mkMintBurnTx>.
(* end hide *)

Definition MintBurnTokensParam : Type := list MintBurnTx.

(** ** Endpoints for the TokenManager*)
Inductive TokenManager := 
    | MintTokens (p : MintBurnTokensParam)
    | BurnTokens (p : MintBurnTokensParam).

(* begin hide *)
Global Instance TokenManager_serializable : Serializable TokenManager :=
Derive Serializable TokenManager_rect<MintTokens, BurnTokens>.
(* end hide *)

(** ** Param and endpoints for TokenAdmin*)
Record PauseParam := mkPauseParam {
    pp_token_id : N;
    pp_paused : bool
}.

Inductive TokenAdmin :=
| Set_admin (addr : Address)
| Confirm_admin
| Pause (param : list PauseParam)
| Set_minter (addr : Address).

(* begin hide *)
Global Instance PauseParam_serializable : Serializable PauseParam :=
Derive Serializable PauseParam_rect<mkPauseParam>.

Global Instance TokenAdmin_serializable : Serializable TokenAdmin :=
Derive Serializable TokenAdmin_rect<Set_admin, Confirm_admin, Pause, Set_minter>.
(* end hide *)

Definition ContractMetadata := FMap string N.

Definition TokenMetaDataStorage := FMap token_id token_metadata.

Inductive FA2EntryPoints :=
| FA2_Transfer (transfers : list transfer)
| Balance_of (balanceOf : balance_of_param)
| Update_operators (updates : list update_operator).

Global Instance FA2EntryPoints_serializable : Serializable FA2EntryPoints :=
Derive Serializable FA2EntryPoints_rect<FA2_Transfer, Balance_of, Update_operators>.

Inductive MultiTokenAdmin := 
| Token_admin (tokenAdmin : TokenAdmin)
| Create_token (tokenMetaData : token_metadata).

Global Instance MultiTokenAdmin_serializable : Serializable MultiTokenAdmin :=
Derive Serializable MultiTokenAdmin_rect<Token_admin, Create_token>.

End FA2Interface_Wrap.