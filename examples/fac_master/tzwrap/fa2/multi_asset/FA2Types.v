(** * FA2 Types*)
(** This file contains the implementation of the file
https://github.com/bender-labs/wrap-tz-contracts/blob/1655949e61b05a1c25cc00dcb8c1da9d91799f31/ligo/fa2/multi_asset/types.mligo
It Contains types required for the FA2 tokens contract.
*)
Require Import FA2Interface_Wrap.
Require Import Containers.
Require Import ZArith.
Require Import Blockchain.
From ConCert.Examples.FA2 Require Import FA2Interface.
Require Import TokenAdmin.
Require Import List.
Require Import Serializable.
Require Import RecordUpdate.

Open Scope N.

Section FA2Types.
Context {BaseTypes: ChainBase}.
Set Nonrecursive Elimination Schemes.

(** ** Types for keeping track of state*)
Definition Ledger := FMap (Address * token_id) N.

Definition OperatorStorage := FMap (Address * (Address * token_id)) unit.

Definition TokenTotalSupply := FMap token_id N.

Record MultiTokenStorage :=   {
        ledger : Ledger ;
        operators : OperatorStorage ; 
        token_total_supply : TokenTotalSupply ;
        mts_token_metadata : TokenMetaDataStorage
    }.

(* begin hide *)
Global Instance MultiTokenStorage_serializable : Serializable MultiTokenStorage :=
Derive Serializable MultiTokenStorage_rect<Build_MultiTokenStorage>.
(* end hide *)

Record MultiAssetStorage :=  {
        fa2_admin : TokenAdminStorage ; 
        fa2_assets : MultiTokenStorage ; 
        metadata : ContractMetadata
    }.

(* begin hide *)
Global Instance MultiAssetStorage_serializable : Serializable MultiAssetStorage :=
Derive Serializable MultiAssetStorage_rect<Build_MultiAssetStorage>.
(* end hide *)

(** ** Return type for the FA2 token contract *)
Definition Return: Type := (MultiAssetStorage * (list ActionBody)).

(* begin hide *)
MetaCoq Run (make_setters MultiTokenStorage).
MetaCoq Run (make_setters MultiAssetStorage).
(* end hide*)

End FA2Types.