Require Import FA2InterfaceOwn.
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

Definition Ledger := FMap (Address * token_id) N.

Definition OperatorStorage := FMap (Address * (Address * token_id)) unit.

Definition TokenTotalSupply := FMap token_id N.

Record MultiTokenStorage :=  
    mkMultiTokenStorage  {
        ledger : Ledger ;
        operators : OperatorStorage ; 
        token_total_supply : TokenTotalSupply ;
        token_metadata : TokenMetaDataStorage
    }.

Record MultiAssetStorage := 
    mkMultiAssetStorage {
        admin : TokenAdminStorage ; 
        assets : MultiTokenStorage ; 
        metadata : ContractMetadata
    }.

Definition Return: Type := ((list ActionBody) * MultiAssetStorage).

MetaCoq Run (make_setters MultiTokenStorage).
MetaCoq Run (make_setters MultiAssetStorage).

End FA2Types.