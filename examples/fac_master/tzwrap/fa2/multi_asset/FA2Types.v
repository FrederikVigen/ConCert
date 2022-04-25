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
Set Nonrecursive Elimination Schemes.

Definition Ledger := FMap (Address * token_id) N.

Definition OperatorStorage := FMap (Address * (Address * token_id)) unit.

Definition TokenTotalSupply := FMap token_id N.

Record MultiTokenStorage :=   {
        ledger : Ledger ;
        operators : OperatorStorage ; 
        token_total_supply : TokenTotalSupply ;
        token_metadata : TokenMetaDataStorage
    }.

Global Instance MultiTokenStorage_serializable : Serializable MultiTokenStorage :=
Derive Serializable MultiTokenStorage_rect<Build_MultiTokenStorage>.

Record MultiAssetStorage :=  {
        admin : TokenAdminStorage ; 
        assets : MultiTokenStorage ; 
        metadata : ContractMetadata
    }.

Global Instance MultiAssetStorage_serializable : Serializable MultiAssetStorage :=
Derive Serializable MultiAssetStorage_rect<Build_MultiAssetStorage>.

Definition Return: Type := (MultiAssetStorage * (list ActionBody)).

MetaCoq Run (make_setters MultiTokenStorage).
MetaCoq Run (make_setters MultiAssetStorage).

End FA2Types.