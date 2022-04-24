Require Import Blockchain.
Require Import Ethereum_Lib.
Require Import Types.
Require Import String.
Require Import ZArith.
From ConCert.Execution Require Import Containers.
Require Import RecordUpdate.
Require Import Serializable.

Section Storage.
Context {BaseTypes : ChainBase}.
Set Nonrecursive Elimination Schemes.

Record ContractAdminStorage :=
     mkConractAdminStorage 
     { administrator : Address ;
        pending_admin : option Address;
        signer : Address;
        oracle : Address;
        paused : bool }.

Global Instance ContractAdminStorage_serializable : Serializable ContractAdminStorage :=
        Derive Serializable ContractAdminStorage_rect<mkConractAdminStorage>.
    
Definition MintsType := (FMap EthEventId unit).

Record AssetsStorage :=
        mkAssetsStorage 
     { erc20tokens : (FMap EthAddress TokenAddress );
        erc721tokens : (FMap EthAddress Address) ;
        mints : MintsType}.

Global Instance AssetsStorage_serializable : Serializable AssetsStorage :=
        Derive Serializable AssetsStorage_rect<mkAssetsStorage>.

Record FeesShare :=
        mkFeesShare 
        { dev_pool : N;
        signers : N;
        staking : N}.

Global Instance FeesShare_serializable : Serializable FeesShare :=
        Derive Serializable FeesShare_rect<mkFeesShare>.

Record GovernanceStorage :=
        mkGovernanceStorage
        { contract : Address;
        staking_address : Address;
        dev_pool_address : Address;
        erc20_wrapping_fees : bps;
        erc20_unwrapping_fees : bps;
        erc721_wrapping_fees : N;
        erc721_unwrapping_fees : N;
        fees_share_rec : FeesShare }.

Global Instance GovernanceStorage_serializable : Serializable GovernanceStorage :=
        Derive Serializable GovernanceStorage_rect<mkGovernanceStorage>.

Definition TokenLedger := FMap (Address * TokenAddress) N.

Definition XTZLedger := (FMap Address N).

Record FeesStorage :=
        mkFeesStorage 
        { fees_storage_signers : FMap N Address;
         fees_storage_tokens : TokenLedger;
         fees_storage_xtz : XTZLedger }.

Global Instance FeesStorage_serializable : Serializable FeesStorage :=
         Derive Serializable FeesStorage_rect<mkFeesStorage>.
 
Record State :=
        mkStorage
        { admin : ContractAdminStorage;
        assets : AssetsStorage;
        governance : GovernanceStorage;
        fees : FeesStorage;
        storage_metadata : MetaData }.

Global Instance State_serializable : Serializable State :=
        Derive Serializable State_rect<mkStorage>.

MetaCoq Run (make_setters ContractAdminStorage).
MetaCoq Run (make_setters AssetsStorage).
MetaCoq Run (make_setters FeesShare).
MetaCoq Run (make_setters GovernanceStorage).
MetaCoq Run (make_setters FeesStorage).
MetaCoq Run (make_setters State).

Definition ReturnType : Type := (State * list ActionBody).

End Storage.