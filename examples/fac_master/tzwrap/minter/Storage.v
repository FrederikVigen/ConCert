Require Import Blockchain.
Require Import Ethereum_Lib.
Require Import Types.
Require Import String.
Require Import ZArith.
From ConCert.Execution Require Import Containers.
Require Import RecordUpdate.

Section Storage.
Context {BaseTypes : ChainBase}.

Record ContractAdminStorage :=
     mkConractAdminStorage 
     { administrator : Address ;
        pending_admin : option Address;
        signer : Address;
        oracle : Address;
        paused : bool }.

Definition MintsType := (FMap EthEventId unit).

Record AssetsStorage :=
        mkAssetsStorage 
     { erc20tokens : (FMap EthAddress TokenAddress );
        erc721tokens : (FMap EthAddress Address) ;
        mints : MintsType}.

Record FeesShare :=
        mkFeesShare 
        { dev_pool : N;
        signers : N;
        staking : N}.
  
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

Definition TokenLedger := FMap (Address * TokenAddress) N.

Definition XTZLedger := (FMap Address N).

Record FeesStorage :=
        mkFeesStorage 
        { fees_storage_signers : FMap N Address;
         fees_storage_tokens : TokenLedger;
         fees_storage_xtz : XTZLedger }.

Record State :=
        mkStorage
        { admin : ContractAdminStorage;
        assets : AssetsStorage;
        governance : GovernanceStorage;
        fees : FeesStorage;
        storage_metadata : MetaData }.

MetaCoq Run (make_setters ContractAdminStorage).
MetaCoq Run (make_setters AssetsStorage).
MetaCoq Run (make_setters FeesShare).
MetaCoq Run (make_setters GovernanceStorage).
MetaCoq Run (make_setters FeesStorage).
MetaCoq Run (make_setters State).

Definition ReturnType : Type := (list ActionBody * State).

End Storage.