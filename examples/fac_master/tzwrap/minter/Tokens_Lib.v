(** * Tokens lib *)
(** This is an implementation of the following file.
https://github.com/bender-labs/wrap-tz-contracts/blob/master/ligo/minter/tokens_lib.mligo.

*)
Require Import Ethereum_Lib.
Require Import Storage.
Require Import Blockchain.
Require Import FA2InterfaceOwn.
From ConCert.Examples Require Import FA2Interface.
From ConCert.Execution Require Import Containers.
Require Import Types.
Require Import ZArith.
Require Import ContractCommon.


Section Tokens_Lib.
Context {BaseTypes : ChainBase}.

Open Scope N.

Definition get_fa2_token_id (eth_contract : EthAddress) (tokens: (FMap EthAddress TokenAddress)) : option TokenAddress := 
     FMap.find eth_contract tokens.

Definition get_nft_contract (eth_contract : EthAddress) (tokens: (FMap EthAddress Address)) : option Address :=
    FMap.find eth_contract tokens. 

Definition fail_if_amount (ctx : ContractCallContext) : option unit :=
    throwIf ((0 <? ctx.(ctx_amount))%Z).

End Tokens_Lib.