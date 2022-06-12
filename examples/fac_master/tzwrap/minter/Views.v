(** * Views *)
(** This is an implementation of the following file.
https://github.com/bender-labs/wrap-tz-contracts/blob/master/ligo/minter/views.mligo.

This file is currently not used in our implementation
*)
Require Import Blockchain.
Require Import Storage.
Require Import ZArith.
Require Import Containers.
Require Import Types.
Require Import List.
Import ListNotations.

Section Views.
Context {BaseTypes : ChainBase}.
Open Scope N.

Definition get_token_balance (addr : Address) (token_address : TokenAddress) (ledger : TokenLedger) : N :=
    let key := (addr, token_address) in
    match FMap.find key ledger with
    | Some v => v
    | None => 0
    end.

Definition get_tez_balance (addr : Address) (ledger : XTZLedger) : N := 
    match FMap.find addr ledger with
    | Some v => v 
    | None => 0
    end.

Record GetTokenRewardParameter := 
    mkGetTokenRewardParameter { 
        gtrp_address : Address ;
        gtrp_token_contract : Address ; 
        gtrp_token_id : N
    }.

Definition get_token_reward_view (p : GetTokenRewardParameter) (s : State) : N := 
    let ledger := s.(fees).(fees_storage_tokens) in
    let token := (p.(gtrp_token_contract), p.(gtrp_token_id)) in
    get_token_balance p.(gtrp_address) token ledger.

Definition get_token_reward_main (p : GetTokenRewardParameter) (s : State) : (list ActionBody * State) := 
    ([], s).

Definition get_tez_reward_view (p : Address) (s : State) : N :=
    let ledger := s.(fees).(fees_storage_xtz) in 
    get_tez_balance p ledger.

Definition get_tez_reward_main (p : Address) (s : State) : (list ActionBody * State) :=
    ([], s).

End Views.