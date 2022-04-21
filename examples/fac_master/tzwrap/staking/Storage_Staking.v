Require Import Blockchain.
Require Import ZArith.

Section Storage_Staking.
Context {BaseTypes : ChainBase}.

Definition token_staking : Type := (Address * N).

Record Delegator := 
    mkDelegator {
        unpaid : N;
        reward_per_token_paid : N;
    }.


End Storage_Staking.