Require Import Blockchain.
Require Import ZArith.

Section Fees_Interface.

Context {BaseTypes : ChainBase}.

Record WithdrawTokensParam : Type :=
     mkWithdrawTokensParam { fa2_tokens : Address ;
                tokens : list N}.

Record WithdrawTokenParam : Type :=
     mkWithdrawTokenParam { fa2_token : Address ;
                wtp_token_id : N;
                wtp_amount : N}.

Inductive WithdrawalEntrypoint :=
| Withdraw_all_tokens (param : WithdrawTokensParam)
| Withdraw_all_xtz 
| Withdraw_token (param : WithdrawTokenParam)
| Withdraw_xtz (tez : N).

End Fees_Interface.