Require Import Blockchain.
Require Import ZArith.
Require Import Serializable.

Section Fees_Interface.

Context {BaseTypes : ChainBase}.
Set Nonrecursive Elimination Schemes.

Record WithdrawTokensParam :=
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

Global Instance WithdrawTokensParam_serializable : Serializable WithdrawTokensParam :=
    Derive Serializable WithdrawTokensParam_rect<mkWithdrawTokensParam>.

Global Instance WithdrawTokenParam_serializable : Serializable WithdrawTokenParam :=
    Derive Serializable WithdrawTokenParam_rect<mkWithdrawTokenParam>.

Global Instance WithdrawalEntrypoint_serializable : Serializable WithdrawalEntrypoint :=
    Derive Serializable WithdrawalEntrypoint_rect<Withdraw_all_tokens, Withdraw_all_xtz, Withdraw_token, Withdraw_xtz>.

End Fees_Interface.