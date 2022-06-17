(** * Interface for core types in the fees contract *)
(** This file contains the definition of some of the cores types used in the Fees part of the Minter Contract 
    The file this file has been translated from can be found here:
    https://github.com/bender-labs/wrap-tz-contracts/blob/1655949e61b05a1c25cc00dcb8c1da9d91799f31/ligo/minter/fees_interface.mligo
*)

Require Import Blockchain.
Require Import ZArith.
Require Import Serializable.

Section Fees_Interface.
Context {BaseTypes : ChainBase}.
Set Nonrecursive Elimination Schemes.

(** ** Param to withdraw multiple tokens*)
Record WithdrawTokensParam :=
     mkWithdrawTokensParam { wtp_fa2_tokens : Address ;
                wtp_tokens : list N}.

(** ** Param to withdraw a single token*)
Record WithdrawTokenParam : Type :=
     mkWithdrawTokenParam { fa2_token : Address ;
                wtp_token_id : N;
                wtp_amount : N}.

(** ** All entrypoints for the Fees part of the Minter Contract*)
Inductive WithdrawalEntrypoint :=
| Withdraw_all_tokens (param : WithdrawTokensParam)
| Withdraw_all_xtz 
| Withdraw_token (param : WithdrawTokenParam)
| Withdraw_xtz (tez : N).

(* begin hide *)
Global Instance WithdrawTokensParam_serializable : Serializable WithdrawTokensParam :=
    Derive Serializable WithdrawTokensParam_rect<mkWithdrawTokensParam>.

Global Instance WithdrawTokenParam_serializable : Serializable WithdrawTokenParam :=
    Derive Serializable WithdrawTokenParam_rect<mkWithdrawTokenParam>.

Global Instance WithdrawalEntrypoint_serializable : Serializable WithdrawalEntrypoint :=
    Derive Serializable WithdrawalEntrypoint_rect<Withdraw_all_tokens, Withdraw_all_xtz, Withdraw_token, Withdraw_xtz>.
(* end hide *)

End Fees_Interface.