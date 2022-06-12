(** * Signer Ops *)
(** This is an implementation of the following file.
https://github.com/bender-labs/wrap-tz-contracts/blob/master/ligo/minter/signer_ops.mligo.

Interface for signer ops

*)
Require Import ZArith.
Require Import Blockchain.
Require Import Serializable.
Require Import Storage.
From ConCert.Utils Require Import RecordUpdate.

Section Signer_Ops_Interface.
Set Nonrecursive Elimination Schemes.
Context {BaseTypes : ChainBase}.

(** ** Set Signer Payment Address parameters *)
Record SetSignerPaymentAddressParam := mkSetSignerPaymentAddressParam {
    sparam_signer : N ;
    payment_address: Address
}.

(** ** Set Signer Payment Address entrypoint *)
Inductive SignerOpsEntrypoint : Type :=
| set_payment_address (set_signer_payment_address_param : SetSignerPaymentAddressParam).

(* begin hide *)
Global Instance SetSignerPaymentAddressParam_serializable : Serializable SetSignerPaymentAddressParam :=
    Derive Serializable SetSignerPaymentAddressParam_rect<mkSetSignerPaymentAddressParam>.

Global Instance SignerOpsEntrypoint_serializable : Serializable SignerOpsEntrypoint :=
    Derive Serializable SignerOpsEntrypoint_rect<set_payment_address>.
(* end hide *)

End Signer_Ops_Interface.