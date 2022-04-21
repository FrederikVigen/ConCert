Require Import ZArith.
Require Import Blockchain.
Require Import Serializable.
Require Import Storage.
From ConCert.Utils Require Import RecordUpdate.

Section Signer_Ops_Interface.
Set Nonrecursive Elimination Schemes.
Context {BaseTypes : ChainBase}.

Record SetSignerPaymentAddressParam := mkSetSignerPaymentAddressParam {
    sparam_signer : N ;
    payment_address: Address
}.

Inductive SignerOpsEntrypoint : Type :=
| set_payment_address (set_signer_payment_address_param : SetSignerPaymentAddressParam).

Global Instance SetSignerPaymentAddressParam_serializable : Serializable SetSignerPaymentAddressParam :=
    Derive Serializable SetSignerPaymentAddressParam_rect<mkSetSignerPaymentAddressParam>.

Global Instance SignerOpsEntrypoint_serializable : Serializable SignerOpsEntrypoint :=
    Derive Serializable SignerOpsEntrypoint_rect<set_payment_address>.

End Signer_Ops_Interface.