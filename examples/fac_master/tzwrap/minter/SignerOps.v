(** * Signer ops *)
(** This is an implementation of the following file.

https://github.com/bender-labs/wrap-tz-contracts/blob/master/ligo/minter/signerops.mligo.
*)
Require Import Signer_Ops_Interface.
Require Import Storage.
Require Import Blockchain.
Require Import List.
Import ListNotations.
Require Import RecordUpdate.
Require Import Containers.

Section SignerOps.
Context {BaseTypes : ChainBase}.


Definition signer_ops_main (ctx : ContractCallContext) (ep : SignerOpsEntrypoint) (s : State) : option ReturnType :=
    match ep with 
    | set_payment_address p => 
        let new_quorom := FMap.update p.(sparam_signer) (Some p.(payment_address)) s.(fees).(fees_storage_signers) in
        Some (s<|fees:= s.(fees)<|fees_storage_signers := new_quorom|>|>, [])
    end.

End SignerOps.