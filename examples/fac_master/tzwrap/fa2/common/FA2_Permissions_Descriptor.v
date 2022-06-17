(** * FA2 Permissions Descriptor*)
(** This is an implementation of the following file

https://github.com/bender-labs/wrap-tz-contracts/blob/1655949e61b05a1c25cc00dcb8c1da9d91799f31/ligo/fa2/common/fa2_permissions_descriptor.mligo

It contains types for permissions
*)
Require Import String.
Require Import Blockchain.

Section FA2_Permissions_Descriptor.

Context {BaseTypes : ChainBase}.

(** ** Inductive types for policies*)
Inductive OperatorTransferPolicy :=
    | NoTransfer
    | OwnerTransfer
    | OwnerOrOperatorTransfer.

Inductive OwnerHookPolicy :=
    | OwnerNoHook
    | OptionalOwnerHook
    | RequiredOwnerHook.

(** ** Custom Permission Policy*)
Record CustomPermissionPolicy := mkCustomPermissionPolicy {
    tag : string ;
    config_api : option Address
}.

(** ** Permission Descriptor*)
Record PermissionsDescriptor := mkPermissionsDescriptor {
    operator : OperatorTransferPolicy ;
    receiver : OwnerHookPolicy ; 
    sender : OwnerHookPolicy ;
    custom : CustomPermissionPolicy
}.

End FA2_Permissions_Descriptor.
