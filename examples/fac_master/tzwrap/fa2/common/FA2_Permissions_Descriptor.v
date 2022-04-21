Require Import String.
Require Import Blockchain.

Section FA2_Permissions_Descriptor.

Context {BaseTypes : ChainBase}.

Inductive OperatorTransferPolicy :=
    | NoTransfer
    | OwnerTransfer
    | OwnerOrOperatorTransfer.

Inductive OwnerHookPolicy :=
    | OwnerNoHook
    | OptionalOwnerHook
    | RequiredOwnerHook.

Record CustomPermissionPolicy := mkCustomPermissionPolicy {
    tag : string ;
    config_api : option Address
}.

Record PermissionsDescriptor := mkPermissionsDescriptor {
    operator : OperatorTransferPolicy ;
    receiver : OwnerHookPolicy ; 
    sender : OwnerHookPolicy ;
    custom : CustomPermissionPolicy
}.

End FA2_Permissions_Descriptor.
