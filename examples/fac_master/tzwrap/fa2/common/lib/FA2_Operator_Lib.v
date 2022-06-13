(** * FA2 Operator Lib*)
(** This is an implementation of the following file

https://github.com/bender-labs/wrap-tz-contracts/blob/1655949e61b05a1c25cc00dcb8c1da9d91799f31/ligo/fa2/common/lib/fa2_operator_lib.mligo

It contains types for permissions
*)
Require Import FA2_Permissions_Descriptor.
Require Import Blockchain.
From ConCert.Examples.FA2 Require Import FA2Interface.
Require Import FA2Interface_Wrap.
Require Import Containers.
Require Import Monads.
Require Import Containers.
Require Import List.

Section FA2_Operator_Lib.

Context {BaseTypes : ChainBase}.

(** ** Storage for operators *)
Definition OperatorStorage := FMap (Address * (Address * token_id)) unit.

(** ** Update Operators*)
Definition update_operators (update : update_operator) (storage : OperatorStorage) : OperatorStorage :=
    match update with
    | add_operator op => FMap.update (op.(op_param_owner), (op.(op_param_operator), op.(op_param_token_id))) (Some tt) storage
    | remove_operator op => FMap.remove (op.(op_param_owner), (op.(op_param_operator), op.(op_param_token_id))) storage
    end.

(** ** Validate Update Operators By Owner*)
Definition validate_update_operators_by_owner (update : update_operator) (updater : Address) : option unit :=
    let op := match update with 
    | add_operator op => op
    | remove_operator op => op 
    end
    in
    if address_eqb op.(op_param_owner) updater then Some tt else None.

(** ** FA2 Update Operators*)
Definition fa2_update_operators (ctx : ContractCallContext) (updates : list update_operator) (storage : OperatorStorage) : option OperatorStorage :=
    let updater := ctx.(ctx_from) in
    let process_update := fun (ops_opt : option OperatorStorage) (update : update_operator) =>
        do ops <- ops_opt ;
        do _ <- validate_update_operators_by_owner update updater ;
        Some (update_operators update ops)
    in
    fold_left process_update updates (Some storage).

(** ** Operator Validator*)
Definition OperatorValidator := Address -> Address -> token_id -> OperatorStorage -> option unit.

(** ** Make Operator Validator*)
Definition make_operator_validator (tx_policy : OperatorTransferPolicy) : option OperatorValidator :=
    do can_tpl <- match tx_policy with 
    | NoTransfer => None
    | OwnerTransfer => Some (true, false)
    | OwnerOrOperatorTransfer => Some (true, true)
    end ;
    Some (fun (owner : Address) (operator : Address) (token_id : token_id) (ops_storage : OperatorStorage) =>
    if andb (fst can_tpl) (address_eqb owner operator) then Some tt
    else if negb (snd can_tpl) then None
    else do _ <- FMap.find (owner, (operator, token_id)) ops_storage ;
    Some tt).

(** ** Default Operator Validator*)
Definition default_operator_validator : OperatorValidator :=
    fun (owner: Address) (operator : Address) (token_id : token_id) (ops_storage : OperatorStorage) =>
    if address_eqb owner operator then Some tt
    else do _ <- FMap.find (owner, (operator, token_id)) ops_storage;
    Some tt.

(** ** Validate Operator*)
Definition validate_operator (ctx: ContractCallContext) (tx_policy: OperatorTransferPolicy) (transfers: list transfer) (ops_storage : OperatorStorage)  : option unit :=
    do validator <- make_operator_validator tx_policy ;
    fold_left (fun (acc_opt : option unit) (tx: transfer) => 
        do _ <- acc_opt ;
        fold_left (fun (acc_opt_inner : option unit) (dst : transfer_destination) =>
            do _ <- acc_opt_inner ;
            do _ <- validator tx.(from_) ctx.(ctx_from) dst.(dst_token_id) ops_storage ;
            Some tt 
        ) tx.(txs) (Some tt)
    ) transfers (Some tt).

End FA2_Operator_Lib.