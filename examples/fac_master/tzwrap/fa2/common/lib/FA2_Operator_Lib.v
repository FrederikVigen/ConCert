Require Import FA2_Permissions_Descriptor.
Require Import Blockchain.
Require Import FA2Interface.
Require Import FA2InterfaceOwn.
Require Import Containers.
Require Import Monads.
Require Import Containers.
Require Import List.

Section FA2_Operator_Lib.

Context {BaseTypes : ChainBase}.

Definition OperatorStorage := FMap (Address * (Address * token_id)) unit.

Definition update_operators (update : update_operator_own) (storage : OperatorStorage) : OperatorStorage :=
    match update with
    | add_operator op => FMap.update (op.(op_param_owner), (op.(op_param_operator), op.(op_param_token_id))) (Some tt) storage
    | remove_operator op => FMap.remove (op.(op_param_owner), (op.(op_param_operator), op.(op_param_token_id))) storage
    end.

Definition validate_update_operators_by_owner (update : update_operator_own) (updater : Address) : option unit :=
    let op := match update with 
    | add_operator op => op
    | remove_operator op => op 
    end
    in
    if address_eqb op.(op_param_owner) updater then Some tt else None.

Definition fa2_update_operators (ctx : ContractCallContext) (updates : list update_operator_own) (storage : OperatorStorage) : option OperatorStorage :=
    let updater := ctx.(ctx_from) in
    let process_update := fun (update : update_operator_own) (ops_opt : option OperatorStorage) =>
        do ops <- ops_opt ;
        do _ <- validate_update_operators_by_owner update updater ;
        Some (update_operators update ops)
    in
    fold_right process_update (Some storage) updates.

Definition OperatorValidator := Address -> Address -> token_id -> OperatorStorage -> option unit.

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

Definition default_operator_validator : OperatorValidator :=
    fun (owner: Address) (operator : Address) (token_id : token_id) (ops_storage : OperatorStorage) =>
    if address_eqb owner operator then Some tt
    else do _ <- FMap.find (owner, (operator, token_id)) ops_storage;
    Some tt.

Definition validate_operator (ctx: ContractCallContext) (tx_policy: OperatorTransferPolicy) (transfers: list Transfer) (ops_storage : OperatorStorage)  : option unit :=
    do validator <- make_operator_validator tx_policy ;
    fold_right (fun (tx: Transfer) (acc_opt : option unit) => 
        do _ <- acc_opt ;
        fold_right (fun (dst : TransferDestination) (acc_opt_inner : option unit) =>
            do _ <- acc_opt_inner ;
            do _ <- validator tx.(from_) ctx.(ctx_from) dst.(dst_token_id) ops_storage ;
            Some tt 
        ) (Some tt) tx.(txs)
    ) (Some tt) transfers.

End FA2_Operator_Lib.