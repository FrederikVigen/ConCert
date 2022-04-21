Require Import Storage.
Require Import Fees.
Require Import Fees_Interface.
Require Import Blockchain.
Require Import Storage.
Require Import Unwrap.
Require Import ContractAdmin.
Require Import Monads.
Require Import RecordUpdate.
Require Import Tokens_Lib.
Require Import Common.
Require Import Governance_Interface.
Require Import Governance.
Require Import Oracle_Interface.
Require Import Oracle.
Require Import Signer_Interface.
Require Import Signer.
Require Import Signer_Ops_Interface.
Require Import SignerOps.

Section Main.

Context {BaseTypes : ChainBase}.

Inductive EntryPoints :=
    | Fees (fees_entrypoints : WithdrawalEntrypoint)
    | Unwrap (unwrap_entrypoints : UnwrapEntrypoints)
    | ContractAdmin (contract_admin_entrypoints : ContractAdminEntrypoints)
    | Governance (governance_entrypoints : GovernanceEntrypoints)
    | Oracle (oracle_entrypoints : OracleEntrypoint)
    | Signer (signer_entrypoints : SignerEntrypoints)
    | Signer_Ops (signer_ops_entrypoints : SignerOpsEntrypoint)
.

Definition fail_if_paused (s : ContractAdminStorage) : option unit :=
    throwIf (s.(paused)).

Definition main (ctx: ContractCallContext) (p: EntryPoints) (s : State) : option ReturnType :=
    match p with
    | Signer p =>
        do _ <- fail_if_not_signer ctx s.(admin) ;
        do _ <- fail_if_paused s.(admin) ; 
        signer_main ctx p s
    | Unwrap p =>
        do _ <- fail_if_paused s.(admin);
        unwrap_main ctx p s
    | ContractAdmin p =>
        do _ <- fail_if_amount ctx;
        do res <- contract_admin_main ctx p s.(admin);
        Some (fst res, s<|admin:= snd res|>)
    | Governance p => 
        do _ <- fail_if_amount ctx ;
        do _ <- fail_if_not_governance ctx s.(governance) ;
        do res <- governance_main ctx p s.(governance) ;
        Some (fst res, s<|governance := snd res|>)
    | Fees p => 
        do _ <- fail_if_amount ctx;
        fees_main ctx s p
    | Oracle p =>
        do _ <- fail_if_amount ctx ;
        do _ <- fail_if_not_oracle ctx s.(admin) ;
        oracle_main ctx p s
    | Signer_Ops p => 
        do _ <- fail_if_amount ctx ;
        do _ <- fail_if_not_signer ctx s.(admin) ; 
        signer_ops_main ctx p s
    end.

End Main.