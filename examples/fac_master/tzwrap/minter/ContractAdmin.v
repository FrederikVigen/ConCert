Require Import Storage.
Require Import Blockchain.
Require Import List.
Require Import Automation.
Require Import Serializable.
From ConCert.Execution Require Import Monads.
Import ListNotations.
From ConCert.Utils Require Import RecordUpdate.

Section ContractAdmin.
Context {BaseTypes : ChainBase}.

Inductive ContractAdminEntrypoints :=
    | SetAdministrator (addr : Address)
    | ConfirmMinterAdmin
    | SetOracle (addr : Address)
    | SetSigner (addr : Address)
    | PauseContract (pause : bool).

Global Instance ContractAdminEntrypoints_serializable : Serializable ContractAdminEntrypoints :=
    Derive Serializable ContractAdminEntrypoints_rect<SetAdministrator, ConfirmMinterAdmin, SetOracle, SetSigner, PauseContract>.

Definition ContractAdminReturnType : Type := (list ActionBody * ContractAdminStorage).

Definition fail_if_not_admin (ctx : ContractCallContext) (s : ContractAdminStorage) : option unit :=
    if address_eqb s.(administrator) ctx.(ctx_from) then Some tt else None.

Definition fail_if_not_signer (ctx : ContractCallContext) (s : ContractAdminStorage) : option unit :=
    if address_eqb s.(signer) ctx.(ctx_from) then Some tt else None.

Definition fail_if_not_oracle (ctx : ContractCallContext) (s : ContractAdminStorage) : option unit :=
    if address_eqb s.(oracle) ctx.(ctx_from) then Some tt else None.

Definition set_administrator (s : ContractAdminStorage) (new_administrator : Address) : ContractAdminReturnType :=
    ([],s<|administrator := new_administrator|>).

Definition set_signer (s : ContractAdminStorage) (new_signer : Address) : ContractAdminReturnType :=
    ([],s<|signer:=new_signer|>).

Definition pause (s : ContractAdminStorage) (p : bool) : ContractAdminReturnType :=
    ([],s<|paused:=p|>).

Definition confirm_new_minter_admin (ctx : ContractCallContext) (s : ContractAdminStorage) : option ContractAdminReturnType :=
    match s.(pending_admin) with
    | Some pending_admin_curr => 
        if address_eqb pending_admin_curr ctx.(ctx_from) then
        Some ([], s<|pending_admin:=None|><|administrator:=ctx.(ctx_from)|>)
        else None
    | None => None
    end.

Definition contract_admin_main (ctx: ContractCallContext) (p : ContractAdminEntrypoints) (s : ContractAdminStorage) : option ContractAdminReturnType :=
    match p with 
    | SetAdministrator n => 
        do _ <- fail_if_not_admin ctx s;
        Some (set_administrator s n)
    | SetOracle n =>
        do _  <- fail_if_not_admin ctx s;
        Some ([], s<|oracle := n|>)
    | SetSigner n =>
        do _ <- fail_if_not_admin ctx s;
        Some (set_signer s n)
    | ConfirmMinterAdmin => confirm_new_minter_admin ctx s
    | PauseContract p => 
        do _ <- fail_if_not_admin ctx s;
        Some (pause s p )
    end.

Lemma set_administrator_fail_if_not_admin {ctx n state} :
    ctx.(ctx_from) <> state.(administrator) ->
    contract_admin_main ctx (SetAdministrator n) state = None.
Proof.
    intros. cbn. unfold fail_if_not_admin. destruct_address_eq; try easy.
Qed.

Lemma set_oracle_fail_if_not_admin {ctx n state} :
    ctx.(ctx_from) <> state.(administrator) ->
    contract_admin_main ctx (SetOracle n) state = None.
Proof.
    intros. cbn. unfold fail_if_not_admin. destruct_address_eq; try easy.
Qed.

Lemma set_signer_fail_if_not_admin {ctx n state} :
    ctx.(ctx_from) <> state.(administrator) ->
    contract_admin_main ctx (SetSigner n) state = None.
Proof.
    intros. cbn. unfold fail_if_not_admin. destruct_address_eq; try easy.
Qed.

Lemma pause_contract_fail_if_not_admin {ctx p state} :
    ctx.(ctx_from) <> state.(administrator) ->
    contract_admin_main ctx (PauseContract p) state = None.
Proof.
    intros. cbn. unfold fail_if_not_admin. destruct_address_eq; try easy.
Qed.

End ContractAdmin.