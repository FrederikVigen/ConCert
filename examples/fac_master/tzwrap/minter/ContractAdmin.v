(** * Contract admin part of the Minter Contract *)
(** This file contains the implementation of the Contract Admin part of the Minter Contract
    The contracts handles all incoming calls that manages admin functionality for the contract. Such as for example changing the new oracle, signer MinterAdmin and also a pause for the whole contract.
    The file this file has been translated from can be found here:
    https://github.com/bender-labs/wrap-tz-contracts/blob/1655949e61b05a1c25cc00dcb8c1da9d91799f31/ligo/minter/contract_admin.mligo
*)

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

(** ** The Entrypoints of the Contract Admin *)
Inductive ContractAdminEntrypoints :=
    | SetAdministrator (addr : Address)
    | ConfirmMinterAdmin
    | SetOracle (addr : Address)
    | SetSigner (addr : Address)
    | PauseContract (pause : bool).

(* begin hide *)
Global Instance ContractAdminEntrypoints_serializable : Serializable ContractAdminEntrypoints :=
    Derive Serializable ContractAdminEntrypoints_rect<SetAdministrator, ConfirmMinterAdmin, SetOracle, SetSigner, PauseContract>.
(* end hide *)

(** ** The Return type of all the Contract Admin Entrypoints *)
Definition ContractAdminReturnType : Type := (list ActionBody * ContractAdminStorage).

(** ** All the fail criteria for the entrypoints *)
(** Fail if the caller is not admin *)
Definition fail_if_not_admin (ctx : ContractCallContext) (s : ContractAdminStorage) : option unit :=
    if address_eqb s.(administrator) ctx.(ctx_from) then Some tt else None.

(** Fail if the caller is not a signer *)
Definition fail_if_not_signer (ctx : ContractCallContext) (s : ContractAdminStorage) : option unit :=
    if address_eqb s.(signer) ctx.(ctx_from) then Some tt else None.

(** Fail if the caller is not the oracle *)
Definition fail_if_not_oracle (ctx : ContractCallContext) (s : ContractAdminStorage) : option unit :=
    if address_eqb s.(oracle) ctx.(ctx_from) then Some tt else None.

(** ** Sets a new administrator *)
Definition set_administrator (s : ContractAdminStorage) (new_administrator : Address) : ContractAdminReturnType :=
    ([],s<|administrator := new_administrator|>).

(** ** Sets a new signer *)
Definition set_signer (s : ContractAdminStorage) (new_signer : Address) : ContractAdminReturnType :=
    ([],s<|signer:=new_signer|>).

(** ** Pause or unpause contract *)
Definition pause (s : ContractAdminStorage) (p : bool) : ContractAdminReturnType :=
    ([],s<|paused:=p|>).

(** ** Confirms a new admin *)
Definition confirm_new_minter_admin (ctx : ContractCallContext) (s : ContractAdminStorage) : option ContractAdminReturnType :=
    match s.(pending_admin) with
    | Some pending_admin_curr => 
        if address_eqb pending_admin_curr ctx.(ctx_from) then
        Some ([], s<|pending_admin:=None|><|administrator:=ctx.(ctx_from)|>)
        else None
    | None => None
    end.

(** ** The main entrypoint function *)
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

End ContractAdmin.