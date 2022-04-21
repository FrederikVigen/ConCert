Require Import Blockchain.
Require Import Storage.


Section Admin_Main.

Context {BaseTypes : ChainBase}.

Inductive admin_entrypoints :=
| Change_admin (addr : Address)
| Confirm_new_admin.

Definition check_admin (s : storage) (ctx : ContractCallContext) : option storage :=
    let admin := s.(admin) in
    if address_eqb ctx.(ctx_from) admin.(administrator)
    then None
    else Some s.

Definition change_admin (pending_admin : Address) (admin : admin)


End Section.