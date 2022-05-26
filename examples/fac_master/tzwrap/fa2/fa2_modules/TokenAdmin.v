Require Import Blockchain.
Require Import Containers.
Require Import FA2InterfaceOwn.
Require Import ZArith.
Require Import RecordUpdate.
Require Import List.
Require Import Monads.
Import ListNotations.
Require Import Serializable.

Section TokenAdmin.
Set Nonrecursive Elimination Schemes.
Context {BaseTypes : ChainBase}.

Definition PausedTokensSet : Type := FMap N unit.

Record TokenAdminStorage := {
    tas_admin : Address ;
    tas_pending_admin : option Address ;
    tas_paused : PausedTokensSet ;
    tas_minter : Address
}.

Global Instance TokenAdminStorage_serializable : Serializable TokenAdminStorage :=
Derive Serializable TokenAdminStorage_rect<Build_TokenAdminStorage>.


MetaCoq Run (make_setters TokenAdminStorage).

Definition set_admin (new_admin : Address) (s : TokenAdminStorage) :=
    s<| tas_pending_admin := Some new_admin |>.

Definition confirm_new_admin (ctx : ContractCallContext) (s : TokenAdminStorage) : option TokenAdminStorage :=
    match s.(tas_pending_admin) with
    | None => None
    | Some pending =>
        if address_eqb ctx.(ctx_from) pending 
        then
            Some (s<| tas_pending_admin := None |><| tas_admin := ctx.(ctx_from) |>)
        else
            None
    end.

Definition pause (tokens : list PauseParam) (s : TokenAdminStorage) :=
    let new_paused := fold_left
        (fun (paused_set : PausedTokensSet) (t : PauseParam) =>
            if t.(pp_paused)
            then FMap.add t.(pp_token_id) tt paused_set
            else FMap.remove t.(pp_token_id) paused_set

        )
        tokens s.(tas_paused) in
    s<| tas_paused := new_paused |>.

Definition fail_if_not_admin (ctx : ContractCallContext) (a : TokenAdminStorage) : option TokenAdminStorage :=
    if address_eqb ctx.(ctx_from) a.(tas_admin)
    then Some a
    else None.

Definition fail_if_not_minter (ctx : ContractCallContext) (a : TokenAdminStorage) : option TokenAdminStorage :=
    if address_eqb ctx.(ctx_from) a.(tas_minter)
    then Some a
    else None.

Definition fail_if_paused_tokens (transfers : list Transfer) (paused : PausedTokensSet) : option unit :=
    fold_left
    ( fun (acc_opt : option unit) (tx : Transfer) =>
        do _ <- acc_opt ;
        fold_left (fun (acc_opt_inner : option unit) (txd : TransferDestination) =>
            do _ <- acc_opt_inner ;
            match FMap.find txd.(dst_token_id) paused with
            | Some _ => None
            | None => Some tt
            end
        ) tx.(txs) (Some tt)
    ) transfers (Some tt). 

Definition fail_if_paused (a : TokenAdminStorage) (param : FA2EntryPoints) :=
    match param with
    | Balance_of _ => Some tt
    | Update_operators _ => Some tt
    | FA2_Transfer transfer => fail_if_paused_tokens transfer a.(tas_paused)
    end.

Definition token_admin (ctx : ContractCallContext) (param : TokenAdmin) (s : TokenAdminStorage) : option (TokenAdminStorage * (list ActionBody)) :=
    match param with
    | Set_admin new_admin =>
        do s <- fail_if_not_admin ctx s ;
        let new_s := set_admin new_admin s in
        Some (new_s, [])
    | Confirm_admin =>
        do new_s <- confirm_new_admin ctx s ;
        Some (new_s, [])
    | Pause tokens =>
        do s <- fail_if_not_admin ctx s ;
        let new_s := pause tokens s in
        Some (new_s, [])
    | Set_minter p =>
        do s <- fail_if_not_admin ctx s ;
        Some (s<| tas_minter := p |>, [])
    end.
End TokenAdmin.