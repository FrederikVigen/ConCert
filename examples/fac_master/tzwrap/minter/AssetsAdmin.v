(** * Asset Admins part of the Minter Contract *)
(** This file contains the implementation of the Assets Admin part of the Minter Contract
    The contracts handles all incoming calls that manages admin functionality for the assets. Such as for example changing the admin, minter or pausing tokens.
    The file this file has been translated from can be found here:
    https://github.com/bender-labs/wrap-tz-contracts/blob/1655949e61b05a1c25cc00dcb8c1da9d91799f31/ligo/minter/assets_admin.mligo 
*)

Require Import Tokens_Lib.
Require Import Blockchain.
Require Import FA2Interface_Wrap.
Require Import ZArith.
Require Import Storage.
Require Import List.
Require Import Serializable.

Section AssetsAdmin.
Context {BaseTypes : ChainBase}.

(** ** Parameters for the Pause_tokens endpoint *)
Record PauseTokensParam := mkPauseTokensParam {
    ptp_contract : Address;
    ptp_tokens : list N;
    ptp_paused : bool
}.

(** ** Asset Admin Entrypoints *)
Inductive AssetAdminentrypoints : Type :=
| Change_tokens_administrator (param : (Address  * list Address))
| Confirm_tokens_administrator (addrList : list Address)
| Pause_tokens (params : list PauseTokensParam).

(** ** The Return type *)
(** This type is return from all of the above entrypoints *)
Definition Return : Type := (list ActionBody * AssetsStorage).

(** ** Confirms a newly selected admin *)
Definition confirm_admin (p : list Address) (s : AssetsStorage) : Return :=
    let create_op : Address -> ActionBody :=
        fun (a : Address) =>
            act_call a 0 (serialize Confirm_admin) 
        in
    let ops := map create_op p in
    (ops, s).

(** ** Pauses a token  *)
Definition pause_tokens_in_contract (p : PauseTokensParam) : ActionBody :=
    let params := map (fun (token_id : N) => 
    {| pp_token_id := token_id ;
       pp_paused := p.(ptp_paused)
    |}) p.(ptp_tokens) in
    act_call p.(ptp_contract) 0 (serialize (Pause params)).

(** ** Pauses multiple tokens *)
Definition pause_tokens (p : list PauseTokensParam) (s : AssetsStorage) : Return :=
    let ops := map pause_tokens_in_contract p in
    (ops, s).

(** ** Change the tokens administrator *)
Definition change_tokens_administator (p : (Address * list Address)) (s : AssetsStorage) : Return :=
    let (new_admin, contracts) := p in
    let create_op : Address -> ActionBody :=
        fun (a : Address) =>
                act_call a 0 (serialize (Set_admin new_admin))
        in
    let ops := map create_op contracts in
    (ops, s).

(** ** The main entrypoint for the assets admin *)
Definition assets_admin_main (p : AssetAdminentrypoints) (s : AssetsStorage) : Return :=
    match p with
    | Change_tokens_administrator p => change_tokens_administator p s
    | Confirm_tokens_administrator p => confirm_admin p s
    | Pause_tokens p => pause_tokens p s
    end.

End AssetsAdmin.