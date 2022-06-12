Require Import Tokens_Lib.
Require Import Blockchain.
Require Import FA2Interface_Wrap.
Require Import ZArith.
Require Import Storage.
Require Import List.
Require Import Serializable.

Section AssetsAdmin.
Context {BaseTypes : ChainBase}.

Record PauseTokensParam := mkPauseTokensParam {
    ptp_contract : Address;
    ptp_tokens : list N;
    ptp_paused : bool
}.

Inductive AssetAdminentrypoints : Type :=
| Change_tokens_administrator (param : (Address  * list Address))
| Confirm_tokens_administrator (addrList : list Address)
| Pause_tokens (params : list PauseTokensParam).

Definition Return : Type := (list ActionBody * AssetsStorage).

Definition confirm_admin (p : list Address) (s : AssetsStorage) : Return :=
    let create_op : Address -> ActionBody :=
        fun (a : Address) =>
            act_call a 0 (serialize Confirm_admin) 
        in
    let ops := map create_op p in
    (ops, s).

Definition pause_tokens_in_contract (p : PauseTokensParam) : ActionBody :=
    let params := map (fun (token_id : N) => {| pp_token_id := token_id ; pp_paused := p.(ptp_paused) |}) p.(ptp_tokens) in
    act_call p.(ptp_contract) 0 (serialize (Pause params)).

Definition pause_tokens (p : list PauseTokensParam) (s : AssetsStorage) : Return :=
    let ops := map pause_tokens_in_contract p in
    (ops, s).

Definition change_tokens_administator (p : (Address * list Address)) (s : AssetsStorage) : Return :=
    let (new_admin, contracts) := p in
    let create_op : Address -> ActionBody :=
        fun (a : Address) =>
                act_call a 0 (serialize (Set_admin new_admin))
        in
    let ops := map create_op contracts in
    (ops, s).

Definition assets_admin_main (p : AssetAdminentrypoints) (s : AssetsStorage) : Return :=
    match p with
    | Change_tokens_administrator p => change_tokens_administator p s
    | Confirm_tokens_administrator p => confirm_admin p s
    | Pause_tokens p => pause_tokens p s
    end.

Lemma confirm_admin_correct {p state ops} :
    confirm_admin p state = (ops, state) ->
    length p = length ops.
Proof.
    intros. unfold confirm_admin in H. inversion H. rewrite map_length. reflexivity.
Qed.

End AssetsAdmin.