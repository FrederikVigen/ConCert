Require Import Blockchain.
Require Import FA2InterfaceOwn.
Require Import RecordUpdate.
Require Import FA2Types.
Require Import MultiTokenAdmin.
Require Import TokenAdmin.


Section FA2_Multi_Asset.
Context {BaseTypes : ChainBase}.

Inductive MultiAssetParam :=
| Assets (param : FA2EntryPoints)
| Admin (param : MultiTokenAdmin)
| Tokens (param : TokenManager).

Definition main (param : MultiAssetParam) (s : MultiAssetStorage) : option Return :=
    match param with
    | Admin p => multi_token_admin_main p s
    | Tokens p =>
        let u1 := fail_if_not_minter s.(admin) in
        let (ops, assets) := token_manager p s.(assets) in
        let new_s := s<| assets:=assets |> in
        (new_s, ops)
    | Assets =>
        let u2 := fail_if_paused s.(admin) p in
        let (ops, assets) := fa2_main p s.(assets) in
        let new_s := s<| assets := assets |> in
        (new_s, ops)
    end.

End FA2_Multi_Asset.