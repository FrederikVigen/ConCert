Require Import Blockchain.
Require Import FA2InterfaceOwn.
Require Import RecordUpdate.
Require Import FA2Types.
Require Import MultiTokenAdmin.
Require Import TokenAdmin.
Require Import FA2_Multi_Token.
Require Import Token_Manager.
Require Import Monads.


Section FA2_Multi_Asset.
Context {BaseTypes : ChainBase}.

Inductive MultiAssetParam :=
| Assets (param : FA2EntryPoints)
| Admin (param : MultiTokenAdmin)
| Tokens (param : TokenManager).

Definition main (ctx : ContractCallContext) (param : MultiAssetParam) (s : MultiAssetStorage) : option Return :=
    match param with
    | Admin p => multi_token_admin_main ctx p s
    | Tokens p =>
        do _ <- fail_if_not_minter ctx s.(admin) ;
        do tpl <- token_manager p s.(assets) ;
        let new_s := s<| assets:= fst tpl |> in
        Some (new_s, snd tpl)
    | Assets p =>
        do _ <- fail_if_paused s.(admin) p ;
        do tpl <- fa2_main ctx p s.(assets) ;
        let new_s := s<| assets := fst tpl |> in
        Some (new_s, snd tpl)
    end.

End FA2_Multi_Asset.