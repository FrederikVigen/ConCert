Require Import ZArith.
Require Import Blockchain.
Require Import Containers.
Require Import List.
Require Import RecordUpdate.
Require Import FA2Types.
Require Import FA2InterfaceOwn.
Require Import TokenAdmin.
Require Import Monads.
Import ListNotations.

Open Scope N_scope.

Section MultiTokenAdmin.
Context {BaseTypes : ChainBase}.

Definition create_token (metadata : TokenMetadata) (storage : MultiTokenStorage) : option MultiTokenStorage :=
    let new_token_id := metadata.(tm_token_id) in
    let existing_meta := FMap.find new_token_id storage.(token_metadata) in
    match existing_meta with
    | Some _ => None
    | None =>
        let meta := FMap.update new_token_id (Some metadata) storage.(token_metadata) in
        let supply := FMap.update new_token_id (Some 0) storage.(token_total_supply) in
        Some (storage<|token_metadata := meta|><|token_total_supply := supply|>)
    end.

Definition multi_token_admin_main (ctx : ContractCallContext) (p : MultiTokenAdmin) (s: MultiAssetStorage) : option Return := 
    match p with
    | Token_admin p =>
        do tpl <- token_admin ctx p s.(fa2_admin) ;
        let new_s := s<|fa2_admin:= (fst tpl) |> in
        Some (new_s, snd tpl)
    | Create_token p =>
        do res <- create_token p s.(fa2_assets) ;
        Some (s<|fa2_assets:= res |>, [])
    end.

End MultiTokenAdmin. 