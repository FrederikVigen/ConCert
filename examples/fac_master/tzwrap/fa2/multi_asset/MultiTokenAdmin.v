(** * Multi Token Admin *)
(** This is an implementation of the following file.

https://github.com/bender-labs/wrap-tz-contracts/blob/master/ligo/fa2/multi_asset/MultiTokenAdmin.mligo.

Entrypoints for creating tokens and managing the contract

*)

Require Import ZArith.
Require Import Blockchain.
Require Import Containers.
Require Import List.
Require Import RecordUpdate.
Require Import FA2Types.
Require Import FA2Interface_Wrap.
From ConCert.Examples.FA2 Require Import FA2Interface.
Require Import TokenAdmin.
Require Import Monads.
Import ListNotations.

Open Scope N_scope.
(** * Implementation *)

Section MultiTokenAdmin.
Context {BaseTypes : ChainBase}.

(** ** Create token *)
Definition create_token (metadata : token_metadata) (storage : MultiTokenStorage) : option MultiTokenStorage :=
    let new_token_id := metadata.(metadata_token_id) in
    let existing_meta := FMap.find new_token_id storage.(mts_token_metadata) in
    match existing_meta with
    | Some _ => None
    | None =>
        let meta := FMap.update new_token_id (Some metadata) storage.(mts_token_metadata) in
        let supply := FMap.update new_token_id (Some 0) storage.(token_total_supply) in
        Some (storage<|mts_token_metadata := meta|><|token_total_supply := supply|>)
    end.

(** ** Main entry point *)
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