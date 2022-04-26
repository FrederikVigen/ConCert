Require Import Blockchain.
Require Import FA2InterfaceOwn.
Require Import RecordUpdate.
Require Import FA2Types.
Require Import MultiTokenAdmin.
Require Import TokenAdmin.
Require Import FA2_Multi_Token.
Require Import Token_Manager.
Require Import Monads.
Require Import ZArith.
Require Import Containers.
Require Import String.
Require Import List.
Require Import Serializable.


Section FA2_Multi_Asset.
Context {BaseTypes : ChainBase}.
Set Nonrecursive Elimination Schemes.

Inductive MultiAssetParam :=
| Assets (param : FA2EntryPoints)
| Admin (param : MultiTokenAdmin)
| Tokens (param : TokenManager).

Global Instance MultiAssetParam_serializable : Serializable MultiAssetParam :=
Derive Serializable MultiAssetParam_rect<Assets, Admin, Tokens>.

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

Definition fa2_receive (chain : Chain) (ctx : ContractCallContext) (state: MultiAssetStorage) (msg_opt : option MultiAssetParam) : option Return :=
    do msg <- msg_opt ;
    main ctx msg state.    

Definition fa2_init (chain : Chain) (ctx: ContractCallContext) (setup: ((Address * Address) * ((list TokenMetadata) * N))) : option MultiAssetStorage :=
    let (t1,t2) := setup in
    let (admin, minter) := t1 in
    let (tokens, meta_data_uri) := t2 in
    let meta := FMap.update EmptyString (Some meta_data_uri) FMap.empty in
    let token_metadata := fold_right (fun (token_metadata : TokenMetadata) (acc : TokenMetaDataStorage) => FMap.update token_metadata.(tm_token_id) (Some token_metadata) acc) FMap.empty tokens in
    let supply := fold_right (fun (token_metadata : TokenMetadata) (acc : TokenTotalSupply) => FMap.update token_metadata.(tm_token_id) (Some 0) acc) FMap.empty tokens in
    Some ({|
        admin := {|
            tas_admin := admin ;
            tas_pending_admin := None ;
            tas_paused := FMap.empty ;
            tas_minter := minter
        |} ;
        assets := {|
            ledger := FMap.empty ;
            operators := FMap.empty ;
            token_metadata := token_metadata ;
            token_total_supply := supply
        |} ;
        metadata := meta
    |}).

(** The FA2 Contract **)
Definition FA2_contract : Contract ((Address * Address) * ((list TokenMetadata) * N)) MultiAssetParam MultiAssetStorage :=
    build_contract fa2_init fa2_receive.

(** If token_id is not paused fail_if_paused is Some **)
(* Lemma token_id_is_not_paused {transfers transfer tx pausedTokenSet} :
    ~ In tx transfer.(txs) ->
    In transfer transfers ->
    FMap.find tx.(dst_token_id) pausedTokenSet = None -> 
    fail_if_paused_tokens transfers pausedTokenSet = Some tt.
Proof.
    intros. unfold fail_if_paused_tokens. cbn. apply In_split in H1. destruct H1. destruct H1. rewrite H1.
    apply In_split in H0. destruct H0. *)

(** If token_id is not paused fail_if_paused is Some **)
Lemma token_id_is_not_paused_inner : forall (txs : list TransferDestination) (pausedTokenSet: PausedTokensSet),
    forall txd', 
    (In txd' txs /\ FMap.find txd'.(dst_token_id) pausedTokenSet = None) ->
    fold_right 
    (fun (txd : TransferDestination) (acc_opt_inner : option unit) =>
    match acc_opt_inner with 
    | None => None
    | Some _ => 
        match FMap.find txd.(dst_token_id) pausedTokenSet with
        | Some _ => None
        | None => Some tt
        end
    end)
    (Some tt) txs = Some tt.
Proof.
    intros. induction txs.
    - try easy.
    - unfold fold_right.

    
(** Checks if the total supply stays the same after transfer **)
Lemma transfer_preserves_total_supply {prev_state next_state acts chain ctx transfers} :
    fa2_receive chain ctx prev_state (Some (Assets (FA2_Transfer transfers))) = Some (next_state, acts) ->
    prev_state.(assets).(token_total_supply) = next_state.(assets).(token_total_supply).
Proof.
    unfold fa2_receive. cbn.
    admit.

End FA2_Multi_Asset.