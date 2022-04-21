Require Import Blockchain.
Require Import Containers.
Require Import Automation.
Require Import Signer_Interface.
Require Import Oracle_Interface.
Require Import Signer_Ops_Interface.
Require Import ZArith.
Require Import String.
Require Import List.
Require Import FSets.
Require Import FSets.FMapList.
Require Import Structures.OrderedTypeEx.
Require Import Monads.
Require Import RecordUpdate.
Require Import Crypto.
Import ListNotations.
Require Import Common.
Require Import Serializable.
Require Import Tokens_Lib.
Require Import Permutation.

Open Scope N_scope.

Section Multisig.
Set Nonrecursive Elimination Schemes.
Context {BaseTypes : ChainBase}.

Definition SignerId: Type := string.

Definition Counter: Type := nat.

Definition Metadata: Type := FMap string N.

Record State : Type :=
    mkState {admin : Address ;
            pending_admin : option Address ;
            threshold : N ;
            signers : FMap SignerId N ;
            metadata : Metadata ; 
            counters : FMap SignerId nat}.

MetaCoq Run (make_setters State).

Record ContractInvocation : Type := 
    mkContractInvocation {entrypoint : SignerEntrypoints ;
            target : Address}.

Definition Signatures : Type := list (SignerId * N).

Record SignerAction : Type :=
    mkSignerAction {signatures : Signatures ;
            action : ContractInvocation}.
            
Global Instance ContractInvocation_serializable : Serializable ContractInvocation :=
    Derive Serializable ContractInvocation_rect<mkContractInvocation>.

Global Instance SignerAction_serializable : Serializable SignerAction :=
    Derive Serializable SignerAction_rect<mkSignerAction>.
    
Inductive AdminAction : Type :=
| ChangeQuorum (params : (N * (FMap SignerId N)))
| ChangeThreshold (n : N)
| SetAdmin (addr : Address)
| ConfirmAdmin.

Definition T1 : Type := (N * Address).

Definition Payload : Type := (T1 * ContractInvocation).

Definition get_key (id : SignerId) (signers : FMap SignerId N): option N :=
    FMap.find id signers.

Definition check_threshold (signatures : Signatures) (threshold : N) : option unit :=
    throwIf (N_of_nat (length signatures) <? threshold).

(*TODO: mock signature failures*)
Definition check_signature (p: (N * Address * ContractInvocation)) (signatures : Signatures) (threshold : N) (signers: (FMap SignerId N)) : option unit := 
    let iter := fun (elem : (SignerId * N)) (acc: N) =>
        let (i, signature) := elem in 
        let key := match get_key i signers with
            | Some n => n
            | None => 0
        end
        in
        (* Mock signature check *)
        if Crypto.check_signature key signature p then acc + 1 else acc
    in 
    let r := fold_right iter 0 signatures in
    throwIf (r <? threshold).

Definition apply_minter (ctx: ContractCallContext) (p: SignerAction) (s: State) : option (list ActionBody) :=
    do _ <- check_threshold p.(signatures) s.(threshold);
    let payload := ((0, ctx.(ctx_contract_address)), p.(action)) in
    do _ <- check_signature payload p.(signatures) s.(threshold) s.(signers);
    let action := p.(action) in
    Some [act_call action.(target) ctx.(ctx_amount) (serialize action.(entrypoint))].

Definition fail_if_not_admin (ctx: ContractCallContext) (s: State): option unit := 
    if address_eqb s.(admin) ctx.(ctx_from) then Some tt else None. 

Definition check_new_quorum (p: (N * FMap SignerId N)) : option unit :=
    let (t, signers) := p in
    if N_of_nat (length (FMap.elements signers)) <? t then None else
    let unique := fin_maps.map_fold
        (fun (key: SignerId) (elem: N) (acc : FMap SignerId unit) => FMap.add key tt acc)
        FMap.empty
        signers in
    if N_of_nat (length (FMap.elements unique)) =? N_of_nat (length (FMap.elements signers)) then Some tt else None.

Definition confirm_admin (ctx: ContractCallContext) (s: State) : option State :=
    do new_admin <- s.(pending_admin);
    if address_eqb new_admin ctx.(ctx_from)
    then Some (s<|pending_admin := None|><|admin := ctx.(ctx_from)|>)
    else None.

Definition apply_admin (ctx : ContractCallContext) (action : AdminAction) (s : State) : option State :=    
    match action with
    | ChangeQuorum params => 
        do _ <- fail_if_not_admin ctx s;
        do _ <- check_new_quorum params;
        let (t, new_signers) := params in
        Some (s<|threshold:=t|><|signers:=new_signers|>)
    | ChangeThreshold n =>
        do _ <- fail_if_not_admin ctx s;
        do _ <- throwIf ((N_of_nat (length (FMap.elements s.(signers))) <? n) || (n <? 1%N));
        Some (s<|threshold:=n|>)
    | SetAdmin a => 
        do _ <- fail_if_not_admin ctx s;
        Some (s<|pending_admin:= Some a|>)
    | ConfirmAdmin => confirm_admin ctx s
    end.

Record PaymentAddressParameter :=
    mkPaymentAddressParameter {
        pap_minter_contract : Address ;
        pap_signer_id : string ;
        pap_signature : N;
    }.

Record DistributeTokensParameter :=
    mkDistributeTokensParameter {
        dtp_minter_contract : Address ;
        dtp_tokens : list (Address * N)
    }.

Inductive FeesEntrypoints : Type :=
| Distribute_tokens_with_quorum (param : DistributeTokensParameter)
| Distribute_xtz_with_quorum (addr : Address).

Inductive MultisigParameter : Type :=
| Admin (admin_action : AdminAction)
| Minter (signer_action : SignerAction)
| Fees (fees_entrypoints : FeesEntrypoints)
| Set_signer_payment_address (payment_addres_parameter : PaymentAddressParameter).

Definition Return : Type := list ActionBody * State.

Definition signers_key_hash (s : State) : list N :=
    fin_maps.map_fold 
    (fun (key: SignerId) (elem: N) (acc : list N) => Crypto.hash_key elem :: acc)
    [] 
    s.(signers).

Definition set_payment_address_payload :Type := T1 * (N * (Address * Address)).

Definition set_payment_address (ctx : ContractCallContext) (p : PaymentAddressParameter) (s : State) : option Return :=
    do k <- FMap.find p.(pap_signer_id) s.(signers);
    let signer_counter := match FMap.find p.(pap_signer_id) s.(counters) with
    | Some n => N.of_nat n
    | None => 0
    end in

    let payload := ((ctx.(ctx_contract_address)), (signer_counter, (p.(pap_minter_contract), ctx.(ctx_from)))) in
    (* Mock signature check *)
    if Crypto.check_signature k p.(pap_signature) payload
    then
        let call := serialize (set_payment_address {| sparam_signer := Crypto.hash_key k; payment_address := ctx.(ctx_from) |}) in
        Some ([act_call p.(pap_minter_contract) 0 call], s<|signers:= FMap.update p.(pap_signer_id) (Some (signer_counter + 1)) s.(signers) |>)
    else
        None.

Definition fees_main (p : FeesEntrypoints) (s : State) : option Return :=
    match p with
    | Distribute_tokens_with_quorum param =>
        let keys := signers_key_hash s in
        let target := param.(dtp_minter_contract) in
        let call := serialize (Distribute_tokens {|dp_signers := keys; dp_tokens := param.(dtp_tokens)|}) in
        Some ([act_call target 0 call], s)
    | Distribute_xtz_with_quorum addr =>    
        let keys := signers_key_hash s in
        let target := addr in
        let call := serialize (Distribute_xtz keys) in
        Some ([act_call target 0 call], s)
    end.

Definition main (ctx : ContractCallContext) (p : MultisigParameter) (s : State) : option Return :=
    match p with
    | Admin action =>
        do _ <- fail_if_amount ctx;
        do res <- apply_admin ctx action s;
        Some ([], res)
    | Minter signer_action => 
        do res <- apply_minter ctx signer_action s;
        Some (res, s)
    | Fees fees_entrypoints =>
        do _ <- fail_if_amount ctx;
        fees_main fees_entrypoints s
    | Set_signer_payment_address payment_addres_parameter =>
        do _ <- fail_if_amount ctx;
        set_payment_address ctx payment_addres_parameter s
    end.

Lemma admin_fail_if_amount {ctx action state} :
    Z.lt 0 ctx.(ctx_amount) -> main ctx (Admin action) state = None.
Proof.
    intros. cbn. unfold fail_if_amount. destruct (0 <? ctx_amount ctx)%Z eqn: amount.
    - reflexivity.
    - apply Z.ltb_ge in amount. easy.
Qed.

Lemma fees_fail_if_amount {ctx fees_entrypoints state} :
    Z.lt 0 ctx.(ctx_amount) -> main ctx (Fees fees_entrypoints) state = None.
Proof.
    intros. cbn. unfold fail_if_amount. destruct (0 <? ctx_amount ctx)%Z eqn: amount.
    - reflexivity.
    - apply Z.ltb_ge in amount. easy.
Qed.

Lemma set_signer_payment_address_fail_if_amount {ctx payment_addres_parameter state} :
    Z.lt 0 ctx.(ctx_amount) -> main ctx (Set_signer_payment_address payment_addres_parameter) state = None.
Proof.
    intros. cbn. unfold fail_if_amount. destruct (0 <? ctx_amount ctx)%Z eqn: amount.
    - reflexivity.
    - apply Z.ltb_ge in amount. easy.
Qed.

Lemma admin_fail_if_not_admin {ctx action state} :
    Z.gt 0 ctx.(ctx_amount) ->
    ctx.(ctx_from) <> state.(admin) -> 
    action <> ConfirmAdmin ->
    main ctx (Admin action) state = None.
Proof.
    intros. cbn. unfold fail_if_amount. destruct (0 <? ctx_amount ctx)%Z.
    - auto.
    - cbn. unfold apply_admin. destruct action; unfold fail_if_not_admin; destruct_address_eq; try easy; cbn; reflexivity.
Qed.

Lemma check_new_quorum_threshold_not_met {t signerMap} :
    N.of_nat (length (FMap.elements signerMap)) < t ->
    check_new_quorum (t, signerMap) = None.
Proof.
    intros. cbn. destruct (N.of_nat (Datatypes.length (FMap.elements signerMap)) <? t) eqn: length. 
    - easy. 
    - apply N.ltb_ge in length. easy.
Qed.

Lemma confirm_admin_correct {ctx state state'} :
    state.(pending_admin) = Some ctx.(ctx_from) ->
    main ctx (Admin ConfirmAdmin) state = Some ([], state') ->
    state'.(pending_admin) = None /\ state'.(admin) = ctx.(ctx_from).
Proof.
    intro H. cbn. destruct fail_if_amount; try easy.
    rewrite H. destruct_address_eq; try easy. intros. inversion H0. easy.
Qed.

Lemma check_signature_aux {sigs} :
    fold_right 
    (fun (elem : SignerId * N) (acc : N) => let (_, _) := elem in acc + 1) 
        0 sigs = N.of_nat (length sigs).
Proof.
    induction sigs; try easy. cbn. rewrite IHsigs. easy.
Qed.

Lemma check_signature_is_correct {p sigs threshold signers} :
    (* 1 <= threshold /\ Threshold is stated to be larger than one in the main *)
    sigs <> [] /\ threshold <= N.of_nat (length sigs) -> 
    check_signature p sigs threshold signers = Some tt.
Proof. 
    intros. unfold check_signature. cbn. rewrite check_signature_aux. unfold throwIf.
        induction sigs; try easy.
        destruct (N.of_nat (Datatypes.length (a :: sigs)) <? threshold) eqn:E.
        + apply N.ltb_lt in E. cbn in H. inversion H. cbn in E. easy.
        + reflexivity.
Qed.


(* (* Lemma fmap_elems_empty : forall (f: FMap SignerId unit), 
     [] = FMap.elements f -> f = FMap.empty.
Proof.
    intros. induction f. cbn in H.  *)


Lemma add_unique_aux {signers} :
    Permutation (FMap.elements (fin_maps.map_fold
        (fun (key : SignerId) (_ : N) (acc : FMap SignerId unit) =>
        FMap.add key tt acc) FMap.empty signers)) (FMap.elements signers).
        (* <-> NoDup (FMap.elements signers). *)
Proof.
    split.
        - intros. admit.
        - intros. apply elements_of_list. inversion H.
            (* + cbn. *)

Lemma check_new_quorum_is_correct {t signers} :
    NoDup (FMap.elements signers) /\ t <= N.of_nat (length (FMap.elements signers)) ->
    check_new_quorum (t, signers) = Some tt.
Proof.
    intros. inversion H. cbn. 
        destruct (N.of_nat (Datatypes.length (FMap.elements signers)) <? t) eqn:E.
        - apply N.ltb_lt in E. easy.
        -  *)
        


End Multisig.