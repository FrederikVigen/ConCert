(** * Quorum Multisig Contract *)
(** This is an implementation of the Quorum Contract (multisig.mligo)
https://github.com/bender-labs/wrap-tz-contracts/blob/master/ligo/quorum/multisig.mligo.

It is used as the main entrypoint to wrap assets and change properties of the protocol.
*)
Require Import Blockchain.
Require Import Containers.
Require Import Automation.
Require Import Signer_Interface.
Require Import Oracle_Interface.
Require Import SignerOps_Interface.
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
Require Import ContractCommon.
Require Import Serializable.
Require Import Tokens_Lib.
Require Import Permutation.

Open Scope N_scope.

(** * Types *)
Section Multisig.
Set Nonrecursive Elimination Schemes.
Context {BaseTypes : ChainBase}.

Definition SignerId: Type := string.

Definition Counter: Type := nat.

Definition Metadata: Type := FMap string N.

(** ** Storage types *)
Record Setup := 
    mkSetup {
    s_admin : Address;
    s_threshold : N;
    s_signers : FMap SignerId N;
    s_metadata : Metadata
}.

Record State :=
    mkState {
        admin : Address ;
        pending_admin : option Address ;
        threshold : N ;
        signers : FMap SignerId N ;
        metadata : Metadata ; 
        counters : FMap SignerId nat
}.

Record ContractInvocation : Type := 
    mkContractInvocation {entrypoint : SignerEntrypoints ;
            target : Address}.

Definition T1 : Type := (N * Address).

Definition Payload : Type := (T1 * ContractInvocation).

Definition Signatures : Type := list (SignerId * N).

Record SignerAction : Type :=
    mkSignerAction {signatures : Signatures ;
            action : ContractInvocation}.

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

(** ** Entrypoint types *)

Inductive AdminAction :=
| ChangeQuorum (params : (N * (FMap SignerId N)))
| ChangeThreshold (n : N)
| SetAdmin (addr : Address)
| ConfirmAdmin.

Inductive FeesEntrypoints : Type :=
| Distribute_tokens_with_quorum (param : DistributeTokensParameter)
| Distribute_xtz_with_quorum (addr : Address).

Inductive MultisigParameter :=
| Admin (admin_action : AdminAction)
| Minter (signer_action : SignerAction)
| Fees (fees_entrypoints : FeesEntrypoints)
| Set_signer_payment_address (payment_addres_parameter : PaymentAddressParameter).

(* begin hide *)

Global Instance PaymentAddressParameter_serializable : Serializable PaymentAddressParameter :=
Derive Serializable PaymentAddressParameter_rect<mkPaymentAddressParameter>.

Global Instance DistributeTokensParameter_serializable : Serializable DistributeTokensParameter :=
Derive Serializable DistributeTokensParameter_rect<mkDistributeTokensParameter>.

Global Instance FeesEntrypoints_serializable : Serializable FeesEntrypoints :=
Derive Serializable FeesEntrypoints_rect<Distribute_tokens_with_quorum, Distribute_xtz_with_quorum>.

Global Instance AdminAction_serializable : Serializable AdminAction :=
Derive Serializable AdminAction_rect<ChangeQuorum, ChangeThreshold, SetAdmin, ConfirmAdmin>.
          
Global Instance ContractInvocation_serializable : Serializable ContractInvocation :=
Derive Serializable ContractInvocation_rect<mkContractInvocation>.

Global Instance SignerAction_serializable : Serializable SignerAction :=
Derive Serializable SignerAction_rect<mkSignerAction>.

Global Instance MultisigParameter_serializable : Serializable MultisigParameter :=
Derive Serializable MultisigParameter_rect<Admin, Minter, Fees, Set_signer_payment_address>.

Global Instance Setup_serializable : Serializable Setup :=
Derive Serializable Setup_rect<mkSetup>.

Global Instance State_serializable : Serializable State :=
Derive Serializable State_rect<mkState>.

MetaCoq Run (make_setters State).

(* end hide *)

(** * Entrypoints implementation *)

(** ** Minter *)

Definition get_key (id : SignerId) (signers : FMap SignerId N): option N :=
    FMap.find id signers.

Definition check_threshold (signatures : Signatures) (threshold : N) : option unit :=
    throwIf (N_of_nat (length signatures) <? threshold).

Definition check_signature (p: (N * Address * ContractInvocation)) (signatures : Signatures) (threshold : N) (signers: (FMap SignerId N)) : option unit := 
    let iter := fun (acc: N) (elem : (SignerId * N)) =>
        let (i, signature) := elem in 
        let key := match get_key i signers with
            | Some n => n
            | None => 0
        end
        in
        (* Mock signature check *)
        if Crypto.check_signature key signature p then acc + 1 else acc
    in 
    let r := fold_left iter signatures 0 in
    throwIf (r <? threshold).

Definition apply_minter (ctx: ContractCallContext) (p: SignerAction) (s: State) : option (list ActionBody) :=
    do _ <- check_threshold p.(signatures) s.(threshold);
    let payload := ((0, ctx.(ctx_contract_address)), p.(action)) in
    do _ <- check_signature payload p.(signatures) s.(threshold) s.(signers);
    let action := p.(action) in
    Some [act_call action.(target) ctx.(ctx_amount) (serialize action.(entrypoint))].

(** ** Admin *)
Definition fail_if_not_admin (ctx: ContractCallContext) (s: State): option unit := 
    if address_eqb s.(admin) ctx.(ctx_from) then Some tt else None. 

Definition check_new_quorum (p: (N * FMap SignerId N)) : option unit :=
    let (t, signers) := p in
    if N_of_nat (length (FMap.elements signers)) <? t then None else
    let unique := fin_maps.map_fold
        (fun (key: SignerId) (elem: N) (acc : FMap N unit) => FMap.add elem tt acc)
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

(** ** Fees *)
Definition Return : Type := State * list ActionBody.

Definition signers_key_hash (s : State) : list N :=
    fin_maps.map_fold 
    (fun (key: SignerId) (elem: N) (acc : list N) => Crypto.hash_key elem :: acc)
    [] 
    s.(signers).

Definition set_payment_address_payload :Type := T1 * (N * (Address * Address)).

Definition set_payment_address (ctx : ContractCallContext) (p : PaymentAddressParameter) (s : State) : option Return :=
    do k <- FMap.find p.(pap_signer_id) s.(signers);
    let signer_counter := match FMap.find p.(pap_signer_id) s.(counters) with
    | Some n => n
    | None => 0%nat
    end in

    let payload := ((ctx.(ctx_contract_address)), (signer_counter, (p.(pap_minter_contract), ctx.(ctx_from)))) in
    (* Mock signature check *)
    if Crypto.check_signature k p.(pap_signature) payload
    then
        let call := serialize (set_payment_address {| sparam_signer := Crypto.hash_key k; payment_address := ctx.(ctx_from) |}) in
        Some (s<|counters:= FMap.update p.(pap_signer_id) (Some (signer_counter + 1%nat)%nat)  s.(counters)|>, [act_call p.(pap_minter_contract) 0 call])
    else
        None.

Definition fees_main (p : FeesEntrypoints) (s : State) : option Return :=
    match p with
    | Distribute_tokens_with_quorum param =>
        let keys := signers_key_hash s in
        let target := param.(dtp_minter_contract) in
        let call := serialize (Distribute_tokens {|dp_signers := keys; dp_tokens := param.(dtp_tokens)|}) in
        Some (s, [act_call target 0 call])
    | Distribute_xtz_with_quorum addr =>    
        let keys := signers_key_hash s in
        let target := addr in
        let call := serialize (Distribute_xtz keys) in
        Some (s, [act_call target 0 call])
    end.


(** ** Contract main entrypoints *)
Definition main (ctx : ContractCallContext) (p : MultisigParameter) (s : State) : option Return :=
    match p with
    | Admin action =>
        do _ <- fail_if_amount ctx;
        do res <- apply_admin ctx action s;
        Some (res, [])
    | Minter signer_action => 
        do res <- apply_minter ctx signer_action s;
        Some (s, res)
    | Fees fees_entrypoints =>
        do _ <- fail_if_amount ctx;
        fees_main fees_entrypoints s
    | Set_signer_payment_address payment_addres_parameter =>
        do _ <- fail_if_amount ctx;
        set_payment_address ctx payment_addres_parameter s
    end.

Definition multisig_receive (chain : Chain) (ctx : ContractCallContext) (state : State) (msg_opt : option MultisigParameter) : option Return :=
    do msg <- msg_opt ;
    main ctx msg state.

Definition multisig_init (chain : Chain) (ctx : ContractCallContext) (setup : Setup) : option State :=
    Some {| admin:=setup.(s_admin);
            threshold:=setup.(s_threshold);
            pending_admin:=None;
            metadata:=setup.(s_metadata);
            signers:=setup.(s_signers);
            counters:=FMap.empty |}.

(** The multisig contract *)
Definition multisig_contract : Contract Setup MultisigParameter State :=
build_contract multisig_init multisig_receive.

End Multisig.

(** * Proofs *)
(** ** Safety proofs *)
Section SafetyProofs.

Context {BaseTypes : ChainBase}.

(** ** Admin endpoints fail if amount in transaction *)
Lemma admin_fail_if_amount {ctx chain action state} :
    Z.lt 0 ctx.(ctx_amount) -> 
    multisig_receive chain ctx state (Some (Admin action)) = None.
Proof.
    intros. cbn. unfold fail_if_amount. destruct (0 <? ctx_amount ctx)%Z eqn: amount.
    - reflexivity.
    - apply Z.ltb_ge in amount. easy.
Qed.

(** ** Fees endpoints fail if amount in transaction *)
Lemma fees_fail_if_amount {ctx chain fees_entrypoints state} :
    Z.lt 0 ctx.(ctx_amount) -> 
    multisig_receive chain ctx state (Some (Fees fees_entrypoints)) = None.
Proof.
    intros. cbn. unfold fail_if_amount. destruct (0 <? ctx_amount ctx)%Z eqn: amount.
    - reflexivity.
    - apply Z.ltb_ge in amount. easy.
Qed.

(** ** Set signer payment address fail if amount in transaction *)
Lemma set_signer_payment_address_fail_if_amount {ctx chain payment_addres_parameter state} :
    Z.lt 0 ctx.(ctx_amount) -> 
    multisig_receive chain ctx state (Some (Set_signer_payment_address payment_addres_parameter)) = None.
Proof.
    intros. cbn. unfold fail_if_amount. destruct (0 <? ctx_amount ctx)%Z eqn: amount.
    - reflexivity.
    - apply Z.ltb_ge in amount. easy.
Qed.

(** ** Admin entrypoints fail if not called by admin *)
Lemma admin_fail_if_not_admin {ctx chain action state} :
    ctx.(ctx_from) <> state.(admin) -> 
    action <> ConfirmAdmin ->
    multisig_receive chain ctx state (Some (Admin action)) = None.
Proof.
    intros. contract_simpl multisig_receive multisig_init. destruct (fail_if_amount ctx); try easy.
    unfold apply_admin. destruct action; unfold fail_if_not_admin; destruct_address_eq; try easy; cbn; reflexivity.
Qed.

(** ** Check new quorum fails if threshold is not met *)
Lemma check_new_quorum_threshold_not_met {t signerMap} :
    N.of_nat (length (FMap.elements signerMap)) < t ->
    check_new_quorum (t, signerMap) = None.
Proof.
    intros. cbn. destruct (N.of_nat (Datatypes.length (FMap.elements signerMap)) <? t) eqn: length. 
    - easy. 
    - apply N.ltb_ge in length. easy.
Qed. 

(** ** Helper lemmas *)
Lemma length_plus_1 {A : Type} {l : list A} {a : A} :
    N.of_nat (length (a :: l)) = 1 + N.of_nat(length l).
Proof.
    induction l; cbn; easy.
Qed.

Lemma check_signature_aux {sigs n} :
    fold_left 
    (fun (acc : N) (elem : SignerId * N) => let (_, _) := elem in acc + 1) 
        sigs n = N.of_nat (length sigs) + n.
Proof.
    generalize dependent n. induction sigs; try easy. rewrite length_plus_1.
    cbn. intros. rewrite IHsigs. destruct a. easy.
Qed.

Lemma check_signature_aux_0 {sigs} :
    fold_left 
    (fun (acc : N) (elem : SignerId * N) => let (_, _) := elem in acc + 1) 
        sigs 0 = N.of_nat (length sigs).
Proof.
    intros. rewrite check_signature_aux; easy.
Qed.

(** ** Check signature is correct *)
Lemma check_signature_is_correct {p sigs threshold signers} :
    sigs <> [] /\ threshold <= N.of_nat (length sigs) -> 
    check_signature p sigs threshold signers = Some tt.
Proof. 
    intros. unfold check_signature. cbn. rewrite check_signature_aux_0. unfold throwIf.
        induction sigs; try easy.
        destruct (N.of_nat (Datatypes.length (a :: sigs)) <? threshold) eqn:E.
        - apply N.ltb_lt in E. cbn in H. inversion H. cbn in E. easy.
        - reflexivity.
Qed.

(** ** Set admin preserves threshold and signers *)
Lemma set_admin_preserves_threshold_signers {chain ctx prev_state addr next_state acts} :
    multisig_receive chain ctx prev_state (Some (Admin (SetAdmin addr))) = Some (next_state, acts) ->
    prev_state.(threshold) = next_state.(threshold) /\
    prev_state.(signers) = next_state.(signers).
Proof.
    intros. contract_simpl multisig_receive multisig_init.
    split; try easy.
Qed.

(** ** Confirm admin preserves threshold and signers *)
Lemma confirm_admin_preserves_threshold_signers {chain ctx prev_state next_state acts} :
    multisig_receive chain ctx prev_state (Some (Admin ConfirmAdmin)) = Some (next_state, acts) ->
    prev_state.(threshold) = next_state.(threshold) /\
    prev_state.(signers) = next_state.(signers).
Proof.
    intros. contract_simpl multisig_receive multisig_init.
    split; try easy.
Qed.

(** ** Set signer payment address preserves threshold and signers *)
Lemma set_signer_payment_address_preserves_threshold_signers {chain ctx prev_state next_state acts param} :
multisig_receive chain ctx prev_state (Some (Set_signer_payment_address param)) = Some (next_state, acts) ->
    prev_state.(threshold) = next_state.(threshold) /\
    prev_state.(signers) = next_state.(signers).
Proof.
    intros. contract_simpl multisig_receive multisig_init.
    split; try easy.
Qed.

(** ** Fees entrypoint does not change the state *)
Lemma fees_preserves_state {chain ctx prev_state next_state acts entrypoint} :
    multisig_receive chain ctx prev_state (Some (Fees entrypoint)) = Some (next_state, acts) -> 
    prev_state = next_state.
Proof.
    intros. destruct entrypoint; contract_simpl multisig_receive multisig_init.
Qed.

(** ** Apply minter endpoints does not change the state *)
Lemma apply_minter_preserves_state {chain ctx prev_state next_state signer_action acts} :
    multisig_receive chain ctx prev_state (Some (Minter signer_action)) =
    Some (next_state, acts) ->
    prev_state = next_state.
Proof.
    intros. contract_simpl multisig_receive multisig_init.
Qed.

(** ** Apply minter fails if below threshold *)
Lemma apply_minter_fails_if_below_threshold {chain ctx prev_state signer_action sigs} :
    signer_action.(signatures) = sigs ->
    N_of_nat (length sigs) < prev_state.(threshold) ->
    multisig_receive chain ctx prev_state (Some (Minter signer_action)) = None.
Proof.
    intros. contract_simpl multisig_receive multisig_init. destruct (check_threshold (signatures signer_action) (threshold prev_state)); try easy.
    unfold check_signature. cbn. rewrite H. rewrite <- N.ltb_lt in H0. rewrite check_signature_aux. rewrite N.add_0_r. rewrite H0. easy.
Qed. 

(** ** Threshold is always lower than or equal to amount of signers *)
Lemma threshold_always_lower_than_or_eq_signers : forall bstate caddr (trace : ChainTrace empty_state bstate),
    reachable bstate ->
    env_contracts bstate caddr = Some (multisig_contract : WeakContract) ->
    exists cstate depinfo,
        contract_state bstate caddr = Some cstate /\
        deployment_info Setup trace caddr = Some depinfo /\
        ( depinfo.(deployment_setup).(s_threshold) <=  N.of_nat (length (FMap.elements depinfo.(deployment_setup).(s_signers))) ->
          cstate.(threshold) <= N.of_nat (length (FMap.elements cstate.(signers))) ).
Proof.
    intros. contract_induction; try easy.
    -   (* Deployment *)
        intros.
        unfold multisig_init in init_some.
        now inversion init_some.
    -   (* Call *)
        intros.
        destruct msg; try easy.
        destruct m.
        --  destruct admin_action.
            --- (* ChangeQuorum *)
                cbn in *.
                destruct (fail_if_amount ctx); try easy.
                destruct (fail_if_not_admin ctx prev_state); try easy.
                unfold check_new_quorum in receive_some.
                destruct params.
                destruct (N.of_nat (Datatypes.length (FMap.elements g)) <? n) eqn:E; try easy.
                apply N.ltb_ge in E.
                destruct (N.of_nat
                (Datatypes.length
                   (FMap.elements
                      (fin_maps.map_fold
                         (fun (_ : SignerId) (elem : N) (acc : FMap N unit) => FMap.add elem tt acc)
                         FMap.empty g))) =? N.of_nat (Datatypes.length (FMap.elements g))); try easy.
                now inversion receive_some.
            --- (* ChangeThreshold *)
                cbn in *.
                destruct (fail_if_amount ctx); try easy.
                destruct (fail_if_not_admin ctx prev_state); try easy.
                destruct (N.of_nat (Datatypes.length (FMap.elements (signers prev_state))) <? n) eqn:E; try easy.
                destruct (n <? 1); try easy.
                cbn in *.
                apply N.ltb_ge in E.
                now inversion receive_some.
            --- (* SetAdmin *) 
                simpl in receive_some.
                apply set_admin_preserves_threshold_signers in receive_some.
                inversion receive_some.
                rewrite <- H0.
                now rewrite <- H1.
            --- (* ConfirmAdmin *)
                simpl in receive_some.
                apply confirm_admin_preserves_threshold_signers in receive_some.
                inversion receive_some.
                rewrite <- H0.
                now rewrite <- H1.
        --  (* Minter *)
            simpl in receive_some.
            apply apply_minter_preserves_state in receive_some.
            now rewrite <- receive_some.
        -- (* Fees *)
            simpl in receive_some.
            apply fees_preserves_state in receive_some.
            now rewrite <- receive_some.
        -- (* Set_signer_payment_address *)
            simpl in receive_some.
            apply set_signer_payment_address_preserves_threshold_signers in receive_some.
            inversion receive_some.
            rewrite <- H0.
            now rewrite <- H1.
    -   (* Recursive call *)
        intros.
        destruct msg; try easy.
        destruct m.
        --  destruct admin_action.
            --- (* ChangeQuorum *)
                cbn in *.
                destruct (fail_if_amount ctx); try easy.
                destruct (fail_if_not_admin ctx prev_state); try easy.
                unfold check_new_quorum in receive_some.
                destruct params.
                destruct (N.of_nat (Datatypes.length (FMap.elements g)) <? n) eqn:E; try easy.
                apply N.ltb_ge in E.
                destruct (N.of_nat
                (Datatypes.length
                (FMap.elements
                    (fin_maps.map_fold
                        (fun (_ : SignerId) (elem : N) (acc : FMap N unit) => FMap.add elem tt acc)
                        FMap.empty g))) =? N.of_nat (Datatypes.length (FMap.elements g))); try easy.
                now inversion receive_some.
            --- (* ChangeThreshold *)
                cbn in *.
                destruct (fail_if_amount ctx); try easy.
                destruct (fail_if_not_admin ctx prev_state); try easy.
                destruct (N.of_nat (Datatypes.length (FMap.elements (signers prev_state))) <? n) eqn:E; try easy.
                destruct (n <? 1); try easy.
                cbn in *.
                apply N.ltb_ge in E.
                now inversion receive_some.
            --- (* SetAdmin *) 
                simpl in receive_some.
                apply set_admin_preserves_threshold_signers in receive_some.
                inversion receive_some.
                rewrite <- H0.
                now rewrite <- H1.
            --- (* ConfirmAdmin *)
                simpl in receive_some.
                apply confirm_admin_preserves_threshold_signers in receive_some.
                inversion receive_some.
                rewrite <- H0.
                now rewrite <- H1.
        --  (* Minter *)
            simpl in receive_some.
            apply apply_minter_preserves_state in receive_some.
            now rewrite <- receive_some.
        -- (* Fees *)
            simpl in receive_some.
            apply fees_preserves_state in receive_some.
            now rewrite <- receive_some.
        -- (* Set_signer_payment_address *)
            simpl in receive_some.
            apply set_signer_payment_address_preserves_threshold_signers in receive_some.
            inversion receive_some.
            rewrite <- H0.
            now rewrite <- H1.
    -   (* Facts *)
        instantiate (AddBlockFacts := fun _ _ _ _ _ _ => True).
        instantiate (DeployFacts := fun _ _ => True).
        instantiate (CallFacts := fun _ _ _ _ => True).
        unset_all; subst;cbn in *.
        destruct step; try easy.
        destruct a; try easy.
Qed.
End SafetyProofs.

(** * Functional correctness *)
Section AdminProofs.
Context {BaseTypes : ChainBase}.

(** ** Change quorum functional correct *)
Lemma change_quorum_functionally_correct {chain ctx prev_state t new_signers next_state} :
    multisig_receive chain ctx prev_state (Some (Admin (ChangeQuorum  (t, new_signers)))) = Some (next_state, []) ->
    ( t <= N.of_nat (length (FMap.elements new_signers)) /\
      next_state.(threshold) = t /\
      next_state.(signers) = new_signers
    ).
Proof.
    intros. contract_simpl multisig_receive multisig_init. split. 
    - rewrite <- N.ltb_ge. easy.
    - split; easy.  
Qed.

(** ** Change threshold functional correct *)
Lemma change_threshold_functionally_correct {chain ctx prev_state t next_state} :
    multisig_receive chain ctx prev_state (Some (Admin (ChangeThreshold  t))) = Some (next_state, []) ->
    next_state.(threshold) = t.
Proof.
    intros. contract_simpl multisig_receive multisig_init. easy.  
Qed.

(** ** Set admin functional correct *)
Lemma set_admin_functionally_correct {chain ctx prev_state a next_state} :
    multisig_receive chain ctx prev_state (Some (Admin (SetAdmin  a))) = Some (next_state, []) ->
    next_state.(pending_admin) = Some a.
Proof.
    intros. contract_simpl multisig_receive multisig_init. easy.   
Qed.

(** ** Confirm admin functional correct *)
Lemma confirm_admin_correct {ctx chain prev_state next_state} :
    multisig_receive chain ctx prev_state (Some (Admin ConfirmAdmin)) = Some (next_state, []) ->
    next_state.(pending_admin) = None /\ 
    next_state.(admin) = ctx.(ctx_from) /\
    prev_state.(pending_admin) = Some (next_state.(admin)).
Proof.
    intros. contract_simpl multisig_receive multisig_init. 
    split; try easy; split; auto. 
    destruct (address_eqb_spec a (ctx_from ctx)) in H2; try easy.
    now f_equal.
Qed.

End AdminProofs.

Section MinterProofs.
Open Scope N_scope.
Context {BaseTypes : ChainBase}.

(** ** Apply minter functional correct *)
Lemma apply_minter_functionally_correct {chain ctx prev_state next_state signer_action acts} :
    multisig_receive chain ctx prev_state (Some (Minter signer_action)) =
    Some (next_state, acts) ->
    (* Creating correct contract call *)
    let action := signer_action.(action) in
    acts = [act_call action.(target) ctx.(ctx_amount) (serialize action.(entrypoint))].
Proof.
    intros. contract_simpl multisig_receive multisig_init. easy.
Qed.

End MinterProofs.

Section FeesProofs.
Context {BaseTypes : ChainBase}.

(** ** Fees endpoint functional correct *)
(* State should not be changed and calls should be made to contracts *)
Lemma fees_functionally_correct {chain ctx prev_state next_state acts entrypoint} :
    multisig_receive chain ctx prev_state (Some (Fees entrypoint)) = Some (next_state, acts) ->
    match entrypoint with
    | Distribute_tokens_with_quorum param => 
        (* Call should be to minter contract and 0 amount *)
        let msg := serialize (Distribute_tokens {|dp_signers := signers_key_hash prev_state; dp_tokens := param.(dtp_tokens)|}) in
        acts = [(act_call param.(dtp_minter_contract) 0 msg)]
    | Distribute_xtz_with_quorum addr => 
        (* Call should be to correct target and 0 amount *)
        let msg := serialize (Distribute_xtz (signers_key_hash prev_state)) in
        acts = [(act_call addr 0 msg)]
    end.
Proof.
    (* We assume that the messages of the calls are correct by inspecting the code *)
    intros. contract_simpl multisig_receive multisig_init. 
    unfold fees_main in H. 
    destruct entrypoint; try easy.
Qed.  

End FeesProofs.

Section SetSignerPaymentAddressProofs.
Context {BaseTypes : ChainBase}.
Open Scope nat.

(** ** Set signer payment address functional correct *)
Lemma set_signer_payment_address_functionally_correct {chain ctx prev_state next_state param acts n new_n k} :
    multisig_receive chain ctx prev_state (Some (Set_signer_payment_address param)) = Some (next_state, acts) ->
    (
        (* Counter is increased by 1 *)
        (
            FMap.find param.(pap_signer_id) prev_state.(counters) = Some n ->
            FMap.find param.(pap_signer_id) next_state.(counters) = Some new_n ->
            new_n = n + 1
        )
        
    /\
        (* Correct call to minter is made *)
        (
            FMap.find param.(pap_signer_id) prev_state.(signers) = Some k ->
            let call := serialize (SignerOps_Interface.set_payment_address {| sparam_signer := Crypto.hash_key k; payment_address := ctx.(ctx_from) |}) in
            acts = [act_call param.(pap_minter_contract) 0 call]
        )
    ).
Proof.
    intros. contract_simpl multisig_receive multisig_init. cbn in *. split.
    - intros. rewrite H in H2. rewrite FMap.find_add in H2. easy.
    - easy. 
Qed.
    
End SetSignerPaymentAddressProofs.