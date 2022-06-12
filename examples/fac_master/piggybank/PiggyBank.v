(** * Piggy Bank Contract *)
(** Implementation of a piggy bank. The contract is based on the Concordium example.

https://developer.concordium.software/en/mainnet/smart-contracts/tutorials/piggy-bank/writing.html#piggy-bank-writing
*)
Require Import Extras.
Require Import Automation.
Require Import Serializable.
Require Import Blockchain.
From ConCert.Execution Require Import ContractCommon.
From Coq Require Import Morphisms ZArith Basics.
From Coq Require Import List.

(** * Types *)

Import ListNotations.
Open Scope Z.

Section PiggyBank.

Set Nonrecursive Elimination Schemes.

Context {BaseTypes : ChainBase}.

Inductive PiggyState := Intact | Smashed.

Inductive Msg :=
| Insert
| Smash.

(** * Types *)
Record State :=
    build_state { balance : Amount ;
                owner : Address ; 
                piggyState : PiggyState}.

Definition Setup : Type := unit.

(** * Implementation *)
Definition insert (n : Amount) (st : State) : State :=
    {| balance := st.(balance) + n ;
        owner := st.(owner);
        piggyState := st.(piggyState) |}.

Definition smash (st : State) : State :=
    {| balance := 0 ;
        owner := st.(owner);
        piggyState := Smashed |}.

Definition piggyBank (st : State) (msg : Msg) (ctx : ContractCallContext) : option (State * list ActionBody) :=
  match msg with
  | Insert =>
    if 0 <? ctx.(ctx_amount)
    then
      match st with
      | {| piggyState := Intact |} => Some ((insert ctx.(ctx_amount) st), [])
      | _ => None 
      end
    else None
  | Smash =>
    match st with
    | {| balance := b; owner := o; piggyState := Intact |} => 
      if address_eqb ctx.(ctx_from) o then (Some ((smash st), [act_transfer o b])) else None
    | _ => None
    end
  end.
          
Definition piggyBank_receive (chain : Chain) (ctx : ContractCallContext)
            (state : State) (msg : option Msg) : option (State * list ActionBody)
  := match msg with
      | Some m => piggyBank state m ctx
      | None => None
      end.

(** We initialize the contract state with [init_value] and set [owner] to the address from which the contract was deployed *)
Definition piggyBank_init (chain : Chain) (ctx : ContractCallContext) (_ : Setup) : option State :=
Some {| balance := 0 ;
        owner := ctx.(ctx_from);
        piggyState := Intact |}.

(* begin hide *)
(** Deriving the [Serializable] instances for the state and for the messages *)
Global Instance PiggyState_serializable : Serializable PiggyState :=
Derive Serializable PiggyState_rect<Intact, Smashed>.

Global Instance State_serializable : Serializable State :=
Derive Serializable State_rect<build_state>.

Global Instance Msg_serializable : Serializable Msg :=
Derive Serializable Msg_rect<Insert, Smash>.
(* end hide *)

(** The piggybank contract *)
Definition piggyBank_contract : Contract Setup Msg State :=
  build_contract piggyBank_init piggyBank_receive.

End PiggyBank.

(** * Proofs *)
Section FunctionalProperties.

Context {BaseTypes : ChainBase}.
  
(** * Functional correctness *)
Lemma piggybank_correct {prev_state next_state acts msg chain ctx} :
  prev_state.(piggyState) = Intact -> piggyBank_receive chain ctx prev_state msg = Some (next_state, acts) ->
  match msg with
    | Some m => 
      match m with
      | Insert => prev_state.(balance) + ctx.(ctx_amount) = next_state.(balance)
      | Smash => prev_state.(owner) = ctx.(ctx_from) -> next_state.(piggyState) = Smashed /\ 
        next_state.(balance) = 0 /\ acts = [act_transfer prev_state.(owner) prev_state.(balance)]
      end
    | None => False
  end.
Proof.
  intros H1 H2. 
  unfold piggyBank_receive in H2. 
  destruct msg; 
  unfold piggyBank in H2.
  destruct m.
  - destruct prev_state. cbn in *. rewrite H1 in H2. unfold insert in *.
    cbn in H2. destruct (0 <? ctx_amount ctx); try discriminate. inversion H2. cbn. reflexivity.
  - intros H3. destruct prev_state. cbn in *. rewrite H1 in H2. rewrite H3 in H2. 
    destruct_address_eq.
    + inversion H2. cbn. rewrite H3. auto.
    + discriminate.
  - discriminate.
Qed.

End FunctionalProperties.

(** * Safety properties *)
Section SafetyProperties.

Context {BaseTypes : ChainBase}.

(** ** Owner never changes *)
Lemma owner_never_changes {prev_state next_state msg chain ctx acts}:
piggyBank_receive chain ctx prev_state msg = Some (next_state, acts) -> prev_state.(owner) = next_state.(owner).
Proof.
  intros H. 
  unfold piggyBank_receive in H. 
  destruct msg; unfold piggyBank in H.
  destruct m; cbn in *; 
  destruct prev_state; cbn in *; 
  destruct piggyState0; 
  destruct (0 <? ctx_amount ctx); try easy.
  inversion H. cbn in *. reflexivity.
  - destruct_address_eq; inversion H; auto.
  - destruct_address_eq; inversion H; auto.
  - discriminate.  
Qed.

(** ** Can't change smashed *)
Lemma cant_change_smashed {prev_state msg chain ctx}:
  prev_state.(piggyState) = Smashed -> piggyBank_receive chain ctx prev_state msg = None.
Proof.
  intros H. 
  unfold piggyBank_receive. 
  destruct msg, prev_state; try auto. 
  cbn in *. unfold piggyBank. 
  rewrite H. 
  destruct (0 <? ctx_amount ctx); 
  now destruct m.
Qed.

(** ** If piggy bank is intact, balance is only increasing *)
Lemma if_intact_balance_only_increasing {prev_state next_state chain ctx new_acts}:
  prev_state.(piggyState) = Intact ->
  piggyBank_receive chain ctx prev_state (Some Insert) = Some (next_state, new_acts) ->
  prev_state.(balance) < next_state.(balance).
Proof.
  intros H H1. 
  destruct prev_state. 
  cbn in *. 
  rewrite H in H1. 
  destruct (0 <? ctx_amount ctx) eqn:E; try easy.
  inversion H1. 
  cbn in *. 
  apply Z.ltb_lt in E; omega.
Qed. 

(** ** Init total supply correct *)
Lemma init_total_supply_correct : forall chain ctx setup state,
  piggyBank_init chain ctx setup = Some state ->
    state.(balance) = 0.
Proof.
  intros; unfold piggyBank_init in H; 
  now inversion H.
Qed.

(** ** Balance always positive *)
Lemma balance_always_positive : forall bstate caddr,
  reachable bstate ->
  env_contracts bstate caddr = Some (piggyBank_contract : WeakContract) ->
  exists cstate,
    contract_state bstate caddr = Some cstate
    /\ 0 <= cstate.(balance).
Proof.
  intros * reach deployed.
  apply (lift_contract_state_prop piggyBank_contract); try easy.
  - cbn. 
    intros. 
    apply init_total_supply_correct in H. 
    omega.
  - cbn. intros. 
    unfold piggyBank_receive in H0. 
    destruct msg; try easy.
    unfold piggyBank in H0. 
    destruct m. 
    + contract_simpl piggyBank_receive piggyBank_init. 
      destruct cstate, piggyState0; try easy. 
      inversion H0. cbn in *. apply Z.ltb_lt in H1. 
      omega.
    + destruct cstate, piggyState0; try easy. 
      destruct_address_eq; try easy.
      now inversion H0.
Qed.

(** ** Owner never changes 2 *)
Lemma owner_never_changes2 : forall bstate caddr (trace : ChainTrace empty_state bstate),
  reachable bstate ->
  env_contracts bstate caddr = Some (piggyBank_contract : WeakContract) ->
  exists cstate depinfo,
    contract_state bstate caddr = Some cstate /\
    deployment_info Setup trace caddr = Some depinfo /\
    depinfo.(deployment_from) = cstate.(owner).
Proof.
  contract_induction;
    intros; auto.
    - cbn in *. unfold piggyBank_init in init_some. inversion init_some. easy.
    - cbn in *. unfold piggyBank_receive in receive_some. destruct msg; try easy.
      unfold piggyBank in receive_some. destruct m; try easy. destruct (0 <? ctx_amount ctx); try easy.
      + rewrite IH. destruct prev_state. cbn in *. destruct piggyState0; try easy. inversion receive_some. easy.
      + rewrite IH. destruct prev_state. cbn in *. destruct piggyState0; try easy. destruct_address_eq; try easy.
      inversion receive_some. easy.
    - rewrite IH. cbn in *. unfold piggyBank_receive in receive_some. destruct msg; try easy.
      unfold piggyBank in receive_some. destruct m.
      + destruct (0 <? ctx_amount ctx); try easy. destruct prev_state. destruct piggyState0; try easy. inversion receive_some. easy.
      + destruct prev_state. destruct piggyState0; try easy. destruct_address_eq; try easy. inversion receive_some. easy.
    - instantiate (AddBlockFacts := fun _ _ _ _ _ _ => True).
      instantiate (DeployFacts := fun _ _ => True).
      instantiate (CallFacts := fun _ _ _ _ => True).
      unset_all; subst;cbn in *.
      destruct_chain_step; auto.
      destruct_action_eval; auto.
Qed.
End SafetyProperties.