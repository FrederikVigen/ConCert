Require Import Extras.
Require Import Automation.
Require Import Serializable.
Require Import Blockchain.

From Coq Require Import Morphisms ZArith Basics.
From Coq Require Import List.

Import ListNotations.
Open Scope Z.

Section PiggyBank.

  (** Enabling recursors for records allows for deriving [Serializable] instances. *)
  Set Nonrecursive Elimination Schemes.

  (** The definitions in this section are generalized over the [ChainBase] that specifies the type of addresses and which properties such a type must have *)
  Context {BaseTypes : ChainBase}.

  Inductive PiggyState := Intact | Smashed.

  Inductive Msg :=
  | Insert
  | Smash.

  Record State :=
      build_state { balance : Amount ;
                  owner : Address ; 
                  piggyState : PiggyState}.

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
          
    (** The "entry point" of the contract. Dispatches on a message and calls [counter]. *)
  Definition piggyBank_receive (chain : Chain) (ctx : ContractCallContext)
             (state : State) (msg : option Msg) : option (State * list ActionBody)
    := match msg with
       | Some m => piggyBank state m ctx
       | None => None
       end.

  (** We initialize the contract state with [init_value] and set [owner] to the address from which the contract was deployed *)
  Definition piggyBank_init (chain : Chain) (ctx : ContractCallContext) (init_value : Amount) : option State :=
  Some {| balance := init_value ;
          owner := ctx.(ctx_from);
          piggyState := Intact |}.

  (** Deriving the [Serializable] instances for the state and for the messages *)
  Global Instance PiggyState_serializable : Serializable PiggyState :=
  Derive Serializable PiggyState_rect<Intact, Smashed>.
  
  Global Instance State_serializable : Serializable State :=
    Derive Serializable State_rect<build_state>.

  Global Instance Msg_serializable : Serializable Msg :=
    Derive Serializable Msg_rect<Insert, Smash>.

  (** The piggybank contract *)
  Definition piggyBank_contract : Contract Amount Msg State :=
    build_contract piggyBank_init piggyBank_receive.

End PiggyBank.

Section FunctionalProperties.

  Context {BaseTypes : ChainBase}.
  
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
    intros H1 H2. unfold piggyBank_receive in H2. destruct msg. unfold piggyBank in H2.
    destruct m.
    - destruct prev_state. cbn in *. rewrite H1 in H2. unfold insert in *.
      cbn in H2. destruct (0 <? ctx_amount ctx); try discriminate. inversion H2. cbn. reflexivity.
    - intros H3. destruct prev_state. cbn in *. rewrite H1 in H2. rewrite H3 in H2. 
      destruct (address_eqb_spec (ctx_from ctx) (ctx_from ctx)) in H2.
      + inversion H2. cbn. rewrite H3. auto.
      + discriminate.
    - discriminate.
  Qed.

End FunctionalProperties.

Section SafetyProperties.

  Context {BaseTypes : ChainBase}.

  Lemma owner_never_changes {prev_state next_state msg chain ctx acts}:
  piggyBank_receive chain ctx prev_state msg = Some (next_state, acts) -> prev_state.(owner) = next_state.(owner).
  Proof.
    intros H. unfold piggyBank_receive in H. destruct msg. unfold piggyBank in H.
    destruct m; cbn in *;destruct prev_state; cbn in *; destruct piggyState0; destruct (0 <? ctx_amount ctx); try easy.
    inversion H. cbn in *. reflexivity.
    - destruct (address_eqb_spec (ctx_from ctx) owner0) in H; inversion H; auto.
    - destruct (address_eqb_spec (ctx_from ctx) owner0) in H; inversion H; auto.
    - discriminate.  
  Qed.

  Lemma cant_change_smashed {prev_state msg chain ctx}:
    prev_state.(piggyState) = Smashed -> piggyBank_receive chain ctx prev_state msg = None.
  Proof.
    intros H. unfold piggyBank_receive. destruct msg, prev_state; try auto. cbn in *. unfold piggyBank. rewrite H. destruct (0 <? ctx_amount ctx); destruct m; auto. 
  Qed.

  Lemma if_intact_balance_only_increasing {prev_state next_state chain ctx new_acts}:
    prev_state.(piggyState) = Intact ->
    piggyBank_receive chain ctx prev_state (Some Insert) = Some (next_state, new_acts) ->
    prev_state.(balance) < next_state.(balance).
  Proof.
    intros H H1. destruct prev_state. cbn in *. rewrite H in H1. destruct (0 <? ctx_amount ctx) eqn:E; try easy.
    inversion H1. cbn in *. apply Z.ltb_lt in E; omega.
  Qed. 
    
End SafetyProperties.