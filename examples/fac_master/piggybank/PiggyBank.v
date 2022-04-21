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
      match st with
      | {| piggyState := Intact |} => Some ((insert ctx.(ctx_amount) st), [])
      | _ => None 
      end
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

  (** The counter contract *)
  Definition piggyBank_contract : Contract Amount Msg State :=
    build_contract piggyBank_init piggyBank_receive.

End PiggyBank.

Section FunctionalProperties.

  Context {BaseTypes : ChainBase}.

  Lemma piggybank_correct {prev_state next_state acts msg ctx} :
  prev_state.(piggyState) = Intact -> piggyBank prev_state msg ctx = Some (next_state, acts) ->
  match msg with
  | Insert => prev_state.(balance) + ctx.(ctx_amount) = next_state.(balance)
  | Smash => prev_state.(owner) = ctx.(ctx_from) -> next_state.(piggyState) = Smashed /\ 
    next_state.(balance) = 0 /\ acts = [act_transfer prev_state.(owner) prev_state.(balance)]
  end.
  Proof.
  intros H1 H2.
  destruct msg.
  - destruct prev_state. cbn in *. rewrite H1 in H2. unfold insert in *.
    cbn in H2. inversion H2. cbn. reflexivity.
  - intros H3. destruct prev_state. cbn in *. rewrite H1 in H2. rewrite H3 in H2. 
    destruct (address_eqb_spec (ctx_from ctx) (ctx_from ctx)) in H2.
    + inversion H2. cbn. rewrite H3. auto.
    + discriminate.
  Qed.

End FunctionalProperties.

Section SafetyProperties.

  Context {BaseTypes : ChainBase}.

  Lemma owner_never_changes {prev_state next_state msg ctx acts}:
    piggyBank prev_state msg ctx = Some (next_state, acts) -> prev_state.(owner) = next_state.(owner).
  Proof.
    intros H; destruct msg; cbn in *;destruct prev_state; cbn in *; destruct piggyState0; inversion H.
    - auto.
    - destruct (address_eqb_spec (ctx_from ctx) owner0) in H1; inversion H1; auto.
  Qed.

  Lemma cant_change_smashed {prev_state msg ctx}:
    prev_state.(piggyState) = Smashed -> piggyBank prev_state msg ctx = None.
  Proof.
    intros H. destruct msg, prev_state; cbn in *; rewrite H; auto.
  Qed.

End SafetyProperties.