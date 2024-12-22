Require Import Monads.
Require Import Blockchain.
Require Import Containers.
Require Import Serializable.
Require Import PArith.
Require Import Extras.
Require Import BoundedN.
Require Import BuildUtils.
Require Import FMapList.
Require Import RecordUpdate.
Require Import Automation.
Require Import ContractCommon.
Require Import ResultMonad.
Require Import InterContractCommunication.
Require Import ChainedList.
Require Import Strat.
From Coq Require Import List.
From Coq Require Import Bool.
From Coq Require Import ZArith.
From Coq Require Import Arith.
From Coq Require Import String.
Import ListNotations.
Require Import Lia.
Import RecordSetNotations.
From Coq Require Import Permutation.
Require Import Coq.Program.Basics.
Require Import Coq.NArith.BinNatDef.

Section PaymentChannel.

  Context {BaseTypes : ChainBase}.
  Set Primitive Projections.
  Set Nonrecursive Elimination Schemes.
  Context {AddrSize : N}.

  (* Define a bytes type as a list of natural numbers (each representing a byte) *)
  Definition bytes := list N.

  (* Define the possible states of the payment channel *)
  Inductive PaymentChannelState :=
  | Open
  | Closed
  | Expired.

  (* Payment Channel state *)
  Record State := build_state {
    sender : Address;              (* Alice *)
    receiver : Address;            (* Bob *)
    balance : Amount;              (* Total funds in the channel *)
    authorized_amount : Amount;    (* Amount authorized by Alice *)
    channel_state : PaymentChannelState; (* Current state of the channel *)
    expiry : nat;                  (* Block number when the channel expires *)
  }.

  (* Setup for the contract *)
  Record Setup := build_setup {
    receiver_addr : Address;    (* Bob's address *)
    duration : nat;       (* Number of blocks after which the channel expires *)
  }.

  Global Instance state_settable : Settable _ :=
    settable! build_state <sender; receiver; balance; authorized_amount; channel_state; expiry>.

  (* Define messages for the payment channel, including the signature where needed *)
  Inductive Msg :=
  | SenderAuthAmount (amount : Amount) (sig : bytes)  (* Alice authorizes a payment *)
  | ReceiverWithdraw (amount : Amount) (sig : bytes)    (* Bob collects the authorized payment *)
  | CloseChannel.                                     (* Alice cancels the channel after expiration *)

  (* Define PaymentChannelState comparison function *)
  Definition eqb_PaymentChannelState (s1 s2 : PaymentChannelState) : bool :=
    match s1, s2 with
    | Open, Open => true
    | Closed, Closed => true
    | Expired, Expired => true
    | _, _ => false
    end.

  Section Serialization.

    (* Serializable instances for relevant types *)
    Global Instance Msg_serializable : Serializable Msg :=
      Derive Serializable Msg_rect<SenderAuthAmount, ReceiverWithdraw, CloseChannel>.

    Global Instance Setup_serializable : Serializable Setup :=
      Derive Serializable Setup_rect<build_setup>.

    Global Instance PaymentChannelState_serializable : Serializable PaymentChannelState :=
      Derive Serializable PaymentChannelState_rect<Open, Closed, Expired>.

    Global Instance State_serializable : Serializable State :=
      Derive Serializable State_rect<build_state>.

  End Serialization.

  (* Serialization helper functions *)
  Definition serializeMsg msg := (@serialize Msg _) msg.
  Definition serializeState state := (@serialize State _) state.
  Definition serializeSetup setup := (@serialize Setup _) setup.

  (* Coercions for automatic serialization *)
  Global Coercion serializeMsg : Msg >-> SerializedValue.
  Global Coercion serializeState : State >-> SerializedValue.
  Global Coercion serializeSetup : Setup >-> SerializedValue.

  (* Define an Error type *)
  Definition Error : Type := nat.
  Definition default_error: Error := 1%nat.

  Local Open Scope Z.

  (* Abstract signature verification function *)
  Parameter verify_signature : Address -> SerializedValue -> bytes -> bool.

  (* Check if the address is not a contract *)
  Definition address_not_contract `{ChainBase} (x : Address) : bool :=
    negb (address_is_contract x).

  (* Initialize the payment channel *)
  Definition init (chain : Chain) (ctx : ContractCallContext) (setup : Setup) : result State Error :=
    if (address_is_contract ctx.(ctx_from)
        || address_is_contract setup.(receiver_addr)
        || (ctx.(ctx_amount) <? 1)%Z
        || (setup.(duration) - chain.(current_slot) =? 7)%nat) (* Example constraints *)
    then Err default_error
    else Ok (build_state
               ctx.(ctx_from)            (* sender *)
               setup.(receiver_addr)     (* receiver *)
               ctx.(ctx_amount)          (* balance *)
               0%Z                       (* authorized_amount *)
               Open                      (* channel_state *)
               (setup.(duration)) (* expiry *)
            ).

  (* Authorize a payment by Alice *)
  Definition authorize_payment (ctx : ContractCallContext) (state : State) (amount : Amount) (sig : bytes) : result (State * list ActionBody) Error :=
    if (ctx.(ctx_from) =? state.(sender))%address
       && (eqb_PaymentChannelState state.(channel_state) Open)
       && (verify_signature state.(sender) (serialize amount) sig)
    then
      if (amount <=? state.(balance))%Z
      then
        let new_state := state <| authorized_amount := amount |>
                              <| balance := state.(balance)|>
                              in Ok (new_state, [])
      else Err default_error
    else Err default_error.

  (* Collect the authorized payment by Bob *)
  Definition collect_payment (ctx : ContractCallContext) (state : State) (amount : Amount) (sig : bytes) : result (State * list ActionBody) Error :=
    if (ctx.(ctx_from) =? state.(receiver))%address
       && (eqb_PaymentChannelState state.(channel_state) Open)
       && (amount =? state.(authorized_amount))%Z
       && (verify_signature state.(sender) (serialize amount) sig)
    then
      let new_state := state <| authorized_amount := state.(authorized_amount) - amount |>
                             <| balance := 0 |>
                             <| channel_state := Closed |>
                             in
      let actions := [act_transfer state.(receiver) amount;
                      act_transfer state.(sender) (state.(balance) - amount)] in
      Ok (new_state, actions)
    else Err default_error.

  (* Cancel the channel after expiration by Alice *)
  Definition cancel_channel (chain : Chain) (ctx : ContractCallContext) (state : State) : result (State * list ActionBody) Error :=
    if (ctx.(ctx_from) =? state.(sender))%address
       && (state.(expiry) <=? chain.(current_slot))%nat
    then
      let new_state := state <| channel_state := Expired |>
                            <| balance := 0 |>
                            in
      let actions := [act_transfer state.(sender) state.(balance)] in
      Ok (new_state, actions)
    else Err default_error.

  (* Contract receive function *)
  Definition receive (chain : Chain) (ctx : ContractCallContext) (state : State) (msg : option Msg) : result (State * list ActionBody) Error :=
    if (negb (address_is_contract ctx.(ctx_from)) && (ctx.(ctx_amount) =? 0)) then
      match msg with
      | Some (SenderAuthAmount amount sig) => authorize_payment ctx state amount sig
      | Some (ReceiverWithdraw amount sig) => collect_payment ctx state amount sig
      | Some CloseChannel => cancel_channel chain ctx state
      | None => Err default_error
      end
    else Err default_error.

  (* Define the contract *)
  Definition contract : Contract Setup Msg State Error :=
    build_contract init receive.

  (* Check if a message is a valid payment channel message *)
  Definition is_payment_channel_msg (msg : SerializedValue) : bool :=
    match @deserialize Msg _ msg with
    | Some (SenderAuthAmount _ _) => true
    | Some (ReceiverWithdraw _ _) => true
    | Some CloseChannel => true
    | _ => false
    end.

  (* Validate Payment Channel action messages *)
  Definition validate_payment_channel_action_msg (act : Action) : bool :=
    match act.(act_body) with
    | act_call _ _ msg => is_payment_channel_msg msg
    | _ => false
    end.

Definition get_contract_state (bstate : ChainState) (contract_addr : Address) : option State :=
    match env_contract_states bstate contract_addr with
    | Some serialized_state =>
      deserialize serialized_state
    | None => None
    end.

Parameter generate_signature : Address -> bytes.

Parameter sign_message : bytes -> bytes -> bytes.

Variable caddr : Address.

Variable s0 : ChainState.

Hypothesis H_init: is_init_bstate contract caddr s0.

Variable miner_address : Address.

Hypothesis H_miner : address_not_contract miner_address = true.

Variable init_cstate : State.

Hypothesis H_state : get_contract_state s0 caddr = Some init_cstate.

Definition alice_address := init_cstate.(alice).
Parameter bob_address : Address.
Parameter alice_private_key : bytes.


  
Definition is_alice_sender (state : State) (uaddr : Address) : bool :=
  (state.(sender) =? uaddr)%address.

Definition alice_cancel state caddr :Action :=
  build_call state.(sender) caddr 0 CloseChannel.

Definition bob_collect state caddr :Action :=
  build_call state.(receiver) caddr 0 (ReceiverWithdraw state.(balance) alice_private_key).

Definition alice_auth state caddr :Action :=
  build_call state.(sender) caddr 0 (SenderAuthAmount state.(balance) alice_private_key).

Variable contract_addr : Address.

Variable DP_init_state : ChainState.

Variable miner_address : Address.

Hypothesis miner_always_eoa : address_is_contract miner_address = false.

Global Definition depth_first := true.

Global Definition miner_reward := 10%Z.

Hypothesis init_s : is_init_bstate contract contract_addr DP_init_state.

Notation "trace( from , to )" := (TransitionTrace miner_address from to)(at level 10).


Definition usr_strategy : strat miner_address :=
  fun s0 s tr =>
    let time := current_slot s in
    match get_payment_channel_state s contract_addr with
    | Some state =>
        match channel_state state with
        | Open =>
            if (Nat.leb (expiry state) time) then
                [alice_cancel state contract_addr]
            else
                [alice_auth state contract_addr]
        | Closed => []
        | Expired => []
        end
    | None => []
    end.

Definition env_strategy : strat miner_address :=
  fun s0 s tr =>
    let time := current_slot s in
    match get_payment_channel_state s contract_addr with
    | Some state =>
        match channel_state state with
        | Open =>
            if Nat.leb (expiry state) time then
                [bob_collect state contract_addr]
            else
                [bob_collect state contract_addr]
        | Closed => []
        | Expired => []
        end
    | None => []
    end.


End strats.



Section theories.
Context {BaseTypes : ChainBase}.
Set Primitive Projections.
Set Nonrecursive Elimination Schemes.


Ltac reduce_authorize_payment :=
  match goal with
  | H : authorize_payment ?ctx ?state ?amount ?sig = _ |- _ =>
      unfold authorize_payment in H;
      destruct ((ctx.(ctx_from) =? state.(sender))%address) eqn:EFrom in H; try discriminate;
      destruct (eqb_PaymentChannelState state.(channel_state) Open) eqn:EState in H; try discriminate;
      destruct (verify_signature state.(sender) (serialize amount) sig) eqn:ESig in H; try discriminate;
      destruct ((amount <=? state.(balance))%Z) eqn:EAmount in H; try discriminate
  end.

Ltac reduce_collect_payment :=
  match goal with
  | H : collect_payment ?ctx ?state ?amount ?sig = _ |- _ =>
      unfold collect_payment in H;
      destruct ((ctx.(ctx_from) =? state.(receiver))%address) eqn:EFrom in H; try discriminate;
      destruct (eqb_PaymentChannelState state.(channel_state) Open) eqn:EState in H; try discriminate;
      destruct ((amount =? state.(authorized_amount))%Z) eqn:EAmount in H; try discriminate;
      destruct (verify_signature state.(sender) (serialize amount) sig) eqn:ESig in H; try discriminate
  end.

Ltac reduce_cancel_channel :=
  match goal with
  | H : cancel_channel ?chain ?ctx ?state = _ |- _ =>
      unfold cancel_channel in H;
      destruct ((ctx.(ctx_from) =? state.(sender))%address) eqn:EFrom in H; try discriminate;
      destruct ((state.(expiry) <=? chain.(current_slot))%nat) eqn:EExpiry in H; try discriminate
  end.


Ltac reduce_payment_channel :=
  match goal with
  | H : authorize_payment _ _ _ _ = _ |- _ =>
      reduce_authorize_payment
  | H : collect_payment _ _ _ _ = _ |- _ =>
      reduce_collect_payment
  | H : cancel_channel _ _ _ = _ |- _ =>
      reduce_cancel_channel
  end.

Tactic Notation "contract_simpl" := contract_simpl @receive @init.

Ltac destruct_message :=
    repeat match goal with
    | H : Blockchain.receive _ _ _ _ _ = Ok _ |- _ => unfold Blockchain.receive in H; cbn in H
    | msg : option Msg |- _ => destruct msg
    | msg : Msg |- _ => destruct msg
    | H : Blockchain.receive _ _ _ _ None = Ok _ |- _ => now contract_simpl
    | H : receive _ _ _ None = Ok _ |- _ => now contract_simpl
    end.


Section correct.

Lemma init_constants_correct : forall state chain ctx setup,
  init chain ctx setup = Ok (state) ->
    state.(sender) =  ctx.(ctx_from) 
    /\ state.(receiver) = setup.(receiver_addr)
    /\ state.(expiry) = setup.(duration).
Proof.
  intros * init_some.
  now contract_simpl.
Qed.

Lemma contract_constants_receive :forall prev_state new_state chain ctx msg new_acts,
  receive chain ctx prev_state msg = Ok (new_state, new_acts) ->
    prev_state.(sender) = new_state.(sender)
    /\ prev_state.(receiver) = new_state.(receiver)
    /\ prev_state.(expiry) = new_state.(expiry).
Proof.
  intros * receive_some.
  unfold receive in receive_some.
  destruct_match in receive_some;destruct_message;try congruence.
  - reduce_authorize_payment;simpl in *;inversion receive_some;simpl;eauto.
  - reduce_collect_payment;simpl in *;inversion receive_some;simpl;eauto.
  - reduce_cancel_channel ;simpl in *;inversion receive_some;simpl;eauto.
Qed.


Lemma constants_are_constant bstate caddr (trace : ChainTrace empty_state bstate) :
env_contracts bstate caddr = Some (contract : WeakContract) ->
exists deploy_info cstate,
  deployment_info _ trace caddr = Some deploy_info
  /\ contract_state bstate caddr = Some cstate
  /\ let setup := deploy_info.(deployment_setup) in
  cstate.(sender) =  deploy_info.(deployment_from)
    /\ cstate.(receiver) = setup.(receiver_addr)
    /\ cstate.(expiry) = setup.(duration).
Proof.
  apply (lift_dep_info_contract_state_prop contract);
    intros *; clear trace bstate caddr.
  - intros init_some.
    now apply init_constants_correct in init_some.
  - intros IH receive_some.
    eapply contract_constants_receive in receive_some.
    destruct_and_split;eauto.
    rewrite <- H2.
    rewrite <- H.
    eauto.
    rewrite <- H3.
    rewrite <- H0.
    eauto.
    rewrite <- H4.
    rewrite <- H1.
    eauto.
Qed.

Lemma alice_and_bob_is_EOA bstate caddr:
  reachable bstate ->
  env_contracts bstate caddr = Some (contract : WeakContract) ->
  exists cstate,
    contract_state bstate caddr = Some cstate
    /\ address_not_contract cstate.(sender) = true
    /\ address_not_contract cstate.(receiver) = true.
Proof.
  contract_induction;intros;cbn in *;eauto;try congruence;try lia.
  - unfold init in *.
    destruct (address_is_contract (ctx_from ctx)
                || address_is_contract (receiver_addr setup)
                || (ctx_amount ctx <? 1)%Z || (duration setup - current_slot chain =? 7)) 
                eqn : requirements_check;try congruence;eauto.
    inversion init_some.
    simpl.
    propify.
    destruct_and_split.
    unfold address_not_contract in *.
    rewrite H. eauto.
    unfold address_not_contract in *.
    rewrite H3. eauto.
  - apply contract_constants_receive in receive_some.
    destruct_and_split.
    rewrite <- H.
    eauto.
    rewrite <- H0.
    eauto.
  - apply contract_constants_receive in receive_some.
    destruct_and_split.
    rewrite <- H.
    eauto.
    rewrite <- H0.
    eauto.
  - solve_facts.
Qed.


Lemma alice_and_bob_is_EOA_forall bstate caddr cstate:
  reachable bstate ->
  env_contracts bstate caddr = Some (contract : WeakContract) ->
    contract_state bstate caddr = Some cstate ->
    address_not_contract cstate.(sender) = true
    /\ address_not_contract cstate.(receiver) = true.
Proof.
  intros.
  eapply alice_and_bob_is_EOA in H;eauto.
  destruct H;
  destruct_and_split;
  rewrite H in H1;
  inversion H1; subst;
  destruct_and_split.
  eauto.
Qed.

Lemma closed_or_expired_bal_eq_zero bstate caddr:
  reachable bstate ->
  env_contracts bstate caddr = Some (contract : WeakContract) ->
  exists cstate, 
  contract_state bstate caddr = Some cstate /\
  ((cstate.(channel_state) = Closed \/
   cstate.(channel_state) = Expired ) -> (cstate.(balance) = 0)%Z).
Proof.
  contract_induction;intros;cbn in *;eauto;try congruence;try lia.
  - unfold init in init_some.
    destruct_match in init_some;try congruence.
    inversion init_some. subst.
    simpl in *.
    destruct H;try congruence.
  - assert(receive chain ctx prev_state msg = Ok (new_state, new_acts)) by eauto.
    apply contract_constants_receive in H0.
    destruct_and_split.
    unfold receive in receive_some.
    destruct_match in receive_some;try congruence.
    destruct_message;try congruence.
    + reduce_authorize_payment. simpl in *.
      inversion receive_some;subst.
      simpl in *.
      unfold eqb_PaymentChannelState in EState.
      destruct (channel_state prev_state) eqn : H' ;try congruence;
      destruct_or_hyps; congruence.
    + reduce_collect_payment. simpl in *.
      inversion receive_some;subst.
      simpl in *.
      eauto.
    + reduce_cancel_channel. simpl in *.
      inversion receive_some;subst.
      simpl in *.
      eauto.
  - assert(receive chain ctx prev_state msg = Ok (new_state, new_acts)) by eauto.
    apply contract_constants_receive in H0.
    destruct_and_split.
    unfold receive in receive_some.
    destruct_match in receive_some;try congruence.
    destruct_message;try congruence.
    + reduce_authorize_payment. simpl in *.
      inversion receive_some;subst.
      simpl in *.
      unfold eqb_PaymentChannelState in EState.
      destruct (channel_state prev_state) eqn : H' ;try congruence;
      destruct_or_hyps; congruence.
    + reduce_collect_payment. simpl in *.
      inversion receive_some;subst.
      simpl in *.
      destruct ((authorized_amount prev_state - amount =? 0)%Z) eqn :amt;try congruence.
    + reduce_cancel_channel. simpl in *.
      inversion receive_some;subst.
      simpl in *.
      eauto.
  - solve_facts.
Qed.

Lemma closed_or_expired_bal_eq_zero_forall bstate caddr cstate:
  reachable bstate ->
  env_contracts bstate caddr = Some (contract : WeakContract) ->
  contract_state bstate caddr = Some cstate ->
  ((cstate.(channel_state) = Closed \/
   cstate.(channel_state) = Expired ) -> (cstate.(balance) = 0)%Z).
Proof.
  intros.
  eapply closed_or_expired_bal_eq_zero in H;eauto.
  destruct H;
  destruct_and_split;
  rewrite H in H1;
  inversion H1; subst;
  eauto.
Qed.


Lemma open_bal_not_eq_zero bstate caddr:
  reachable bstate ->
  env_contracts bstate caddr = Some (contract : WeakContract) ->
  exists cstate, 
  contract_state bstate caddr = Some cstate /\
  ((cstate.(channel_state) = Open ) -> (cstate.(balance) <> 0)%Z).
Proof.
  contract_induction;intros;cbn in *;eauto;try congruence;try lia.
  - unfold init in init_some.
    destruct (address_is_contract (ctx_from ctx)
    || address_is_contract (receiver_addr setup)
    || (ctx_amount ctx <? 1)%Z || (duration setup - current_slot chain =? 7)) eqn : requirements_check.
    propify.
    destruct_or_hyps;try lia;try congruence.
    inversion init_some. subst.
    simpl in *.
    propify.
    destruct_or_hyps;try lia;try congruence.
  - unfold receive in receive_some.
    destruct_match in receive_some;try congruence.
    destruct_message;try congruence.
    + reduce_authorize_payment. simpl in *.
      inversion receive_some;subst.
      simpl in *.
      apply IH in H.
      unfold eqb_PaymentChannelState in EState.
      destruct (channel_state prev_state) eqn : H' ;try congruence;
      destruct_or_hyps;try congruence.
    + reduce_collect_payment. simpl in *.
      inversion receive_some;subst.
      simpl in *.
      destruct ((authorized_amount prev_state - amount =? 0)%Z) eqn :amt;try congruence.
    + reduce_cancel_channel. simpl in *.
      inversion receive_some;subst.
      simpl in *.
      eauto.
  - unfold receive in receive_some.
    destruct_match in receive_some;try congruence.
    destruct_message;try congruence.
    + reduce_authorize_payment. simpl in *.
      inversion receive_some;subst.
      simpl in *.
      apply IH in H.
      unfold eqb_PaymentChannelState in EState.
      destruct (channel_state prev_state) eqn : H' ;try congruence;
      destruct_or_hyps;try congruence.
    + reduce_collect_payment. simpl in *.
      inversion receive_some;subst.
      simpl in *.
      destruct ((authorized_amount prev_state - amount =? 0)%Z) eqn :amt;try congruence.
    + reduce_cancel_channel. simpl in *.
      inversion receive_some;subst.
      simpl in *.
      eauto.
  - solve_facts.
Qed.

Lemma open_bal_not_eq_zero_forall bstate caddr cstate:
  reachable bstate ->
  env_contracts bstate caddr = Some (contract : WeakContract) -> 
  contract_state bstate caddr = Some cstate ->
  ((cstate.(channel_state) = Open ) -> (cstate.(balance) <> 0)%Z).
Proof.
  intros.
  eapply open_bal_not_eq_zero in H;eauto.
  destruct H;
  destruct_and_split;
  rewrite H in H1;
  inversion H1; subst;
  eauto.
Qed.



Lemma address_not_contract_negb:
  forall  caddr,
    address_not_contract caddr= true -> address_is_contract caddr = false.
Proof.
intros.
unfold address_not_contract  in H.
destruct ((address_is_contract caddr)) eqn : H'; try congruence.
simpl in H.
congruence.
Qed.

Lemma balance_on_chain' :
  forall bstate caddr,
    reachable bstate ->
    let effective_balance := (env_account_balances bstate caddr - (sumZ (fun act => act_body_amount act) (outgoing_acts bstate caddr)))%Z in
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    exists cstate,
      contract_state bstate caddr = Some cstate /\
      effective_balance = cstate.(balance).
Proof.
  intros.
  unfold effective_balance.
  contract_induction; intros; auto; cbn in *;try congruence;try lia;eauto.
  - unfold init in init_some.
    destruct (address_is_contract (ctx_from ctx)
    || address_is_contract (receiver_addr setup) || (ctx_amount ctx <? 1)%Z
    || (duration setup - current_slot chain =? 7)%nat) eqn:requirements_check;try congruence;eauto;
    propify;
    destruct_and_split.
    inversion init_some.
    simpl.
    lia.
  - unfold receive in receive_some.
    destruct (negb (address_is_contract (ctx_from ctx)) && (ctx_amount ctx =? 0)%Z) eqn : requirements_check;try congruence.
    propify.
    destruct_and_split.
    destruct_message;try congruence.
    + reduce_authorize_payment. cbn in *.
      inversion receive_some. simpl. lia.
    + reduce_collect_payment. cbn in *.
      inversion receive_some. simpl.
      destruct (authorized_amount prev_state - amount =? 0)%Z eqn:H';try congruence;try lia.
    + reduce_cancel_channel. cbn in *.
      inversion receive_some. simpl.
      lia.
  - unfold receive in receive_some.
    destruct (negb (address_is_contract (ctx_from ctx)) && (ctx_amount ctx =? 0)%Z) eqn : requirements_check;try congruence.
    propify.
    destruct_and_split.
    destruct_message;try congruence.
    + reduce_authorize_payment.
      inversion receive_some; destruct head; cbn in *; lia.
    + reduce_collect_payment.
      inversion receive_some; destruct head; cbn in *; lia.
    + reduce_cancel_channel. 
      inversion receive_some; destruct head; cbn in *; lia.
  - now erewrite sumZ_permutation in IH by eauto.
  - solve_facts.
Qed.


Lemma balance_on_chain :
    forall bstate caddr,
    reachable bstate ->
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    outgoing_acts bstate caddr = [] ->
    exists cstate,
      contract_state bstate caddr = Some cstate /\
      env_account_balances bstate caddr = cstate.(balance).
Proof.
  intros * reach deployed.
  specialize balance_on_chain' as (cstate & balance); eauto.
  intros Hact. rewrite Hact in balance. cbn in *.
  exists cstate. destruct balance.
  split.
  eauto.
  lia.
Qed.

Lemma balance_on_chain_forall :
    forall bstate caddr cstate,
    reachable bstate ->
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    outgoing_acts bstate caddr = [] ->
    contract_state bstate caddr = Some cstate ->
    env_account_balances bstate caddr = cstate.(balance).
Proof.
  intros.
  eapply balance_on_chain in H;eauto.
  destruct H;
  destruct_and_split.
  rewrite H2 in H.
  inversion H; subst;
  eauto.
Qed.

Lemma balance_zero_close_and_exipred :
    forall bstate caddr cstate,
    reachable bstate ->
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    outgoing_acts bstate caddr = [] ->
    contract_state bstate caddr = Some cstate ->
    (cstate.(channel_state) = Closed \/ cstate.(channel_state) = Expired) ->
    env_account_balances bstate caddr = 0%Z.
Proof.
  intros.
  assert(H_reachable : reachable bstate). eauto.
  eapply balance_on_chain in H;eauto.
  destruct H;
  destruct_and_split.
  destruct_or_hyps.
  rewrite H2 in H.
  inversion H; subst;
  eauto.
  rewrite H4.
  eapply closed_or_expired_bal_eq_zero_forall;eauto.
  rewrite H4.
  eapply closed_or_expired_bal_eq_zero_forall;eauto.
  rewrite H2 in H.
  inversion H. subst.
  eauto.
Qed.

Lemma balance_not_zero_open :
    forall bstate caddr cstate,
    reachable bstate ->
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    outgoing_acts bstate caddr = [] ->
    contract_state bstate caddr = Some cstate ->
    cstate.(channel_state) = Open ->
    env_account_balances bstate caddr <> 0%Z.
Proof.
  intros.
  assert(H_reachable : reachable bstate). eauto.
  eapply balance_on_chain in H;eauto.
  destruct H;
  destruct_and_split.
  destruct_or_hyps.
  rewrite H2 in H.
  inversion H; subst;
  eauto.
  rewrite H4.
  eapply open_bal_not_eq_zero_forall;eauto.
Qed.


Lemma bal_not_eq_zero_state_open bstate caddr:
  reachable bstate ->
  env_contracts bstate caddr = Some (contract : WeakContract) ->
  exists cstate, 
  contract_state bstate caddr = Some cstate /\
  ((cstate.(balance) <> 0)%Z -> (cstate.(channel_state) = Open )).
Proof.
  contract_induction;intros;cbn in *;eauto;try congruence;try lia.
  - unfold init in init_some.
    destruct (address_is_contract (ctx_from ctx)
    || address_is_contract (receiver_addr setup) || 
    (ctx_amount ctx <? 1)%Z || (duration setup - current_slot chain =? 7)%nat) eqn : requirements_check;try congruence.
    inversion init_some.
    simpl.
    eauto.
  - unfold receive in receive_some.
    destruct (negb (address_is_contract (ctx_from ctx)) && (ctx_amount ctx =? 0)%Z) eqn:requirements_check;try congruence.
    propify.
    destruct_and_split.
    destruct_message;try congruence.
    + reduce_authorize_payment.
      cbn in receive_some.
      inversion receive_some.
      simpl.
      unfold eqb_PaymentChannelState in EState.
      destruct (channel_state prev_state) eqn : H'; try congruence;eauto.
    + reduce_collect_payment.
      cbn in receive_some.
      inversion receive_some.
      simpl in * .
      rewrite <- H3 in H.
      simpl in H.
      lia.
    + reduce_cancel_channel.
      cbn in receive_some.
      inversion receive_some.
      simpl in * .
      rewrite <- H3 in H.
      simpl in H.
      lia.
  - unfold receive in receive_some.
    destruct (negb (address_is_contract (ctx_from ctx)) && (ctx_amount ctx =? 0))%Z eqn:requirements_check;try congruence.
    propify.
    destruct_and_split.
    destruct_message;try congruence.
    + reduce_authorize_payment.
      cbn in receive_some.
      inversion receive_some.
      simpl.
      unfold eqb_PaymentChannelState in EState.
      destruct (channel_state prev_state) eqn : H'; try congruence;eauto.
    + reduce_collect_payment.
      cbn in receive_some.
      inversion receive_some.
      simpl in * .
      rewrite <- H3 in H.
      simpl in H.
      lia.
    + reduce_cancel_channel.
      cbn in receive_some.
      inversion receive_some.
      simpl in * .
      rewrite <- H3 in H.
      simpl in H.
      lia.
  - solve_facts.
Qed.

Lemma bal_not_eq_zero_state_open_forall bstate caddr cstate:
  reachable bstate ->
  env_contracts bstate caddr = Some (contract : WeakContract) ->
  contract_state bstate caddr = Some cstate ->
  (cstate.(balance) <> 0)%Z -> 
  (cstate.(channel_state) = Open ).
Proof.
  intros.
  eapply bal_not_eq_zero_state_open in H;eauto.
  destruct H;
  destruct_and_split;
  rewrite H in H1;
  inversion H1; subst;
  eauto.
Qed.


Lemma bal_eq_zero_closed_or_expired bstate caddr:
  reachable bstate ->
  env_contracts bstate caddr = Some (contract : WeakContract) ->
  exists cstate, 
  contract_state bstate caddr = Some cstate /\
  ((cstate.(balance) = 0)%Z ->
  (cstate.(channel_state) = Closed \/
   cstate.(channel_state) = Expired )).
Proof.
  contract_induction;intros;cbn in *;eauto;try congruence;try lia.
  - unfold init in init_some.
    destruct (address_is_contract (ctx_from ctx)
    || address_is_contract (receiver_addr setup) || 
    (ctx_amount ctx <? 1)%Z || (duration setup - current_slot chain =? 7)%nat) eqn:requirements_check; try congruence.
    inversion init_some; subst.
    simpl in *.
    propify.
    destruct_and_split.
    lia.
  - unfold receive in receive_some.
    destruct (negb (address_is_contract (ctx_from ctx)) && (ctx_amount ctx =? 0))%Z eqn:requirements_check; try congruence.
    propify.
    destruct_and_split.
    destruct_message; try congruence.
    + reduce_authorize_payment.
      inversion receive_some.
      cbn in *.
      unfold eqb_PaymentChannelState in EState.
      destruct (channel_state prev_state) eqn:H';try congruence.
      rewrite <- H3 in H.
      simpl in H.
      apply IH in H.
      congruence.
    + reduce_collect_payment.
      inversion receive_some.
      cbn in *.
      eauto.
    + reduce_cancel_channel.
      inversion receive_some.
      cbn in *.
      eauto.
  - unfold receive in receive_some.
    destruct (negb (address_is_contract (ctx_from ctx)) && (ctx_amount ctx =? 0))%Z eqn:requirements_check; try congruence.
    propify.
    destruct_and_split.
    destruct_message; try congruence.
    + reduce_authorize_payment.
      inversion receive_some.
      cbn in *.
      unfold eqb_PaymentChannelState in EState.
      destruct (channel_state prev_state) eqn:H';try congruence.
      rewrite <- H3 in H.
      simpl in H.
      apply IH in H.
      congruence.
    + reduce_collect_payment.
      inversion receive_some.
      cbn in *.
      eauto.
    + reduce_cancel_channel.
      inversion receive_some.
      cbn in *.
      eauto.
  - solve_facts.
Qed.

Lemma bal_eq_zero_closed_or_expired_forall bstate caddr cstate :
  reachable bstate ->
  env_contracts bstate caddr = Some (contract : WeakContract) ->
  contract_state bstate caddr = Some cstate ->
  (cstate.(balance) = 0)%Z ->
  (cstate.(channel_state) = Closed \/
   cstate.(channel_state) = Expired ).
Proof.
  intros.
  eapply bal_eq_zero_closed_or_expired in H;eauto.
  destruct H;
  destruct_and_split;
  rewrite H in H1;
  inversion H1; subst;
  eauto.
Qed.   

Open Scope Z.

Lemma add_block_exec_from_delta_gt_zero:
  forall bstate caddr creator (trace : ChainTrace empty_state bstate),
    ActiveContract bstate caddr contract ->
    (funds bstate caddr > 0)%Z ->
    address_not_contract creator = true->
    exists next_header,
      validate_header next_header bstate = true /\
      exists acts mid_bstate new_bstate,
      ActionsGeneratedByStrategy delta_ideal_alice_strategy caddr trace acts /\
      add_block_exec deep_first bstate next_header acts = Ok new_bstate /\
      stratSucc bstate mid_bstate delta_ideal_alice_strategy caddr /\
      nonStratSucc mid_bstate new_bstate caddr /\
      (funds new_bstate caddr = 0)%Z. 
Proof.
Admitted.
(* Proof.
  intros * H_observ H_fund H_creator.
  set (header := (build_block_Header
  (S (chain_height bstate))
  (current_slot bstate + 1)%nat
  (finalized_height bstate)
  (10)
  creator)).
  exists header.
  assert(H_header : validate_header header bstate = true).
  {
    unfold validate_header.
    propify.
    repeat split;simpl;eauto;try lia.
  }
  unfold ActiveContract in H_observ.
  destruct H_observ as [H_bstate [H_queue H_contract]].
  assert(H_cstate:exists cstate : State, contract_state bstate caddr = Some cstate).
  {
    apply (deployed_contract_state_typed H_contract);eauto.
  }
  destruct H_cstate.
  rename x into cstate.
  rename H into H_cstate.
  assert (H_constants : address_not_contract cstate.(sender) = true
  /\ address_not_contract cstate.(receiver) = true).
  {
    eapply alice_and_bob_is_EOA_forall;eauto.
  }
  destruct H_constants as [H_sender_not_ctr H_receiver_not_ctr].
  assert (H_header_t : validate_header header bstate = true) by eauto.
  unfold validate_header in H_header_t.
  assert (exists bstate', reachable_through bstate bstate' /\ 
    (current_slot bstate' >= expiry cstate)%nat).
  {
    forward_time (cstate.(expiry)+1)%nat.
    eauto.
    eauto.
    apply address_not_contract_negb in H_creator.
    eauto.
    assert (block_reward header>=0) by lia.
    eauto.
    exists bstate0.
    split;eauto.
    lia.
  }
  rename H into H_cur_forward.
  propify.
  destruct_and_split.
  rename H into H_header_1.
  rename H2 into H_header_2.
  rename H3 into H_header_3.
  rename H4 into H_through_x.
  rename x into bstate'.
  eauto.
  rename H into H_header_1.
  rename H2 into H_header_2.
  rename H3 into H_header_3.
  rename H4 into H_through_x.
  unfold ActionsGeneratedByStrategy.
  rename H0 into H_header_4.
  unfold delta_ideal_alice_strategy.
  
  
  unfold get_payment_channel_state.
  assert(H': contract_state bstate caddr = Some cstate) by eauto.
  unfold contract_state in H'.
  simpl in H'.
  rewrite H'.
  unfold funds in H_fund.
  assert (H_balance_eq : env_account_balances bstate caddr = cstate.(balance)).
  {
    eapply balance_on_chain_forall;eauto.
    unfold outgoing_acts.
    rewrite H_queue.
    simpl.
    eauto.
  }
  assert (H :balance cstate > 0 ).
  {
    rewrite <- H_balance_eq.
    eauto.
  }
  assert(channel_state cstate = Open).
  {
    eapply bal_not_eq_zero_state_open_forall;eauto.
    lia.
  }
  rewrite H0.
  destruct ((expiry cstate <=? current_slot bstate)%nat) eqn:H_time.
  + exists [alice_cancel cstate caddr].
    set (mid := {|
    chain_state_env := add_new_block_to_env header bstate;
    chain_state_queue := [alice_cancel cstate caddr]
    |}).
    exists mid.
    unfold add_block_exec.
    rewrite H_header.
    unfold find_invalid_root_action.
    simpl.
    destruct_address_eq;simpl;try congruence;eauto.
    apply address_not_contract_negb in H_sender_not_ctr.
    rewrite H_sender_not_ctr.
    unfold send_or_call.
    simpl.
    destruct_address_eq;try congruence.
    ++  apply (contract_addr_format caddr contract) in H_bstate.
        rewrite e3 in H_bstate.
        apply address_not_contract_negb in H_creator.
        congruence.
        eauto.
    ++  assert(Ht1:0 >? 10 + env_account_balances bstate (sender cstate) = false).
       {
        propify.
        eapply (account_balance_nonnegative bstate (sender cstate)) in H_bstate.
        lia.
       }
       rewrite Ht1.
       rewrite H_contract.
       assert(Ht2:contract_state bstate caddr = Some cstate) by eauto.
       unfold contract_state in Ht2;simpl in Ht2.
       destruct (env_contract_states bstate caddr);try congruence.
       simpl.
       rewrite Ht2.
       unfold result_of_option.
       setoid_rewrite deserialize_serialize.
       unfold receive.
       simpl.
       rewrite H_sender_not_ctr.
       simpl.
       unfold cancel_channel.
       simpl.
       destruct_address_eq;try congruence.
       assert (Ht3:(expiry cstate <=? current_slot bstate + 1)%nat = true).
       {
          propify.
          lia.
       }
       erewrite Ht3.
       simpl.
       unfold send_or_call.
       assert (ht4: balance cstate <? 0 = false ) by lia.
       rewrite ht4.
       simpl.
       destruct_address_eq;try congruence.
       assert(ht5:balance cstate >? 0 + env_account_balances bstate caddr = false).
       {
        lia.
       }
       rewrite ht5.
       assert (H_none: env_contracts bstate (sender cstate) = None).
        { destruct (env_contracts bstate (sender cstate)) eqn:H_env.
          - exfalso.
            apply (contract_addr_format (sender cstate) w) in H_bstate; eauto.
            congruence.
          - reflexivity.
        }
        rewrite H_none.
        rewrite H_sender_not_ctr.
        simpl.
        set (new := {|
          chain_state_env :=
            transfer_balance caddr (sender cstate) (balance cstate)
              (set_contract_state caddr
                (serialize (cstate <| channel_state := Expired |> <| balance := 0 |>))
                (transfer_balance (sender cstate) caddr 0
                    (add_new_block_to_env header bstate)));
          chain_state_queue := []
        |}).
        exists new.
        split.
        apply Forall_forall.
        simpl.
        eauto.
        intros.
        destruct H2;try congruence.
        left.
        eauto.
        inversion H2.
        split;eauto.
        unfold stratSucc.
        simpl.
        split.
        * exists trace.
          exists header.
          exists [alice_cancel cstate caddr].
         ** unfold ActionsGeneratedByStrategy.
            assert(Ht5: contract_state bstate caddr = Some cstate) by eauto.
            unfold contract_state in Ht5.
            simpl in Ht5.
            destruct(env_contract_states bstate caddr);try congruence.
            setoid_rewrite Ht5.
            rewrite H0.
            assert (ht6 : (expiry cstate <=? current_slot bstate)%nat = true).
            {
              propify.
              eauto.
            }
            rewrite ht6.
            repeat split;simpl;eauto;try lia.
            - apply address_not_contract_negb in H_creator.
              eauto.
            - apply Forall_forall.
              simpl.
              unfold act_origin_is_eq_from.
              intros.
              destruct_address_eq;try congruence.
              unfold alice_cancel in *.
              destruct_or_hyps.
              rewrite <- H2 in n3.
              simpl in n3.
              eauto.
              inversion H2.
        * split.
          ** unfold nonStratSucc.
             exists [alice_cancel cstate caddr].
             simpl.
             split.
             eauto.
             unfold send_or_call.
             simpl.
             destruct_address_eq;try congruence.
              rewrite Ht1.
              rewrite H_contract.
              simpl.
              assert(Ht7:contract_state bstate caddr = Some cstate) by eauto.
              unfold contract_state in Ht7;simpl in Ht7.
              destruct (env_contract_states bstate caddr);try congruence.
              simpl.
              rewrite Ht7.
              unfold result_of_option.
              setoid_rewrite deserialize_serialize.
              unfold receive.
              simpl.
              rewrite H_sender_not_ctr.
              simpl.
              unfold cancel_channel.
              simpl.
              destruct_address_eq;try congruence.
              erewrite Ht3.
              simpl.
              unfold send_or_call.
              rewrite ht4.
              simpl.
              destruct_address_eq;try congruence.
              rewrite ht5.
              rewrite H_none.
              rewrite H_sender_not_ctr.
              simpl.
              split.
              eauto.
              eauto.
          ** destruct_address_eq; try congruence.
             lia.
    ++ apply (contract_addr_format caddr contract) in H_bstate.
        rewrite e0 in H_bstate.
        apply address_not_contract_negb in H_creator.
        congruence.
        eauto.
    ++ apply (contract_addr_format caddr contract) in H_bstate.
        rewrite e1 in H_bstate.
        apply address_not_contract_negb in H_creator.
        congruence.
        eauto.
    ++ assert(Ht1:0 >? env_account_balances bstate (sender cstate) = false).
        {
        propify.
        eapply (account_balance_nonnegative bstate (sender cstate)) in H_bstate.
        lia.
        }
        rewrite Ht1.
        rewrite H_contract.
        assert(Ht2:contract_state bstate caddr = Some cstate) by eauto.
        unfold contract_state in Ht2;simpl in Ht2.
        destruct (env_contract_states bstate caddr);try congruence.
        simpl.
        rewrite Ht2.
        unfold result_of_option.
        setoid_rewrite deserialize_serialize.
        unfold receive.
        simpl.
        rewrite H_sender_not_ctr.
        simpl.
        unfold cancel_channel.
        simpl.
        destruct_address_eq;try congruence.
        assert (Ht3:(expiry cstate <=? current_slot bstate + 1)%nat = true).
        {
          propify.
          lia.
        }
        erewrite Ht3.
        simpl.
        unfold send_or_call.
        assert (ht4: balance cstate <? 0 = false ) by lia.
        rewrite ht4.
        simpl.
        destruct_address_eq;try congruence.
        assert(ht5:balance cstate >? 0 + env_account_balances bstate caddr = false).
        {
        lia.
        }
        rewrite ht5.
        assert (H_none: env_contracts bstate (sender cstate) = None).
        { destruct (env_contracts bstate (sender cstate)) eqn:H_env.
          - exfalso.
            apply (contract_addr_format (sender cstate) w) in H_bstate; eauto.
            congruence.
          - reflexivity.
        }
        rewrite H_none.
        rewrite H_sender_not_ctr.
        simpl.
        set (new := {|
          chain_state_env :=
            transfer_balance caddr (sender cstate) (balance cstate)
              (set_contract_state caddr
                (serialize (cstate <| channel_state := Expired |> <| balance := 0 |>))
                (transfer_balance (sender cstate) caddr 0
                    (add_new_block_to_env header bstate)));
          chain_state_queue := []
        |}).
        exists new.
        split.
        apply Forall_forall.
        simpl.
        eauto.
        intros.
        destruct H2.
        left.
        eauto.
        inversion H2.
        split;eauto.
        unfold stratSucc.
        simpl.
        split.
        * exists trace.
          exists header.
          exists [alice_cancel cstate caddr].
          ** unfold ActionsGeneratedByStrategy.
            assert(Ht5: contract_state bstate caddr = Some cstate) by eauto.
            unfold contract_state in Ht5.
            simpl in Ht5.
            destruct(env_contract_states bstate caddr);try congruence.
            setoid_rewrite Ht5.
            rewrite H0.
            assert (ht6 : (expiry cstate <=? current_slot bstate)%nat = true).
            {
              propify.
              eauto.
            }
            rewrite ht6.
            repeat split;simpl;eauto;try lia.
            - apply address_not_contract_negb in H_creator.
              eauto.
            - apply Forall_forall.
              simpl.
              unfold act_origin_is_eq_from.
              intros.
              destruct_address_eq;try congruence.
              unfold alice_cancel in *.
              destruct_or_hyps.
              rewrite <- H2 in n5.
              simpl in n5.
              eauto.
              inversion H2.
        * split.
          ** unfold nonStratSucc.
              exists [alice_cancel cstate caddr].
              simpl.
              split.
              eauto.
              unfold send_or_call.
              simpl.
              destruct_address_eq;try congruence.
              rewrite Ht1.
              rewrite H_contract.
              simpl.
              assert(Ht7:contract_state bstate caddr = Some cstate) by eauto.
              unfold contract_state in Ht7;simpl in Ht7.
              destruct (env_contract_states bstate caddr);try congruence.
              simpl.
              rewrite Ht7.
              unfold result_of_option.
              setoid_rewrite deserialize_serialize.
              unfold receive.
              simpl.
              rewrite H_sender_not_ctr.
              simpl.
              unfold cancel_channel.
              simpl.
              destruct_address_eq;try congruence.
              erewrite Ht3.
              simpl.
              unfold send_or_call.
              rewrite ht4.
              simpl.
              destruct_address_eq;try congruence.
              rewrite ht5.
              rewrite H_none.
              rewrite H_sender_not_ctr.
              simpl.
              split.
              eauto.
              eauto.
          ** destruct_address_eq; try congruence.
              lia.
  + 
 
       
    

    



  
Admitted. *)

(* 辅助引理 *)
Lemma IsValidNextBlock_implies_validate_header :
  forall header bstate,
    IsValidNextBlock header bstate ->
    validate_header header bstate = true.
Proof.
  intros header bstate H_valid.
  destruct H_valid.
  unfold validate_header.
  propify.
  repeat split;eauto.
  unfold Blockchain.address_not_contract.
  rewrite valid_creator.
  simpl. eauto.
  lia.
Qed.

Require Import Coq.Logic.FunctionalExtensionality.
Import ListNotations.

Lemma EnvironmentEquiv_eq : forall e1 e2,
  EnvironmentEquiv e1 e2 ->
  e1 = e2.
Proof.
  intros e1 e2 Hequiv.
  destruct Hequiv as [H_chain_eq H_balances_eq H_contracts_eq H_contract_states_eq].
  destruct e1 as [chain1 acc_balances1 contracts1 contract_states1].
  destruct e2 as [chain2 acc_balances2 contracts2 contract_states2].
  simpl in *.
  subst chain2.
  f_equal; 
    [ 
      (* env_account_balances *)
      extensionality a; 
      apply H_balances_eq
    | 
      (* env_contracts *)
      extensionality a; 
      apply H_contracts_eq
    | 
      (* env_contract_states *)
      extensionality addr; 
      apply H_contract_states_eq
    ].
Qed.

Lemma prove_chainstate_equality :
  forall s' x0 bstate x1,
    EnvironmentEquiv (chain_state_env s') (add_new_block_to_env x0 bstate) ->
    chain_state_queue s' = x1 ->
    s' = {| chain_state_env := add_new_block_to_env x0 bstate; chain_state_queue := x1 |}.
Proof.
  intros s' x0 bstate x1 H9 H6.
  (* 解构 s' 记录 *)
  destruct s' as [env queue].
  simpl in *.
  (* 使用辅助引理将 EnvironmentEquiv 转换为环境相等 *)
  apply EnvironmentEquiv_eq in H9.
  subst env.
  (* 使用 H6 证明 queue = x1 *)
  subst queue.
  (* 证明 s' 等于目标记录 *)
  reflexivity.
Qed.
Lemma find_none_implies_all_false :
  forall (A : Type) (P : A -> bool) (l : list A),
    find P l = None ->
    Forall (fun x => P x = false) l.
Proof.
  intros A P l Hfind.
  induction l as [|a l' IH].
  - apply Forall_nil.
  - simpl in Hfind.
    destruct (P a) eqn:Heq.
    + inversion Hfind.
    + apply Forall_cons.
      * assumption.
      * apply IH. assumption.
Qed.

(* Assuming necessary imports and definitions are already in place *)

Lemma execute_actions_success_empty_queue :
  forall count bstate depth_first s'0,
    execute_actions count bstate depth_first = Ok s'0 ->
    chain_state_queue s'0 = [].
Proof.
  induction count as [| count' IH].
  - 
    intros bstate depth_first s'0 H_exec.
    simpl in H_exec.
    inversion H_exec.
    destruct_match in H0.
    inversion H0.
    simpl.
    eauto.
    congruence.
  - 
    intros bstate depth_first s'0 H_exec.
    simpl in H_exec.
    destruct (chain_state_queue bstate) as [| act acts'] eqn:H_acts.
    + 
      inversion H_exec.
      reflexivity.
    + 
      destruct (execute_action act bstate.(chain_state_env)) as [new_bstate | e] eqn:H_exec_act.
      * 
        destruct depth_first eqn:H_depth.
        -- 
           simpl.
           simpl in H_exec.
           specialize (IH (build_chain_state new_bstate.(chain_state_env) (new_bstate.(chain_state_queue) ++ acts')) depth_first).
           apply IH. eauto. rewrite H_depth.
           assumption.
        -- 
           simpl.
           simpl in H_exec.
           specialize (IH (build_chain_state new_bstate.(chain_state_env) (acts' ++ new_bstate.(chain_state_queue))) depth_first).
           apply IH. rewrite H_depth.
           assumption.
      * 
        inversion H_exec.
Qed.



Lemma lm0: forall bstate caddr creator next_header acts new_bstate (trace : ChainTrace empty_state bstate),
  ActiveContract bstate caddr contract  ->
  address_not_contract creator = true->
  validate_header next_header bstate = true ->
  (exists cstate,
    contract_state bstate caddr = Some cstate /\
    (cstate.(expiry) <= bstate.(current_slot))%nat) ->
    ActionsGeneratedByStrategy delta_ideal_alice_strategy caddr trace acts ->
    add_block_exec deep_first bstate next_header acts = Ok new_bstate ->
    exists mid,
    mid = {|
    chain_state_env := add_new_block_to_env next_header bstate;
    chain_state_queue := acts
    |} /\
    stratSucc bstate mid delta_ideal_alice_strategy caddr /\
    nonStratSucc mid new_bstate caddr .
Proof.
  (* intros.
  unfold add_block_exec in H3.
  rewrite H1 in H3.
  destruct (find_origin_neq_from acts) eqn: fonf ;try congruence.
  destruct (find_invalid_root_action acts) eqn: fira ;try congruence.
  unfold ActiveContract in H.
  destruct_and_split.
  unfold validate_header  in H1.
  propify.
  destruct_and_split.
  set (mid_bstate := {|
  chain_state_env := add_new_block_to_env next_header bstate;
  chain_state_queue := acts
  |}).
  exists mid_bstate.
  split.
  eauto.
  split.
  unfold stratSucc.
  exists trace.
  exists next_header.
  exists acts.
  repeat split;eauto.
  apply address_not_contract_negb in H7.
  eauto.
  lia.
  apply find_none_implies_all_false.
  apply fira.
  unfold act_origin_is_eq_from.
  apply find_none_implies_all_false in fonf.
  apply Forall_impl with (P := fun act => address_neqb (act_origin act) (act_from act) = false).
  intros act H'.
  destruct_address_eq;try congruence;eauto.
  apply fonf.
  unfold nonStratSucc.
  exists acts.
  split.
  eauto.
  split.
  eauto.
  apply (execute_actions_success_empty_queue stack_count mid_bstate deep_first new_bstate) .
  eauto. *)
Admitted.

Lemma lm0': forall bstate caddr creator next_header (trace : ChainTrace empty_state bstate),
  ActiveContract bstate caddr contract  ->
  address_not_contract creator = true->
  validate_header next_header bstate = true ->
  (exists cstate,
    contract_state bstate caddr = Some cstate /\
    (cstate.(expiry) > bstate.(current_slot))%nat) ->
      exists new_bstate,
      (nonStratSucc bstate new_bstate caddr /\
       (exists cstate',
        contract_state new_bstate caddr = Some cstate' /\
        (cstate'.(expiry) <= new_bstate.(current_slot))%nat)).
Proof.
Admitted.


Lemma lm2: forall bstate caddr creator next_header acts (trace : ChainTrace empty_state bstate),
  ActiveContract bstate caddr contract ->
  address_not_contract creator = true->
  validate_header next_header bstate = true ->
  funds bstate caddr > 0 ->
  ActionsGeneratedByStrategy delta_ideal_alice_strategy caddr trace acts ->
  (exists cstate,
    contract_state bstate caddr = Some cstate /\
    (cstate.(expiry) <= bstate.(current_slot))%nat) ->
  (exists new_bstate,
    add_block_exec deep_first bstate next_header acts = Ok new_bstate /\
    funds new_bstate caddr = 0).
Proof.
Admitted.


(* Generalized definition of ActionsCanSuccessReceive *)
Definition ActionsCanSuccessReceive 
           (validate : Action -> bool) 
           (acts : list Action) 
           : Prop :=
  Forall (fun act => validate act = true) acts.


(* Using the generalized ActionsCanSuccessReceive with Payment Channel validation *)
Definition PaymentChannel_ActionsCanSuccessReceive 
           (contract : Contract Setup Msg State Error) 
           (acts : list Action) 
           : Prop :=
  ActionsCanSuccessReceive validate_payment_channel_action_msg acts.

Lemma LM3 :forall bstate bstate' header acts,
  reachable bstate ->
 add_block_exec Depth bstate header acts = Ok bstate' ->
 reachable bstate'.
Proof.
Admitted.

Require Import Coq.Init.Nat.
Open Scope nat.
(* 定义 gt_nat 函数，用于判断 x 是否大于 y *)
Fixpoint gt_nat (x y : nat) : bool :=
  match x, y with
  | 0, _ => false
  | S x', 0 => true                           (* 任何正数都大于 0 *)
  | S x', S y' => gt_nat x' y'                (* 递归比较前一个数 *)
  end.
(* 定义 >? 的记号 *)
Notation "x >? y" := (gt_nat x y) (at level 70).

Lemma gt_nat_false_implies_le :
  forall x y,
    (x >? y) = false ->
    x <= y.
Proof.
  intros x y H.
  generalize dependent y.
  induction x as [| x' IH].
  - (* 基本情况: x = 0 *)
    intros y H.
    apply le_0_n.
  - 
    intros [| y'] H.
    + 
      discriminate.
    + 
      simpl in H.
      apply IH in H.
      apply le_n_S.
      assumption.
Qed.


Definition ExistsExpiryTimeoutTrace (delta : strat) (caddr : Address) (s : ChainState) : Prop :=
  forall cstate,
    get_payment_channel_state s caddr = Some cstate -> 
    (expiry cstate >? current_slot s) = true ->
    exists s',
      StrategyTrace delta caddr s s' /\
      (expiry cstate >? current_slot s') = false.



  



Lemma fm1: forall bstate caddr creator delta (trace : ChainTrace empty_state bstate) cstate,
  ActiveContract bstate caddr contract  ->
  address_not_contract creator = true->
  fund_gt_zero bstate caddr ->
    contract_state bstate caddr = Some cstate ->
    (expiry cstate >? current_slot bstate) = true ->
    exists s'0 : ChainState,
      StrategyTrace delta caddr bstate s'0 /\
      funds s'0 caddr = 0%Z.
Proof.
Admitted.

Lemma fm1': forall bstate caddr creator delta (trace : ChainTrace empty_state bstate) cstate,
  ActiveContract bstate caddr contract  ->
  address_not_contract creator = true->
  fund_gt_zero bstate caddr ->
    contract_state bstate caddr = Some cstate ->
    (expiry cstate >? current_slot bstate) = true ->
    exists s'0 : ChainState,
      StrategyTrace delta caddr bstate s'0 /\
      funds s'0 caddr = 0%Z.
Proof.
Admitted.

(* 可证 *)
Lemma fm2: forall bstate caddr creator delta (trace : ChainTrace empty_state bstate),
  ActiveContract bstate caddr contract  ->
  address_not_contract creator = true->
  (exists cstate,
    contract_state bstate caddr = Some cstate /\
    (cstate.(expiry) <= bstate.(current_slot))%nat) ->
      exists new_bstate,
      (stratSucc bstate new_bstate delta caddr /\
        funds new_bstate caddr = 0)%Z.
Proof.
Admitted.

Lemma add_block_reachable_through (prev_bstate next_bstate : ChainState) df header actions (trace : ChainTrace empty_state prev_bstate)  :
    df = true ->
    add_block_exec df prev_bstate header actions = Ok next_bstate ->
     reachable_through prev_bstate next_bstate.
Proof.
Admitted.

Lemma stratSucc_reachable_through prev_bstate next_bstate delta caddr :
  reachable prev_bstate ->
  stratSucc prev_bstate next_bstate delta caddr ->
  reachable_through prev_bstate next_bstate.
Proof.
Admitted.


Lemma StrategyTrace_chain_trace_reachable_through prev_bstate next_bstate delta caddr (trace : ChainTrace empty_state prev_bstate):
  reachable prev_bstate ->
  StrategyTrace delta caddr prev_bstate next_bstate ->
  reachable_through prev_bstate next_bstate.
Proof.
Admitted.

Lemma StrategyTrace_chain_trace prev_bstate next_bstate delta caddr (trace : ChainTrace empty_state prev_bstate):
reachable prev_bstate ->
  StrategyTrace delta caddr prev_bstate next_bstate ->
  ChainTrace empty_state next_bstate.
Proof.
Admitted.

Lemma StrategyTrace_empty_queue prev_bstate next_bstate delta caddr :
StrategyTrace delta caddr prev_bstate next_bstate ->
next_bstate.(chain_state_queue) = [].
Proof.
Admitted.

Lemma stratSucc_next_state_queue prev_bstate next_bstate delta caddr :
reachable prev_bstate ->
stratSucc prev_bstate next_bstate delta caddr ->
next_bstate.(chain_state_queue) = [].
Proof.
Admitted.

Lemma stratSucc_preserves_expiry :
  forall s s' delta caddr,
    stratSucc s s' delta caddr ->
    forall cstate_s cstate_s',
      contract_state s caddr = Some cstate_s ->
      contract_state s' caddr = Some cstate_s' ->
      cstate_s.(expiry) = cstate_s'.(expiry).
Proof.
intros s s' delta caddr Hsucc cstate_s cstate_s' Hcstate_s Hcstate_s'.
destruct Hsucc as [trace  [Hnew_env [Hnew_actions H ]]].
destruct_and_split.
induction Hnew_actions; subst.
- unfold add_block_exec in H5.
  destruct_match in H5;try congruence.
  destruct_match in H5;try congruence.
  destruct_match in H5;try congruence.
  unfold execute_actions in H5.
  simpl in *.
  inversion H5.
  subst.
  simpl.
Admitted.

Theorem uniDPStratLiquid : StratLiquid contract delta_ideal_alice_strategy.
Proof.
  unfold StratLiquid.
  intros * trace H_observ  H_creator H_gtZero.
  eapply C1'.
  right.
  intros s' H_stratSucc.
  
  apply C2'.
  destruct (Z.eq_dec (funds s'.(chain_state_env) caddr) 0%Z) as [H_fund_zero | H_fund_nonzero].
  - left.
    unfold fund_eq_zero.
    unfold funds in *.
    eauto.
  - right.
    assert(H_observ': ActiveContract bstate caddr contract) by eauto.
    unfold ActiveContract in H_observ'.
    destruct_and_split.
    assert(H' : env_contracts bstate caddr = Some (contract:WeakContract)) by eauto.
    eapply deployed_contract_state_typed in H1;eauto.
    destruct H1.
    rename x into cstate.
    rename s' into s.
    assert (stratSucc bstate s delta_ideal_alice_strategy caddr) by
    eauto.
    assert(reachable_through bstate s).
    {
      eapply stratSucc_reachable_through.
      eauto.
      eauto.
    }
    assert(env_contracts s caddr = Some (contract : WeakContract)).
    {
      eapply reachable_through_contract_deployed.
      eauto.
      unfold ActiveContract  in H_observ.
      destruct_and_split.
      eauto.
    }
    eapply deployed_contract_state_typed in H4.
    
    destruct H4.
    rename x into cstate'. 
    destruct ((cstate'.(expiry)) >? s.(current_slot)) eqn:time.
    + assert(H_stratSucc' : stratSucc bstate s delta_ideal_alice_strategy caddr) by eauto.
    
    unfold stratSucc in H_stratSucc'.
    destruct_and_split.
    
      assert(trace' : ChainTrace empty_state s).
      {
        eapply (add_block_trace  bstate s Depth x0 x1) in H11. eauto.
         eauto.
      }
      
      assert(reachable_through bstate s).
      {
        eapply stratSucc_reachable_through.
        eauto.
        eauto.
      }
      
      assert(env_contracts s caddr = Some (contract : WeakContract)).
      {
        eapply reachable_through_contract_deployed.
        eauto.
        unfold ActiveContract  in H_observ.
        destruct_and_split.
        eauto.
      }
      assert(ActiveContract s caddr contract).
      {
       unfold ActiveContract.
       split.
       apply trace_reachable in trace'.
       eauto.
       split.
       eauto.
       apply trace_reachable in trace'.
       eauto.
      }
      assert(ActiveContract s caddr contract) by eauto.
      assert(H_cstate' :exists cstate' ,contract_state s caddr = Some cstate').
      {
        eapply deployed_contract_state_typed in H13;eauto.
      }
      destruct H_cstate'. 
      rename x2 into scstate.
      eapply (fm1 s caddr creator delta_ideal_alice_strategy trace' cstate') in H14;eauto;try lia.
      destruct H14.
      rename x2 into s'.
      destruct H14.
      exists s'.
      split.
      eauto.
      apply C1'.
      left.
      unfold fund_eq_zero.
      eauto.
      unfold fund_gt_zero.
      eapply reachable_through_reachable in H12.
      apply (account_balance_nonnegative s caddr) in H12.
      unfold funds in *.
      lia.
    + propify.
          assert(H_stratSucc' : stratSucc bstate s delta_ideal_alice_strategy caddr) by eauto.
          unfold stratSucc in H_stratSucc'.
          destruct_and_split.
            assert(trace' : ChainTrace empty_state s).
            {
              eapply add_block_trace in H11. eauto. eauto.
            }
            assert(reachable_through bstate s).
            {
              eapply stratSucc_reachable_through.
              eauto.
              eauto.
            }
            assert(env_contracts s caddr = Some (contract : WeakContract)).
            {
              eapply reachable_through_contract_deployed.
              eauto.
              unfold ActiveContract  in H_observ.
              destruct_and_split.
              eauto.
            }
      
            assert(ActiveContract s caddr contract).
            {
             unfold ActiveContract.
             split.
             apply trace_reachable in trace'.
             eauto.
             split.
             eauto.
             apply trace_reachable in trace'.
             eauto.
            }
            assert(ActiveContract s caddr contract).
            {
             unfold ActiveContract.
             split.
             apply trace_reachable in trace'.
             eauto.
             split.
             eauto.
             apply trace_reachable in trace'.
             eauto.
            }
            assert(ActiveContract s caddr contract) by eauto.
            assert(H_cstate' :exists cstate' ,contract_state s caddr = Some cstate').
            {
              eapply deployed_contract_state_typed in H13;eauto.
            }
            destruct H_cstate'. 
            rename x2 into scstate.

          eapply (fm2 s caddr creator delta_ideal_alice_strategy trace' ) in H14;eauto;try lia.
          destruct H14.
        rename x2 into s'.
        destruct H14.
        exists s'.
        split.
        assert(stratSucc s s' delta_ideal_alice_strategy caddr) by eauto.
        apply single_step in H14.
        eauto.
        apply stratSucc_next_state_queue in H14.
        eauto.
        eauto.
        apply C1.
        left.
        unfold fund_eq_zero.
        eauto.
        apply trace_reachable in trace'.
        eauto.
        exists cstate'.
        split.
        eauto.
        apply gt_nat_false_implies_le in time.
        eauto.
    + eauto.

Qed.

Theorem uniDPStratLiquid : StratLiquid contract delta_ideal_alice_strategy.
Proof.
  unfold StratLiquid.
  intros * trace H_observ  H_creator H_gtZero.
  eapply C1.
  right.
  intros s' H_stratSucc.
  
  apply C2.
  destruct (Z.eq_dec (funds s'.(chain_state_env) caddr) 0%Z) as [H_fund_zero | H_fund_nonzero].
  - left.
    unfold fund_eq_zero.
    unfold funds in *.
    eauto.
  - right.
    assert(H_observ': ActiveContract bstate caddr contract) by eauto.
    unfold ActiveContract in H_observ'.
    destruct_and_split.
    assert(H' : env_contracts bstate caddr = Some (contract:WeakContract)) by eauto.
    eapply deployed_contract_state_typed in H1;eauto.
    destruct H1.
    rename x into cstate.
    rename s' into s.
    assert (stratSucc bstate s delta_ideal_alice_strategy caddr) by
    eauto.
    assert(reachable_through bstate s).
    {
      eapply stratSucc_reachable_through.
      eauto.
      eauto.
    }
    assert(env_contracts s caddr = Some (contract : WeakContract)).
    {
      eapply reachable_through_contract_deployed.
      eauto.
      unfold ActiveContract  in H_observ.
      destruct_and_split.
      eauto.
    }
    eapply deployed_contract_state_typed in H4.
    
    destruct H4.
    rename x into cstate'. 
    destruct ((cstate'.(expiry)) >? s.(current_slot)) eqn:time.
    + assert(H_stratSucc' : stratSucc bstate s delta_ideal_alice_strategy caddr) by eauto.
    
    unfold stratSucc in H_stratSucc'.
    destruct_and_split.
    
      assert(trace' : ChainTrace empty_state s).
      {
        eapply (add_block_trace  bstate s Depth x0 x1) in H11. eauto.
         eauto.
      }
      
      assert(reachable_through bstate s).
      {
        eapply stratSucc_reachable_through.
        eauto.
        eauto.
      }
      
      assert(env_contracts s caddr = Some (contract : WeakContract)).
      {
        eapply reachable_through_contract_deployed.
        eauto.
        unfold ActiveContract  in H_observ.
        destruct_and_split.
        eauto.
      }
      assert(ActiveContract s caddr contract).
      {
       unfold ActiveContract.
       split.
       apply trace_reachable in trace'.
       eauto.
       split.
       eauto.
       apply trace_reachable in trace'.
       eauto.
      }
      assert(ActiveContract s caddr contract) by eauto.
      assert(H_cstate' :exists cstate' ,contract_state s caddr = Some cstate').
      {
        eapply deployed_contract_state_typed in H13;eauto.
      }
      destruct H_cstate'. 
      rename x2 into scstate.
      eapply (fm1 s caddr creator delta_ideal_alice_strategy trace' cstate') in H14;eauto;try lia.
      destruct H14.
      rename x2 into s'.
      destruct H14.
      exists s'.
      split.
      eauto.
      apply C1.
      left.
      unfold fund_eq_zero.
      eauto.
      unfold fund_gt_zero.
      eapply reachable_through_reachable in H12.
      apply (account_balance_nonnegative s caddr) in H12.
      unfold funds in *.
      lia.
    + propify.
          assert(H_stratSucc' : stratSucc bstate s delta_ideal_alice_strategy caddr) by eauto.
          unfold stratSucc in H_stratSucc'.
          destruct_and_split.
            assert(trace' : ChainTrace empty_state s).
            {
              eapply add_block_trace in H11. eauto. eauto.
            }
            assert(reachable_through bstate s).
            {
              eapply stratSucc_reachable_through.
              eauto.
              eauto.
            }
            assert(env_contracts s caddr = Some (contract : WeakContract)).
            {
              eapply reachable_through_contract_deployed.
              eauto.
              unfold ActiveContract  in H_observ.
              destruct_and_split.
              eauto.
            }
      
            assert(ActiveContract s caddr contract).
            {
             unfold ActiveContract.
             split.
             apply trace_reachable in trace'.
             eauto.
             split.
             eauto.
             apply trace_reachable in trace'.
             eauto.
            }
            assert(ActiveContract s caddr contract).
            {
             unfold ActiveContract.
             split.
             apply trace_reachable in trace'.
             eauto.
             split.
             eauto.
             apply trace_reachable in trace'.
             eauto.
            }
            assert(ActiveContract s caddr contract) by eauto.
            assert(H_cstate' :exists cstate' ,contract_state s caddr = Some cstate').
            {
              eapply deployed_contract_state_typed in H13;eauto.
            }
            destruct H_cstate'. 
            rename x2 into scstate.

          eapply (fm2 s caddr creator delta_ideal_alice_strategy trace' ) in H14;eauto;try lia.
          destruct H14.
        rename x2 into s'.
        destruct H14.
        exists s'.
        split.
        assert(stratSucc s s' delta_ideal_alice_strategy caddr) by eauto.
        apply single_step in H14.
        eauto.
        apply stratSucc_next_state_queue in H14.
        eauto.
        eauto.
        apply C1.
        left.
        unfold fund_eq_zero.
        eauto.
        apply trace_reachable in trace'.
        eauto.
        exists cstate'.
        split.
        eauto.
        apply gt_nat_false_implies_le in time.
        eauto.
    + eauto.

Qed.


End theories.

