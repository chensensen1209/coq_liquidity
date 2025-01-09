From Coq Require Import Lia.
From Coq Require Import List. Import ListNotations.
From Coq Require Import Logic.Decidable.
From Coq Require Import ZArith.
Require Import Automation.
Require Import RecordUpdate.
Require Import Blockchain.
Require Import Serializable.
Require Import ResultMonad.

Section BuildUtils.
Context {BaseTypes : ChainBase}.

Lemma reachable_empty_state :
  reachable empty_state.
Proof.
  repeat constructor.
Qed.

(* Transitivity property of reachable and ChainTrace *)
Lemma reachable_trans from to :
  reachable from -> ChainTrace from to -> reachable to.
Proof.
intros [].
constructor.
eapply ChainedList.clist_app.
eauto.
eapply ChainedList.clist_app.
eauto.
constructor.
Qed.

(* Transitivity property of reachable and ChainStep *)
Lemma reachable_step from to :
  reachable from -> ChainStep from to -> reachable to.
Proof.
intros [].
do 2 econstructor.
eauto.
eauto.
Qed.

Ltac destruct_chain_step :=
  match goal with
  | [step: ChainStep _ _ |- _] =>
    destruct step as
        [?header ?queue_prev ?valid_header ?acts_from_accs ?origin_correct ?env_eq|
         ?act ?acts ?new_acts ?queue_prev ?eval ?queue_new
         ]
  end.

  Hint Resolve reachable_empty_state
  reachable_trans
  reachable_step : core.

  (* A state `to` is reachable through `mid` if `mid` is reachable and there exists a trace
    from `mid` to `to`. This captures that there is a valid execution ending up in `to`
    and going through the state `mid` at some point *)
Definition reachable_through mid to := reachable mid /\ inhabited (ChainTrace mid to).

(* A state is always reachable through itself *)
Lemma reachable_through_refl : forall bstate,
  reachable bstate -> reachable_through bstate bstate.
Proof.
intros bstate reach.
split; auto.
do 2 constructor.
Qed.

(* Transitivity property of reachable_through and ChainStep *)
Lemma reachable_through_trans' : forall from mid to,
  reachable_through from mid -> ChainStep mid to -> reachable_through from to.
Proof.
  intros * [reach [trace]] step.
  repeat (econstructor; eauto).
Qed.

(* Transitivity property of reachable_through *)
Lemma reachable_through_trans : forall from mid to,
  reachable_through from mid -> reachable_through mid to -> reachable_through from to.
Proof.
intros * [[trace_from] [trace_mid]] [_ [trace_to]].
do 2 constructor.
assumption.
eapply ChainedList.clist_app.
eauto.
eauto.
Qed.

(* Reachable_through can also be constructed from ChainStep instead of a
   ChainTrace since a ChainTrace can be constructed from a ChainStep *)
Lemma reachable_through_step : forall from to,
  reachable from -> ChainStep from to -> reachable_through from to.
Proof.
intros * reach_from step.
apply reachable_through_refl in reach_from.
eapply reachable_through_trans' ; eauto.
Qed.

(* Any ChainState that is reachable through another ChainState is reachable *)
Lemma reachable_through_reachable : forall from to,
  reachable_through from to -> reachable to.
Proof.
intros * [[trace_from] [trace_to]].
constructor.
eapply ChainedList.clist_app ; eauto.
Qed.

Hint Resolve reachable_through_refl
             reachable_through_trans'
             reachable_through_trans
             reachable_through_step
             reachable_through_reachable : core.

(* If a state has a contract deployed to some addr then any other state
    reachable through the first state must also have the same contract
    deployed to the same addr *)
Lemma reachable_through_contract_deployed : forall from to addr wc,
  reachable_through from to -> env_contracts from addr = Some wc ->
    env_contracts to addr = Some wc.
Proof.
intros * [reach [trace]] deployed.
induction trace as [ | from mid to trace IH step ].
- assumption.
- destruct_chain_step;
    only 2: destruct_action_eval;
    rewrite_environment_equiv; cbn;
    destruct_address_eq; subst; try easy ;eauto.
    
    now rewrite IH in not_deployed by assumption.
Qed.

(* If a state has a contract state on some addr then any other state
    reachable through the first state must also have the some contracts
    state on the same addr *)
Lemma reachable_through_contract_state : forall from to addr cstate,
  reachable_through from to -> env_contract_states from addr = Some cstate ->
    exists new_cstate, env_contract_states to addr = Some new_cstate.
Proof.
intros * [reachable [trace]] deployed_state.
generalize dependent cstate.
induction trace as [ | from mid to trace IH step ];
  intros cstate deployed_state.
- eexists. eauto.
- destruct_chain_step;
    only 2: destruct_action_eval;
    try rewrite_environment_equiv;
    try setoid_rewrite env_eq;
    cbn in *;
    destruct_address_eq; now eauto.
Qed.

(* If a state is reachable through another state then it cannot have a lower chain height *)
Lemma reachable_through_chain_height : forall from to,
  reachable_through from to -> from.(chain_height) <= to.(chain_height).
Proof.
intros * [reachable [trace]].
induction trace as [ | from mid to trace IH step ].
- apply Nat.le_refl.
- destruct_chain_step;
  try destruct_action_eval;
  rewrite_environment_equiv; cbn; auto.
  + inversion valid_header. cbn in *. eapply IH in reachable. 
  lia.
Qed.

(* If a state is reachable through another state then it cannot have a lower current slot *)
Lemma reachable_through_current_slot : forall from to,
  reachable_through from to -> from.(current_slot) <= to.(current_slot).
Proof.
intros * [reachable [trace]].
induction trace as [ | from mid to trace IH step ].
- apply Nat.le_refl.
- destruct_chain_step;
  try destruct_action_eval;
  rewrite_environment_equiv; cbn; auto.
  + inversion valid_header. cbn in *. eapply IH in reachable. 
  lia.
Qed.

(* If a state is reachable through another state then it cannot have a lower finalized height *)
Lemma reachable_through_finalized_height : forall from to,
  reachable_through from to -> from.(finalized_height) <= to.(finalized_height).
Proof.
intros * [reachable [trace]].
induction trace as [ | from mid to trace IH step ].
- apply le_refl.
- destruct_chain_step;
  try destruct_action_eval;
  rewrite_environment_equiv; cbn; auto.
  + inversion valid_header. cbn in *. eapply IH in reachable. 
  lia.
Qed.

(* Initial contract balance will always be positive in reachable states *)
Lemma deployment_amount_nonnegative : forall {Setup : Type} `{Serializable Setup}
                                      bstate caddr dep_info
                                      (trace : ChainTrace empty_state bstate),
  deployment_info Setup trace caddr = Some dep_info ->
  (0 <= dep_info.(deployment_amount))%Z.
Proof.
intros * deployment_info_some.
remember empty_state.
induction trace; subst.
- discriminate.
- destruct_chain_step; auto.
  destruct_action_eval; auto.
  cbn in deployment_info_some.
  destruct_address_eq; auto.
  destruct_match in deployment_info_some;
    try congruence.
  inversion_clear deployment_info_some.
  now apply Z.ge_le.
Qed.

Definition receiver_can_receive_transfer (bstate : ChainState) act_body :=
  match act_body with
  | act_transfer to _ => address_is_contract to = false \/
    (exists wc state,
      env_contracts bstate to = Some wc /\
      env_contract_states bstate to = Some state /\
      forall (bstate_new : ChainState) ctx, exists new_state, wc_receive wc bstate_new ctx state None = Ok (new_state, []))
  | _ => True
  end.

(* This axiom states that for any reachable state and any contract it is
    decidable wether or there is an address where the contract can be deployed to.
   This is not provable in general with the assumption ChainBase makes about
    addresses and the function address_is_contract. However this should be
    provable in any sensible instance of ChainBase *)
Axiom deployable_address_decidable : forall bstate wc setup act_origin act_from amount,
  reachable bstate ->
  decidable (exists addr state, address_is_contract addr = true
            /\ env_contracts bstate addr = None
            /\ wc_init wc
                  (transfer_balance act_from addr amount bstate)
                  (build_ctx act_origin act_from addr amount amount)
                  setup = Ok state).

Ltac action_not_decidable :=
  right; intro;
  match goal with
  | H : exists bstate new_acts, inhabited (ActionEvaluation _ _ bstate new_acts) |- False =>
    destruct H as [bstate_new [new_acts [action_evaluation]]];
    destruct_action_eval; try congruence
  end; repeat
  match goal with
  | H : {| act_origin := _; act_from := _; act_body := _ |} = {| act_origin := _; act_from := _; act_body := match ?msg with | Some _ => _ | None =>_ end |} |- False =>
    destruct msg
  | H : {| act_origin := _; act_from := _; act_body := _ |} = {| act_origin := _; act_from := _; act_body := _ |} |- False =>
    inversion H; subst; clear H
  end.

Ltac action_decidable :=
  left; do 2 eexists; constructor;
  match goal with
  | H : wc_receive _ _ _ _ ?m = Ok _ |- _ => eapply (eval_call _ _ _ _ _ m)
  | H : wc_init _ _ _ _ = Ok _ |- _ => eapply eval_deploy
  | H : context [act_transfer _ _] |- _ => eapply eval_transfer
  end;
  eauto; try now constructor.

Ltac rewrite_balance :=
  match goal with
  | H := context [if (_ =? ?to)%address then _ else _ ],
    H2 : Environment |- _ =>
    assert (new_to_balance_eq : env_account_balances H2 to = H);
    [ try rewrite_environment_equiv; cbn; unfold H; destruct_address_eq; try congruence; lia |
    now rewrite <- new_to_balance_eq in *]
  end.


  (* For any reachable state and an action it is decidable if it is
    possible to evaluate the action in the state *)
Open Scope Z_scope.
Lemma action_evaluation_decidable : forall bstate act,
  reachable bstate ->
  decidable (exists bstate' new_acts, inhabited (ActionEvaluation bstate act bstate' new_acts)).
Proof.
(* intros * reach.
  destruct act eqn:Hact.
  destruct act_body;
    (destruct (amount >=? 0) eqn:amount_positive;
    [destruct (amount <=? env_account_balances bstate act_from) eqn:balance |
      action_not_decidable; now rewrite Z.geb_leb, Z.leb_gt in amount_positive (* Eliminate cases where amount is negative *)];
    [| action_not_decidable; rewrite Z.leb_gt in balance;eauto ]); (* Eliminate cases where sender does not have enough balance *)
  try (destruct (address_is_contract to) eqn:to_is_contract;
    [destruct (env_contracts bstate to) eqn:to_contract;
    [destruct (env_contract_states bstate to) eqn:contract_state |] |]);
  try now action_not_decidable. (* Eliminate cases with obvious contradictions *)
  all : rewrite Z.geb_leb, <- Zge_is_le_bool in amount_positive.
  all : try rewrite Z.leb_le in balance.
  - (* act_body = act_transfer to amount *)
    pose (new_to_balance := if (address_eqb act_from to)
                         then (env_account_balances bstate to)
                         else (env_account_balances bstate to) + amount).
    destruct (wc_receive w
        (transfer_balance act_from to amount bstate)
        (build_ctx act_origin act_from to new_to_balance amount)
        s None) eqn:receive.
    + (* Case: act_transfer is evaluable by eval_call *)
    destruct t.
    pose (bstate' := (set_contract_state to s0
                     (transfer_balance act_from to amount bstate))).
    action_decidable.
    assert (new_to_balance_eq : env_account_balances bstate' to = new_to_balance).
    { cbn; unfold new_to_balance; destruct_address_eq; try congruence; lia.
    } simpl.
    cbn in *.
    rewrite new_to_balance_eq. eauto.

    + (* Case: act_transfer is not evaluable by eval_call
          because wc_receive returned None *)

          action_not_decidable.
          assert (new_to_balance_eq : env_account_balances bstate_new to_addr = new_to_balance).
          { try rewrite_environment_equiv; cbn; unfold new_to_balance; destruct_address_eq; try congruence; lia .
      }

      rewrite <- new_to_balance_eq in *. congruence.

  - (* act_body = act_transfer to amount *)
    (* Case: act_transfer is evaluable by eval_transfer *)
    pose (bstate' := (transfer_balance act_from to amount bstate)).
    action_decidable.
    erewrite to_contract in contract_state.
    
  - (* act_body = act_call to amount msg *)
    pose (new_to_balance := if (address_eqb act_from to)
                         then (env_account_balances bstate to)
                         else (env_account_balances bstate to) + amount).
    destruct (wc_receive w
        (transfer_balance act_from to amount bstate)
        (build_ctx act_origin act_from to new_to_balance amount)
        s (Some msg)) eqn:receive.
    + (* Case: act_call is evaluable by eval_call *)
      destruct p.
      pose (bstate' := (set_contract_state to s0
                       (transfer_balance act_from to amount bstate))).
      action_decidable.
      rewrite_balance.
    + (* Case: act_call is not evaluable by eval_call
          because wc_receive returned None *)
      action_not_decidable.
      rewrite_balance.
  - (* act_body = act_call to amount msg *)
    (* Case: contradiction *)
    action_not_decidable.
    now apply contract_addr_format in deployed; auto.
  - (* act_body = act_deploy amount c setup *)
    apply deployable_address_decidable
      with (wc:=c) (setup:=setup) (act_origin:=act_origin)
      (act_from:=act_from) (amount:=amount)
      in reach.
    destruct reach as [[to [state [to_is_contract_addr [to_not_deployed init]]]] | no_deployable_addr].
    + (* Case: act_deploy is evaluable by eval_deploy *)
      pose (bstate' := (set_contract_state to state
                       (add_contract to c
                       (transfer_balance act_from to amount bstate)))).
      action_decidable.
    + (* Case: act_deploy is not evaluable by eval_deploy
          because no there is no available contract address
          that this contract can be deployed to *)
      action_not_decidable.
      apply no_deployable_addr.
      eauto. *)
Admitted.
Close Scope Z_scope.

(* Property stating that an action does not produce any new action when evaluated *)
Definition produces_no_new_acts act : Prop :=
  forall bstate bstate' new_acts, ActionEvaluation bstate act bstate' new_acts -> new_acts = [].

(* Property on a ChainState queue stating all actions are from accounts and produces
    no new actions when evaluated. This ensures that the queue can be emptied successfully *)
Definition emptyable queue : Prop :=
  Forall act_is_from_account queue /\
  Forall produces_no_new_acts queue.

(* An empty queue is always emptyable *)
Lemma empty_queue_is_emptyable : emptyable [].
Proof.
  now constructor.
Qed.

(* A subset of a emptyable queu is also emptyable *)
Lemma emptyable_cons : forall x l,
  emptyable (x :: l) -> emptyable l.
Proof.
  intros * [acts_from_account no_new_acts].
  apply Forall_inv_tail in acts_from_account.
  now apply Forall_inv_tail in no_new_acts.
Qed.

(* For any reachable state it is possible to empty the chain_state_queue
    if the queue only contains action that satisfy the following
    1) the action is from a user and not a contract
    2) the action does not produce any actions when evaluated
   For any property that holds on the starting state this also hold on
    the state with an empty queue if it can be proven that the property
    holds after evaluating any action.
*)

(* wc_receive and contract receive are equivalent *)
Lemma wc_receive_to_receive : forall {Setup Msg State Error : Type}
                                    `{Serializable Setup}
                                    `{Serializable Msg}
                                    `{Serializable State}
                                    `{Serializable Error}
                                    (contract : Contract Setup Msg State Error)
                                    chain cctx cstate msg new_cstate new_acts,
  contract.(receive) chain cctx cstate (Some msg) = Ok (new_cstate, new_acts) <->
  wc_receive contract chain cctx ((@serialize State _) cstate) (Some ((@serialize Msg _) msg)) = Ok ((@serialize State _) new_cstate, new_acts).
Proof.
  split; intros receive_some.
  - cbn.
    rewrite !deserialize_serialize.
    cbn.
    now rewrite receive_some.
  - apply wc_receive_strong in receive_some as
      (prev_state' & msg' & new_state' & prev_state_eq & msg_eq & new_state_eq & receive_some).
    apply serialize_injective in new_state_eq. subst.
    rewrite deserialize_serialize in prev_state_eq.
    inversion prev_state_eq. subst.
    destruct msg' eqn:Hmsg.
    + cbn in msg_eq.
      rewrite deserialize_serialize in msg_eq; eauto; try congruence.
    + inversion msg_eq.
Qed.

(* wc_init and contract init are equivalent *)
Lemma wc_init_to_init : forall {Setup Msg State Error : Type}
                               `{Serializable Setup}
                               `{Serializable Msg}
                               `{Serializable State}
                               `{Serializable Error}
                               (contract : Contract Setup Msg State Error)
                               chain cctx cstate setup,
  contract.(init) chain cctx setup = Ok cstate <->
  wc_init contract chain cctx ((@serialize Setup _) setup) = Ok ((@serialize State _) cstate).
Proof.
  split; intros init_some.
  - cbn.
    rewrite deserialize_serialize.
    cbn.
    now rewrite init_some.
  - apply wc_init_strong in init_some as
      (setup_strong & result_strong & serialize_setup & serialize_result & init_some).
    apply serialize_injective in serialize_result. subst.
    rewrite deserialize_serialize in serialize_setup.
    now inversion serialize_setup.
Qed.

Open Scope Z_scope.
(* Lemma showing that there exists a future ChainState with an added block *)
Lemma add_block : forall bstate reward creator acts slot_incr,
  reachable bstate ->
  chain_state_queue bstate = [] ->
  address_is_contract creator = false ->
  reward >= 0->
  (slot_incr > 0)%nat ->
  Forall act_is_from_account acts ->
  Forall act_origin_is_eq_from acts ->
    (exists bstate',
       reachable_through bstate bstate'
    /\ chain_state_queue bstate' = acts
    /\ EnvironmentEquiv
        bstate'
        (add_new_block_to_env {| block_height := S (chain_height bstate);
          block_slot := current_slot bstate + slot_incr;
          block_finalized_height := finalized_height bstate;
          block_creator := creator;
          block_reward := reward; |} bstate)).
Proof.
  intros * reach queue creator_not_contract
    reward_positive slot_incr_positive
    acts_from_accounts origins_from_accounts.
  pose (header :=
    {| block_height := S (chain_height bstate);
       block_slot := current_slot bstate + slot_incr;
       block_finalized_height := finalized_height bstate;
       block_creator := creator;
       block_reward := reward; |}).
  pose (bstate_with_acts := (bstate<|chain_state_queue := acts|>
                                   <|chain_state_env := add_new_block_to_env header bstate|>)).
  assert (step_with_acts : ChainStep bstate bstate_with_acts).
  { eapply step_block; try easy.
    - constructor; try easy.
      + cbn. lia.
      + try (cbn; lia).
        
  }
  exists bstate_with_acts.
  split; eauto.
  split; eauto.
  constructor; try reflexivity.
Qed.

(* Lemma showing that there exists a future ChainState with the
    same contract states where the current slot is <slot> *)
Lemma forward_time_exact : forall bstate reward creator slot,
  reachable bstate ->
  chain_state_queue bstate = [] ->
  address_is_contract creator = false ->
  reward >= 0 ->
  (current_slot bstate < slot)%nat ->
    (exists bstate' header,
       reachable_through bstate bstate'
    /\ IsValidNextBlock header bstate
    /\ (slot = current_slot bstate')%nat
    /\ chain_state_queue bstate' = []
    /\ EnvironmentEquiv
        bstate'
        (add_new_block_to_env header bstate)).
Proof.
  intros bstate reward creator slot reach queue
    creator_not_contract reward_positive slot_not_hit.
  eapply add_block with (slot_incr := (slot - current_slot bstate)%nat) in reach as new_block; try easy.
  destruct new_block as [bstate_with_act [reach' [queue' env_eq]]].
  do 2 eexists.
  split; eauto.
  do 3 try split; only 8: apply env_eq; eauto; cbn; try lia.
  - rewrite_environment_equiv. cbn. lia.
  - eauto.
  - eauto.
  - lia. 
Qed.

(* Lemma showing that there exists a future ChainState with the
    same contract states where the current slot is at least <slot> *)
Lemma forward_time : forall bstate reward creator slot,
  reachable bstate ->
  chain_state_queue bstate = [] ->
  address_is_contract creator = false ->
  reward >= 0 ->
    (exists bstate' header,
       reachable_through bstate bstate'
    /\ IsValidNextBlock header bstate
    /\ (slot <= current_slot bstate')%nat
    /\ chain_state_queue bstate' = []
    /\ EnvironmentEquiv
        bstate'
        (add_new_block_to_env header bstate)).
Proof.
  intros * reach queue creator_not_contract reward_positive.
  destruct (slot - current_slot bstate)%nat eqn:slot_hit.
  - eapply add_block with (slot_incr := 1%nat) in reach as new_block; try easy.
    destruct new_block as [bstate_with_act [reach' [queue' env_eq]]].
    do 2 eexists.
    split; eauto.
    do 3 try split; only 8: apply env_eq; eauto; cbn; try lia.
    + apply NPeano.Nat.sub_0_le in slot_hit.
      rewrite_environment_equiv. cbn. lia.
    + eauto.
    + eauto.
    + lia.
  - specialize forward_time_exact with (slot := slot) as
      (bstate' & header & reach' & header_valid & slot_hit' & queue' & env_eq);
      try easy;eauto.
      lia.
    do 2 eexists.
    split; eauto.
    intuition.
    eauto.
    eauto.
Qed.

(* Lemma showing that there exists a future ChainState
    where the contract call is evaluated *)
Lemma evaluate_action : forall {Setup Msg State Error : Type}
                              `{Serializable Setup}
                              `{Serializable Msg}
                              `{Serializable State}
                              `{Serializable Error}
                               (contract : Contract Setup Msg State Error)
                               bstate origin from caddr amount msg acts new_acts
                               cstate new_cstate,
  reachable bstate ->
  chain_state_queue bstate = {| act_from := from;
                                act_origin := origin;
                                act_body := act_call caddr amount ((@serialize Msg _) msg) |} :: acts ->
  amount >= 0 ->
  env_account_balances bstate from >= amount ->
  env_contracts bstate caddr = Some (contract : WeakContract) ->
  env_contract_states bstate caddr = Some ((@serialize State _) cstate) ->
  Blockchain.receive contract (transfer_balance from caddr amount bstate)
                     (build_ctx origin from caddr (if (address_eqb from caddr)
                         then (env_account_balances bstate caddr)
                         else (env_account_balances bstate caddr) + amount) amount)
                     cstate (Some msg) = Ok (new_cstate, new_acts) ->
    (exists bstate',
       reachable_through bstate bstate'
    /\ env_contract_states bstate' caddr = Some ((@serialize State _) new_cstate)
    /\ chain_state_queue bstate' = (map (build_act origin caddr) new_acts) ++ acts
    /\ EnvironmentEquiv
        bstate'
        (set_contract_state caddr ((@serialize State _) new_cstate) (transfer_balance from caddr amount bstate))).
Proof.
  intros * reach queue amount_nonnegative enough_balance%Z.ge_le
    deployed deployed_state receive_some.
  pose (new_to_balance := if (address_eqb from caddr)
                         then (env_account_balances bstate caddr)
                         else (env_account_balances bstate caddr) + amount).
  pose (bstate' := (bstate<|chain_state_queue := (map (build_act origin caddr) new_acts) ++ acts|>
                          <|chain_state_env := set_contract_state caddr ((@serialize State _) new_cstate)
                                                  (transfer_balance from caddr amount bstate)|>)).
  assert (new_to_balance_eq : env_account_balances bstate' caddr = new_to_balance) by
   (cbn; destruct_address_eq; eauto;try congruence;try lia;try tauto).
  assert (step : ChainStep bstate bstate').
  - eapply step_action; eauto.
    eapply eval_call with (msg := Some ((@serialize Msg _) msg)); eauto.
    + rewrite new_to_balance_eq.
       apply wc_receive_to_receive in receive_some;eauto.
    + constructor; reflexivity.
  - exists bstate'.
    split; eauto.
    repeat split; eauto.
    cbn.
    now destruct_address_eq.
Qed.

(* Lemma showing that there exists a future ChainState
    where the transfer action is evaluated *)
Lemma evaluate_transfer : forall bstate origin from to amount acts,
  reachable bstate ->
  chain_state_queue bstate = {| act_from := from;
                                act_origin := origin;
                                act_body := act_transfer to amount |} :: acts ->
  amount >= 0 ->
  env_account_balances bstate from >= amount ->
  address_is_contract to = false ->
    (exists bstate',
       reachable_through bstate bstate'
    /\ chain_state_queue bstate' = acts
    /\ EnvironmentEquiv
        bstate'
        (transfer_balance from to amount bstate)).
Proof.
  intros * reach queue amount_nonnegative enough_balance%Z.ge_le to_not_contract.
  pose (bstate' := (bstate<|chain_state_queue := acts|>
                          <|chain_state_env := (transfer_balance from to amount bstate)|>)).
  assert (step : ChainStep bstate bstate').
  - eapply step_action with (new_acts := []); eauto.
    eapply eval_transfer; eauto.
    constructor; reflexivity.
  - eexists bstate'.
    split; eauto.
    repeat split; eauto.
Qed.





(* Lemma showing that there exists a future ChainState
    where the contract is deployed *)
Lemma deploy_contract : forall {Setup Msg State Error : Type}
                              `{Serializable Setup}
                              `{Serializable Msg}
                              `{Serializable State}
                              `{Serializable Error}
                               (contract : Contract Setup Msg State Error)
                               bstate origin from caddr amount acts setup cstate,
  reachable bstate ->
  chain_state_queue bstate = {| act_from := from;
                                act_origin := origin;
                                act_body := act_deploy amount contract ((@serialize Setup _) setup) |} :: acts ->
  amount >= 0 ->
  env_account_balances bstate from >= amount ->
  address_is_contract caddr = true ->
  env_contracts bstate caddr = None ->
  Blockchain.init contract
        (transfer_balance from caddr amount bstate)
        (build_ctx origin from caddr amount amount)
        setup = Ok cstate ->
    (exists bstate' (trace : ChainTrace empty_state bstate'),
       reachable_through bstate bstate'
    /\ env_contracts bstate' caddr = Some (contract : WeakContract)
    /\ env_contract_states bstate' caddr = Some ((@serialize State _) cstate)
    /\ deployment_info Setup trace caddr = Some (build_deployment_info origin from amount setup)
    /\ chain_state_queue bstate' = acts
    /\ EnvironmentEquiv
        bstate'
        (set_contract_state caddr ((@serialize State _) cstate)
        (add_contract caddr contract
        (transfer_balance from caddr amount bstate)))).
Proof.
  intros * reach queue amount_nonnegative enough_balance%Z.ge_le
    caddr_is_contract not_deployed init_some.
  pose (bstate' := (bstate<|chain_state_queue := acts|>
                          <|chain_state_env :=
                            (set_contract_state caddr ((@serialize State _) cstate)
                            (add_contract caddr contract
                            (transfer_balance from caddr amount bstate)))|>)).
  assert (step : ChainStep bstate bstate').
  - eapply step_action with (new_acts := []); eauto.
    eapply eval_deploy; eauto.
    + apply wc_init_to_init in init_some;eauto.
    + constructor; reflexivity.
  - exists bstate'.
    destruct reach as [trace].
    exists (ChainedList.snoc trace step).
    split; eauto.
    repeat split; eauto;
    try (cbn; now destruct_address_eq).
    cbn. destruct_chain_step; try congruence.
    + destruct_action_eval;
        try congruence; cbn in *; subst; rewrite queue in queue_prev; inversion queue_prev; subst.
      * destruct_address_eq.
        -- now rewrite deserialize_serialize.
        -- inversion env_eq.
           cbn in contracts_eq.
           specialize (contracts_eq caddr).
            rewrite address_eq_refl, address_eq_ne in contracts_eq;eauto.
            congruence.
      * destruct msg;eauto;try lia;try tauto;try congruence.
Qed.
Close Scope Z_scope.

Lemma step_reachable_through_exists : forall from mid (P : ChainState -> Prop),
  reachable_through from mid ->
  (exists to : ChainState, reachable_through mid to /\ P to) ->
  (exists to : ChainState, reachable_through from to /\ P to).
Proof.
  intros * reach [to [reach_ HP]].
   exists to; eauto.
Qed.

End BuildUtils.

Global Hint Resolve reachable_through_refl
             reachable_through_trans'
             reachable_through_trans
             reachable_through_step
             reachable_through_reachable : core.

Global Hint Resolve reachable_through_refl
             reachable_through_trans'
             reachable_through_trans
             reachable_through_step
             reachable_through_reachable : core.

Local Ltac update_fix term1 term2 H H_orig H' :=
  match H with
  | context G [ term1 ] =>
    let x := context G [ term2 ] in
      update_fix term1 term2 x H_orig H'
  | _ =>
    let h := fresh "H" in
      assert H; [H' | clear H_orig; rename h into H_orig]
  end.

(* Replaces all occurrences of <term1> with <term2> in hypothesis <H>
    using tactic <H'> to prove the old hypothesis implies the updated *)
Local Ltac update_ term1 term2 H H' :=
  match type of H with
  | context G [ term1 ] =>
    let x := context G [ term2 ] in
      update_fix term1 term2 x H H'
  end.

Tactic Notation "update" constr(t1) "with" constr(t2) "in" hyp(H) := update_ t1 t2 H ltac:(try (cbn; easy)).
Tactic Notation "update" constr(t1) "with" constr(t2) "in" hyp(H) "by" tactic(G) := update_ t1 t2 H G.
Tactic Notation "update" constr(t2) "in" hyp(H) := let t1 := type of H in update_ t1 t2 H ltac:(try (cbn; easy)).
Tactic Notation "update" constr(t2) "in" hyp(H) "by" tactic(G) := let t1 := type of H in update_ t1 t2 H G.

Local Ltac only_on_match tac :=
  match goal with
  | |- exists bstate', reachable_through ?bstate bstate' /\ _ => tac
  | |- _ => idtac
  end.

Local Ltac update_chainstate bstate1 bstate2 :=
  match goal with
  | H : reachable bstate1 |- _ => clear H
  | H : chain_state_queue bstate1 = _ |- _ => clear H
  | H : IsValidNextBlock _ bstate1.(chain_state_env).(env_chain) |- _ => clear H
  | H : reachable_through bstate1 bstate2 |- _ =>
      update (reachable bstate2) in H
  | H : env_contracts bstate1.(chain_state_env) _ = Some _ |- _ =>
      update bstate1 with bstate2 in H by (now rewrite_environment_equiv)
  | H : env_contract_states bstate1.(chain_state_env) _ = Some _ |- _ =>
      update bstate1 with bstate2 in H by (now rewrite_environment_equiv)
  | H : context [ bstate1 ] |- _ =>
    match type of H with
    | EnvironmentEquiv _ _ => fail 1
    | _ => update bstate1 with bstate2 in H by (try (rewrite_environment_equiv; cbn; easy))
    end
  end;
  only_on_match ltac:(progress update_chainstate bstate1 bstate2).

(* Tactic for updating goal and all occurences of an old ChainState
    after adding a future ChainState to the environment. *)
Ltac update_all :=
  match goal with
  | Hreach : reachable_through ?bstate1 ?bstate2,
    Henv_eq : EnvironmentEquiv ?bstate2.(chain_state_env) (add_new_block_to_env ?header ?bstate1.(chain_state_env)) |-
    exists bstate3, reachable_through ?bstate1 bstate3 /\ _ =>
      apply (step_reachable_through_exists bstate1 bstate2); auto;
      update_chainstate bstate1 bstate2;
      only_on_match ltac:(
        clear Henv_eq;
        (try clear dependent header);
        clear dependent bstate1)
  | Hreach : reachable_through ?bstate1 ?bstate2,
    Henv_eq : EnvironmentEquiv ?bstate2.(chain_state_env) _ |-
    exists bstate3, reachable_through ?bstate1 bstate3 /\ _ =>
      apply (step_reachable_through_exists bstate1 bstate2); auto;
      update_chainstate bstate1 bstate2;
      only_on_match ltac:(
        clear Henv_eq;
        clear dependent bstate1)
  | Hreach : reachable_through ?bstate1 ?bstate2 |-
    exists bstate3, reachable_through ?bstate1 bstate3 /\ _ =>
      apply (step_reachable_through_exists bstate1 bstate2); auto;
      update (reachable bstate2) in Hreach;
      only_on_match ltac:(clear dependent bstate1)
  end.

Ltac forward_time slot_ :=
  let new_bstate := fresh "bstate" in
  let new_header := fresh "header" in
  let new_header_valid := fresh "header_valid" in
  let new_reach := fresh "reach" in
  let new_queue := fresh "queue" in
  let new_env_eq := fresh "env_eq" in
  let new_slot_hit := fresh "slot_hit" in
  match goal with
  | Hqueue : (chain_state_queue ?bstate) = [],
    Hreach : reachable ?bstate |-
    exists bstate', reachable_through ?bstate bstate' /\ _ =>
      specialize (forward_time bstate) with (slot := slot_)
        as [new_bstate [new_header [new_reach [new_header_valid [new_slot_hit [new_queue new_env_eq]]]]]]
  end.

Ltac forward_time_exact slot_ :=
  let new_bstate := fresh "bstate" in
  let new_header := fresh "header" in
  let new_header_valid := fresh "header_valid" in
  let new_reach := fresh "reach" in
  let new_queue := fresh "queue" in
  let new_env_eq := fresh "env_eq" in
  let new_slot_hit := fresh "slot_hit" in
  match goal with
  | Hqueue : (chain_state_queue ?bstate) = [],
    Hreach : reachable ?bstate |-
    exists bstate', reachable_through ?bstate bstate' /\ _ =>
      specialize (forward_time_exact bstate) with (slot := slot_)
        as [new_bstate [new_header [new_reach [new_header_valid [new_slot_hit [new_queue new_env_eq]]]]]]
  end.

Ltac add_block acts_ slot_ :=
  let new_bstate := fresh "bstate" in
  let new_reach := fresh "reach" in
  let new_queue := fresh "queue" in
  let new_env_eq := fresh "env_eq" in
  match goal with
  | Hqueue : (chain_state_queue ?bstate) = [],
    Hreach : reachable ?bstate |-
    exists bstate', reachable_through ?bstate bstate' /\ _ =>
      specialize add_block with (acts := acts_) (slot_incr := slot_)
        as [new_bstate [new_reach [new_queue new_env_eq]]];
      [apply Hreach | apply Hqueue| | | | | |]
  end.

Ltac evaluate_action contract_ :=
  let new_bstate := fresh "bstate" in
  let new_reach := fresh "reach" in
  let new_deployed_state := fresh "deployed_state" in
  let new_queue := fresh "queue" in
  let new_env_eq := fresh "env_eq" in
  match goal with
  | Hqueue : (chain_state_queue ?bstate) = _,
    Hreach : reachable ?bstate |-
    exists bstate', reachable_through ?bstate bstate' /\ _ =>
      specialize (evaluate_action contract_) as
        [new_bstate [new_reach [new_deployed_state [new_queue new_env_eq]]]];
      [apply Hreach | rewrite Hqueue | | | | | | ]
  end.

Ltac evaluate_transfer :=
  let new_bstate := fresh "bstate" in
  let new_reach := fresh "reach" in
  let new_queue := fresh "queue" in
  let new_env_eq := fresh "env_eq" in
  match goal with
  | Hqueue : (chain_state_queue ?bstate) = _,
    Hreach : reachable ?bstate |-
    exists bstate', reachable_through ?bstate bstate' /\ _ =>
      specialize evaluate_transfer as
        [new_bstate [new_reach [new_queue new_env_eq]]];
      [apply Hreach | rewrite Hqueue | | | | ]
  end.




  Ltac deploy_contract contract_ :=
    let new_bstate := fresh "bstate" in
    let new_reach := fresh "reach" in
    let new_deployed_state := fresh "deployed_state" in
    let new_contract_deployed := fresh "contract_deployed" in
    let new_queue := fresh "queue" in
    let new_env_eq := fresh "env_eq" in
    let new_cstate := fresh "cstate" in
    let contract_not_deployed := fresh "trace" in
    let deploy_info := fresh "deploy_info" in
    match goal with
    | Hqueue : (chain_state_queue ?bstate) = _,
      Hreach : reachable ?bstate,
      Haddress : address_is_contract ?caddr = true,
      Hdeployed : env_contracts ?bstate.(chain_state_env) ?caddr = None |-
      exists bstate', reachable_through ?bstate bstate' /\ _ =>
        specialize (deploy_contract contract_) as
          (new_bstate & trace & new_reach & new_contract_deployed &
            new_deployed_state & deploy_info & new_queue & new_env_eq);
        [apply Hreach | rewrite Hqueue | | |
         apply Haddress | apply Hdeployed | |
         clear Haddress Hdeployed;
         match type of new_deployed_state with
         | env_contract_states _ _ = Some ((@serialize _ _) ?state) => remember state as new_cstate
         end
         ]
    end.




