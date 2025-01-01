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
From Coq Require Import List.
From Coq Require Import Bool.
From Coq Require Import ZArith.
From Coq Require Import Arith.
From Coq Require Import String.
From Coq Require Import Lia.
Import RecordSetNotations.
From Coq Require Import Permutation.
Import ListNotations.


Ltac decompose_exists :=
  repeat match goal with
          | [ H : exists _, _ |- _ ] =>
              let x := fresh "x" in
              destruct H as [x H]
          end.
  Ltac decompose_wellDefinedSystem H :=
    match type of H with
    | wellDefinedSystem ?delta_usr ?addrs_usr ?delta_env ?addrs_env ?caddr ?c ?s0 =>
        unfold wellDefinedSystem in H;
        let H_usr_strat := fresh "H_usr_strat" in
        let H_env_strat := fresh "H_env_strat" in
        let H_finite := fresh "H_finite" in
        let H_init := fresh "H_init" in
        destruct H as [H_usr_strat [H_env_strat [H_finite H_init]]]
    | _ => fail "The hypothesis" H "is not of the form wellDefinedSystem."
    end.


  Ltac decompose_wellStrat H :=
    unfold wellStrat in H;
    let Hs0 := fresh "Hs0" in
    let Hs := fresh "Hs" in
    let Htr_s := fresh "Htr_s" in
    intros Hs0 Hs Htr_s;
    match type of H with
    | context[let delta_actions := ?delta _ _ _ _ in _] =>
        let Hda := fresh "Hda" in
        set (delta_actions := delta _ _ _ _) in H;
        unfold delta_actions in H
    | _ => idtac
    end;
    match type of H with
    | _ -> Forall _ _ =>
        let Hq := fresh "Hq" in
        intros Hq; specialize (H Hq)
    | Forall _ ?l =>
        let Ha := fresh "Ha" in
        apply Forall_forall in H; intros Ha
    | _ => idtac
    end.

Ltac decompose_transition_reachable H :=
  unfold transition_reachable in H;
  destruct H as [init_bstate [trace]].



  Ltac decompose_reachable_via H :=
    match type of H with
    | reachable_via ?contract ?caddr ?s0 ?mid ?to =>
        unfold reachable_via in H;
        let H_reachable := fresh "H_reachable" in
        let tr := fresh "tr" in
        destruct H as [H_reachable H_trace];
        destruct H_trace as [tr] (* 只引入轨迹变量 tr，避免未使用的附加绑定 *)
    | _ => fail "The hypothesis" H "is not of the form reachable_via contract caddr s0 mid to."
    end.

  Ltac decompose_is_init_state H :=
    match type of H with
    | is_init_state ?contract ?caddr ?init_state =>
        unfold is_init_state in H;
        let H_reachable := fresh "H_reachable" in
        let H_queue := fresh "H_queue" in
        let H_env_contracts := fresh "H_env_contracts" in
        let H_env_details := fresh "H_env_details" in
        destruct H as [H_reachable [H_queue [H_env_contracts H_env_details]]];
        let ctx := fresh "ctx" in
        let setup := fresh "setup" in
        let state := fresh "state" in
        let H_env_states := fresh "H_env_states" in
        let H_init := fresh "H_init" in
        destruct H_env_details as [ctx [setup [state [H_env_states H_init]]]]
    | _ => fail "The hypothesis" H "is not of the form is_init_state contract caddr init_state."
    end.



Ltac decompose_stratDrive H :=
  match type of H with
  | stratDrive ?s0 ?delta ?addrs ?s ?tr ?s' ?tr' =>
      unfold stratDrive in H;
      let a := fresh "a" in
      let H_trans := fresh "H_transition" in
      destruct H as [a [H_trans [H_in H_trace]]]
  | _ => fail "The hypothesis" H "is not of the form stratDrive s0 delta addrs s tr s' tr'."
  end.



Ltac decompose_transition H :=
  unfold transition in H;
  repeat match type of H with
  | context[if ?cond then _ else _] =>
      let Hcond := fresh "Hcond" in
      destruct cond eqn:Hcond; try congruence
  | context[match get_wait_time ?act with | Ok _ => _ | Err _ => _ end] =>
      let Hres := fresh "Hres" in
      destruct (get_wait_time act) eqn:Hres; try congruence
  | context[match add_block_exec ?mode ?state ?header ?acts with | Ok _ => _ | Err _ => _ end] =>
      let Hexec := fresh "Hexec" in
      destruct (add_block_exec mode state header acts) eqn:Hexec; try congruence
  end;
  repeat match type of H with
  | Ok _ = Ok _ => inversion H; subst; clear H
  | Err _ = Err _ => inversion H; subst; clear H
  end.


    Lemma transition_reachable_init_state c s0 :
    is_init_state c caddr s0 ->
    transition_reachable c caddr s0 s0.
  Proof.
    intros.
    unfold transition_reachable.
    split.
    eauto.
    econstructor.
    eapply clnil.
  Qed.


  Lemma transition_reachable_trans c s0 s s' :
    transition_reachable c caddr s0 s -> 
    TransitionTrace s s' -> 
    transition_reachable c caddr s0 s'.
  Proof.
    intros H_reachable H_trace.
    decompose_transition_reachable H_reachable.
    unfold transition_reachable in *.
    eauto.
    econstructor;eauto.
    econstructor;eauto.
    eapply clist_app;eauto.
  Qed.

  (* Transitivity property of reachable and ChainStep *)
  Lemma transition_reachable_step s0 c from to :
    transition_reachable c caddr s0 from -> 
    TransitionStep from to -> 
    transition_reachable c caddr s0 to.
  Proof.
    intros H_reachable H_step.
    decompose_transition_reachable H_reachable.
    unfold transition_reachable .
    split.
    eauto.
    econstructor;eauto.
    eapply (snoc trace H_step).
  Qed.

  Hint Resolve transition_reachable_init_state
                transition_reachable_trans
                transition_reachable_step : core.

  Lemma reachable_via_refl : forall c caddr s0 s,
    transition_reachable c caddr s0 s -> reachable_via c caddr s0 s s.
  Proof.
    intros.
    decompose_transition_reachable H3.
    repeat (econstructor; eauto).
  Qed.

  Lemma reachable_via_trans' : 
    forall c caddr init from mid to,
      reachable_via c caddr init from mid -> 
      TransitionStep mid to -> 
      reachable_via c caddr init from to.
  Proof.
    intros * [reach [trace]] step.
    repeat (econstructor; eauto).
  Qed.

  Lemma reachable_via_trans : 
    forall c caddr init from mid to,
      reachable_via c caddr init from mid -> 
      reachable_via c caddr init mid to -> 
      reachable_via c caddr init from to.
  Proof.
    intros.
    decompose_reachable_via H3.
    decompose_reachable_via H4.
    unfold reachable_via.
    split.
    eauto.
    econstructor;eauto.
    eapply ChainedList.clist_app;eauto.
  Qed.


  Lemma reachable_via_step : 
    forall c caddr init from to,
      transition_reachable c caddr init from -> 
      TransitionStep from to -> 
      reachable_via c caddr init from to.
  Proof.
    intros * reach_from step.
    apply reachable_via_refl in reach_from.
    eapply reachable_via_trans' ; eauto.
  Qed.

  Lemma transition_reachable_through_reachable : 
    forall c caddr init from to,
      reachable_via c caddr init from to -> 
      transition_reachable c caddr init to.
  Proof.
    intros.
    decompose_reachable_via H3.
    decompose_transition_reachable H_reachable.
    econstructor.
    eauto.
    econstructor.
    eapply ChainedList.clist_app ; eauto.
  Qed.
  
  Lemma is_wait_act_vo_true_vo:
    forall a,
      is_wait_act_vo a = true ->
      a = wait_action_vo.
  Proof.
    intros.
    unfold is_wait_act_vo in H3.
    destruct a eqn : H_a;try congruence.
    destruct (act_body);try congruence.
    unfold wait_action_vo.
    unfold wait_action.
    destruct_address_eq;eauto;try congruence;simpl in *;try lia.
    propify.
    destruct_and_split.
    subst.
    simpl.
    eauto.
  Qed.

  Lemma transition_trans_through c :
  forall (s0 s s' : ChainState) a,
    transition_reachable c caddr s0 s ->
    transition s a = Ok s' ->
    reachable_via c caddr s0 s s'.
  Proof.
    intros.
    unfold transition_reachable in H3;
    destruct H3 as [init_bstate [trace]].
    econstructor.
    eauto.
    econstructor.
    assert(step : TransitionStep s s').
    {
      pose proof H4 as H_new.
      unfold transition in H4.
      destruct_match in H4;try congruence.
      destruct (is_call_act a) eqn : H_call;try congruence.
      eapply step_trans;eauto.
    }
    assert(TransitionTrace s s).
    {
      eauto.
      eapply clnil.
    }
    econstructor;eauto.
  Qed.


  Lemma init_ready : 
  forall s0 c,
    is_init_state c caddr s0 ->
    readyToStepState c caddr s0 s0 .
  Proof.
    intros s0 c H_init.
    unfold readyToStepState.
    assert (H_temp:is_init_state c caddr s0) by eauto.
    decompose_is_init_state H_temp.
    split.
    unfold transition_reachable.
    split.
    eauto.
    econstructor;eauto.
    eapply clnil.
    eauto.
  Qed.


  Hint Resolve reachable_via_refl
                reachable_via_trans'
                reachable_via_trans
                reachable_via_step
                transition_reachable_through_reachable 
                transition_trans_through 
                init_ready: core.

  Hint Unfold maxMultiStratDrive : core.


  Lemma call_act_not_wait_act : 
  forall act,
    is_call_act act = true ->
    is_wait_act act = false.
Proof.
  intros.
  intros.
  unfold is_call_act in *.
  unfold is_wait_act in *.
  destruct act.
  destruct act_body;try congruence.
Qed.

Lemma wait_act_not_call_act : 
  forall act,
    is_wait_act act = true ->
    is_call_act act = false.
Proof.
  intros.
  intros.
  unfold is_call_act in *.
  unfold is_wait_act in *.
  destruct act.
  destruct act_body;try congruence.
Qed.

Lemma get_valid_header_is_valid_header s:
  validate_header( get_valid_header s )  s = true.
Proof.
  intros.
  unfold get_valid_header.
  unfold validate_header.
  propify.
  repeat split;cbn ;try lia;eauto.
  unfold miner_reward.
  unfold address_not_contract.
  rewrite miner_always_eoa.
  simpl.
  lia.
  unfold miner_reward.
  lia. 
Qed.

Lemma get_valid_header_forward_time_is_valid_header s n:
n >= 1 ->
validate_header( get_valid_header_forward_time s n)  s = true.
Proof.
  intros.
  unfold get_valid_header_forward_time.
  unfold validate_header.
  propify.
  repeat split;cbn ;try lia;eauto.
  unfold address_not_contract.
  rewrite miner_always_eoa.
  simpl.
  lia.
  unfold miner_reward.
  lia. 
Qed.

Lemma wait_action_vo_is_wait_act :
  is_wait_act wait_action_vo = true.
Proof.
  intros.
  unfold is_wait_act.
  unfold wait_action_vo.
  unfold wait_action.
  destruct_address_eq;eauto.
Qed.


Lemma multiSuccTrace_trans_thrid :
forall delta addrs s0 s1 s2 s3  tr1 tr2 tr3 n m,
  multiStratDrive delta addrs s0 s1 tr1 s2 tr2 n ->
  multiStratDrive delta addrs s0 s2 tr2 s3 tr3 m ->
  multiStratDrive delta addrs s0 s1 tr1 s3 tr3 (n + m).
Proof.
  clear H H0 H1 H2.
  intros delta addrs s0 s1 s2 tr0 tr1 tr2 tr3 n m H1 H2 .
  induction H2.
  - assert( n + 0 = n) by lia.
    rewrite H.
    assumption.
  - (* Case MS_Step *)
    assert(multiStratDrive delta addrs s0 s1 tr1 s'' tr''  (n + count + 1)).
    {
      eapply MS_Step with (s' := s') (s'' := s'') (tr' := tr') (tr'' := tr'') (count := n + count).
      + apply IHm0; assumption.
      + assumption.
    }
    assert((n + count + 1) = (n + (count + 1))) by lia.
    rewrite <- H3.
    eauto.
Qed.

    Lemma stratDrive_reachable_via :
      forall (s0 s s' : ChainState) tr_s delta addrs c tr_s' ,
        transition_reachable c caddr s0 s ->
        stratDrive s0 delta addrs s tr_s s' tr_s' ->
        reachable_via c caddr s0 s s'.
    Proof.
      intros s0 s s' tr_s delta addrs c tr_s' H_transition_reachable H_stratDrive.
      unfold stratDrive in H_stratDrive.
      destruct_and_split.
      eapply transition_trans_through;eauto.
    Qed.

  Lemma UserLiquidatesNSteps_can_reachable_via :
    forall delta_usr delta_env addrs_usr addrs_env c s0 s s' tr_s tr_s' ,
      is_init_state c caddr s0 ->
      wellStrat delta_usr addrs_usr c s0 ->
      wellStrat delta_env addrs_env c s0->
      UserLiquidatesNSteps delta_usr addrs_usr delta_env addrs_env caddr s0 s  tr_s s' tr_s' ->
      reachable_via c caddr s0 s s'.
  Proof.
    intros * Hinit Hwell_usr Hwell_env Husr_liq.
    eapply (env_mut delta_usr addrs_usr delta_env addrs_env caddr s0 
        (fun s tr_s  s' tr_s' (_ : envProgress_Mutual delta_usr addrs_usr delta_env addrs_env caddr  s0 s tr_s  s' tr_s') => is_init_state c caddr s0 -> reachable_via c caddr s0 s s')
        (fun  s tr_s  s' tr_s' (_ : UserLiquidatesNSteps delta_usr addrs_usr delta_env addrs_env caddr  s0 s tr_s  s' tr_s') => is_init_state c caddr s0 -> reachable_via c caddr s0 s s')
        );intros;eauto.
        - intros.
          specialize(H3 s1 tr 0).
          eapply H3;eauto.
          eapply MS_Refl.

        - specialize(H3 H4).
          unfold stratDrive  in s2.
          decompose_exists.
          assert(reachable_via c caddr s0 s1 s'0).
          {
            assert(transition_reachable c caddr s0 s1).
            {
              econstructor;eauto.
            }
            eapply transition_trans_through in H5;eauto.
          }
          eauto.
    Qed.

  Lemma UserLiquidatesNSteps_can_liquid :
    forall delta_usr delta_env addrs_usr addrs_env  c s0 s s' tr_s tr_s' ,
      is_init_state c caddr s0 ->
      wellStrat delta_usr addrs_usr c s0->
      wellStrat delta_env addrs_env c s0->
      UserLiquidatesNSteps delta_usr addrs_usr delta_env  addrs_env  caddr s0 s tr_s  s' tr_s' ->
      funds s' caddr = 0%Z.
  Proof.
    intros * Hinit Hwell_usr Hwell_env Husr_liq.
    eapply (env_mut delta_usr addrs_usr delta_env addrs_env caddr s0
        (* P : For interleavedExecutionEnv *)
        (fun s tr_s  s' tr_s' (_ : envProgress_Mutual delta_usr addrs_usr delta_env addrs_env caddr  s0 s tr_s  s' tr_s') =>
        funds s' caddr = 0%Z)
        (* P0 : For interleavedExecutionUsr *)
        (fun s tr_s  s' tr_s' (_ : UserLiquidatesNSteps delta_usr addrs_usr delta_env addrs_env caddr  s0 s tr_s  s' tr_s') =>
        funds s' caddr = 0%Z)
        );eauto.
    - intros.
      specialize(H3 s1 tr 0).
      eapply H3.
      eapply MS_Refl.
  Qed.


  Lemma transition_reachable_stratDrive_transition_reachable_through:
    forall s0 s tr_s  delta s' c tr' addrs,
      transition_reachable c caddr s0 s ->
      stratDrive s0 delta addrs s tr_s s' tr' ->
      reachable_via c caddr s0 s s'.
  Proof.
    intros * H_transition_reachable H_stratDrive.
    unfold stratDrive in H_stratDrive.
    destruct_and_split.
    assert(HReachable:  transition_reachable c caddr s0 s) by eauto.
    eapply transition_trans_through.
    eauto.
    eauto.
  Qed.

    
  Lemma queue_isb_empty_true : 
    forall bstate,
      queue_isb_empty bstate = true ->
      chain_state_queue bstate = [].
  Proof.
    intros * H_empty.
    unfold queue_isb_empty in H_empty.
    destruct (chain_state_queue bstate);try congruence;eauto.
  Qed.  

  Lemma empty_true_queue_isb : 
  forall bstate,
    chain_state_queue bstate = [] ->
    queue_isb_empty bstate = true .
  Proof.
    intros * H_empty.
    unfold queue_isb_empty.
    rewrite H_empty;eauto.
  Qed.  

  Lemma transition_next_state_queue_empty : 
    forall (s s' : ChainState)  a (tr_s : trace(s)),
      transition s a = Ok s' ->
      s'.(chain_state_queue) = [].
  Proof.
    intros * tr_s H_transition.
    unfold transition in H_transition.
    destruct (queue_isb_empty s) eqn : H_queue;try congruence.
    destruct (is_call_act a) eqn : H_call ;try congruence.
    destruct (add_block_exec true s (get_valid_header s) [a]) eqn : H_exec;try congruence.
    eapply add_block_next_state_queue_empty in H_exec;eauto.
    inversion H_transition;subst. eauto.
  Qed.



  Lemma transition_reachable_prev_next_trace : 
  forall (s s' : ChainState) (tr_s : trace(s)) a,
    reachable s ->
    s.(chain_state_queue) = [] ->
    transition s a = Ok s' ->
    ChainTrace s s'.
  Proof.
    intros.
    decompose_transition H5.
    eapply add_block_reachable_through_aux in Hexec;eauto.
    (* eapply add_block_reachable_through_aux in Hexec;eauto. *)
  Qed.


  Lemma ttrace_with_trace:
    forall s (tr_s:trace(s))  s',
      reachable s ->
      TransitionTrace s s' ->
      ChainTrace s s'.
  Proof.
    intros.
    induction X.
    eauto.
    assert(ChainTrace from mid).
    {
    apply IHX in H3.
    eauto.
    eauto.
    }
    inversion l.
    eapply transition_reachable_prev_next_trace in H5.
    apply (clist_app X0 H5).
    apply (clist_app  tr_s X0).
    eapply reachable_trans;eauto.
    unfold transition in H5.
    destruct (queue_isb_empty mid) eqn :H_queue;try congruence.
    eapply queue_isb_empty_true in H_queue.
    eauto.
  Qed.

  Lemma ttreachable_to_reachable:
    forall (s0 s s' : ChainState) c caddr,
        is_init_state c caddr s0 ->
        transition_reachable c caddr s0 s ->
        reachable s.
  Proof.
    intros.
    decompose_is_init_state H3.
    decompose_transition_reachable H4.
    decompose_is_init_state init_bstate.
    assert(H_t : reachable s0) by eauto.
    destruct H_t as [tr_s0].
    assert(ChainTrace s0 s).
    {
      eapply ttrace_with_trace;eauto.
    }
    eapply reachable_trans;eauto.
  Qed.

  Lemma tthrough_to_reachable_through:
    forall (s0 s s' : ChainState) c,
      is_init_state c caddr s0 ->
      reachable_via c caddr s0 s s' ->
      reachable_through s s'.
  Proof.
    intros.
    assert(reachable_via c caddr s0 s s') by eauto.
    decompose_reachable_via H5.
    assert(reachable s).
    {
      eapply ttreachable_to_reachable;eauto.
    }
    clear H_reachable.
    decompose_is_init_state H3.
    assert(reachable s) by eauto.
    destruct H5 as [trace'].
    assert(ChainTrace s s').
    {
      eapply ttrace_with_trace in tr;eauto. 
    }
    econstructor;eauto.
  Qed.

  Lemma readyToStepState_stratDrive_readyToStepState :
    forall (s0 s s' : ChainState) (tr_s : trace(s0,s)) contract delta tr_s' addrs,
      readyToStepState  contract caddr s0 s  ->
      stratDrive s0 delta addrs  s  tr_s s' tr_s' ->
      readyToStepState contract caddr s0 s'.
  Proof.
    intros.
    unfold readyToStepState.
    split.
    eapply transition_reachable_stratDrive_transition_reachable_through in H4;eauto.
    unfold readyToStepState in H3.
    destruct_and_split;eauto.
    unfold stratDrive in H4.
    destruct_and_split.
    assert (transition s x = Ok s') by eauto.
    unfold readyToStepState  in H3.
    destruct H3.
    decompose_transition_reachable H3.
    unfold is_init_state in init_bstate.
    destruct init_bstate.
    destruct H3.
    assert(trace(s)).
    {
      assert(trace( s0, s)) by eauto.
      eapply ttrace_with_trace in X0;eauto.
      eauto.
      eapply (clist_app X X0).
      econstructor; eauto.
    }
    eapply transition_next_state_queue_empty in H6;eauto.
  Qed.


  Ltac decompose_TransitionStep H :=
    inversion H as [a Hcall_to_caddr Htrans ];
    subst;
    clear H.


    Lemma readyToStepState_multiStratDrive_readyToStepState:
      forall (s0 s s' : ChainState) (tr : trace(s0,s)) (delta : strat) addrs contract tr' n,
        readyToStepState contract caddr s0 s  ->
        multiStratDrive delta addrs s0 s tr s' tr' n ->
        readyToStepState contract caddr s0 s'  .
    Proof.
        intros.
        induction H4;eauto.
        eapply readyToStepState_stratDrive_readyToStepState in H5;eauto.
    Qed.

    Lemma readyToStepState_interleavedExecution_readyToStepState:
      forall (delta_usr delta_env : strat) (addrs_usr addrs_env : list Address) (s0 s : ChainState) (tr : TransitionTrace s0 s) (s' : ChainState) (tr' : TransitionTrace s0 s') contract flag,
        readyToStepState contract caddr s0 s ->
        interleavedExecution delta_usr addrs_usr delta_env addrs_env s0 s tr flag s' tr' ->
        readyToStepState contract caddr s0 s'.
    Proof.
      intros delta_usr delta_env addrs_usr addrs_env s0 s tr s' tr' contract flag H_readyToStepState H_interaction .
      induction H_interaction;eauto.
      (* - eapply readyToStepState_timeDrive_readyToStepState in H3;eauto. *)
      - eapply readyToStepState_multiStratDrive_readyToStepState in H3;eauto.
      (* - eapply readyToStepState_multiStratDrive_readyToStepState in H3;eauto.  *)
      - eapply readyToStepState_stratDrive_readyToStepState in H3;eauto.
    Qed.


    Lemma is_delta_empty_max_succ:
      forall delta addrs n,
        is_empty_strat delta addrs ->
        strat_finite delta addrs n.
    Proof.
      intros.
      unfold strat_finite.
      intros.
      unfold is_empty_strat in H3.
      specialize(H3 s0 s tr).
      unfold maxMultiStratDrive.
      exists 0, s, tr .
      split.
      unfold maxMultiStratDriveSteps.
      lia.
      split.
      eapply MS_Refl.
      eauto.


    Qed.


        Lemma readyToStepState_multiStratDrive_reachable_via:
    forall (s0 s s' : ChainState) (delta : strat) addrs c  tr tr' n,
      readyToStepState c caddr s0 s   ->
      multiStratDrive delta addrs s0 s tr s' tr' n ->
      reachable_via c caddr s0 s s'.
    Proof.
        intros.
        assert(Hacs:readyToStepState c caddr s0 s ) by eauto.
        unfold readyToStepState in H3.
        destruct_and_split.
        induction H4;eauto.
        assert (reachable_via c caddr s0 s' s'').
        {
          eapply stratDrive_reachable_via.
          eauto.
          eauto.    
        }
        assert(Hsss:stratDrive s0 delta addrs s'  tr' s''  tr'') by eauto.
        unfold stratDrive in H7.
        destruct H7.
        destruct_and_split.
        assert(reachable_via c caddr s0 s s') by eauto.
        unfold reachable_via in H9.
        destruct H9.
        destruct H10 as [trace].
        set(t_trace := clist_app tr trace).
        destruct H8 as [trace'].
        unfold reachable_via.
        split.
        eauto.
        econstructor.
        eapply (clist_app trace trace').
    Qed.

    Lemma transition_reachable_readyToStepState: 
    forall s0 s c ,
      is_init_state c caddr s0 ->
      transition_reachable c caddr s0 s ->
      readyToStepState c caddr s0 s .
    Proof.
      intros * H_init H_transition_reachable.
      unfold readyToStepState.
      split.
      eauto.
      decompose_transition_reachable H_transition_reachable. 
      induction trace.
      - decompose_is_init_state H_init.
        eauto.
      - intuition.
        rename H4 into H_mid_queue.
        decompose_is_init_state H_init.
        assert(H_t : reachable from) by eauto.
        destruct H_t as [tr_from].
        inversion l as [a H_call H_trans ].
        + eapply transition_next_state_queue_empty in H_trans;eauto.
          eapply ttrace_with_trace in trace;eauto.
          unfold is_init_state in H_init.
          destruct_and_split.
          eapply (clist_app tr_from trace).
    Qed.

    Lemma reachable_via_multiStratDrive_reachable_via:
    forall (s0 s s' s'' : ChainState) (delta : strat) addrs c tr' tr'' n,
      reachable_via c caddr s0 s s'  ->
      multiStratDrive delta addrs s0 s' tr' s'' tr'' n ->
      reachable_via c caddr s0 s s''.
    Proof.
      intros * H_reachable_via H_multi.
      assert(H_t:reachable_via c caddr s0 s s') by eauto.
      decompose_reachable_via H_t.
      rename tr into tr_s_s'.
      decompose_transition_reachable H_reachable.
      assert(transition_reachable c caddr s0 s) by eauto.
      assert(is_init_state c caddr s0) by eauto.
      decompose_is_init_state H4.
      assert(readyToStepState c caddr s0 s' ).
      {
        eapply transition_reachable_readyToStepState;eauto.
      }
      assert(readyToStepState c caddr s0 s ).
      {
        eapply transition_reachable_readyToStepState;eauto.
      }
      eapply readyToStepState_multiStratDrive_reachable_via in H_multi;eauto.
    Qed.


    Lemma reachable_via_stratDrive_reachable_via :
      forall s0 s s' s'' tr' tr'' delta addrs c,
        reachable_via c caddr s0 s s' ->
        stratDrive s0 delta addrs s'  tr' s''  tr'' ->
        reachable_via c caddr s0 s s''.
    Proof.
      intros * H_reachable_via H_stratDrive.
      assert(H_t : reachable_via c caddr s0 s s') by eauto.
      decompose_reachable_via H_t.
      unfold reachable_via.
      split.
      rename tr into tr_s_s'.
      rename H_reachable into H_reachable_s.
      decompose_reachable_via H_reachable_via.
      eauto.
      assert(trace(s,s)).
      {
        apply clnil.
      }
      decompose_stratDrive H_stratDrive.
      destruct_and_split.
      assert(step := (step_trans a H_transition H_in)).
      econstructor.
      eapply (snoc tr step).
    Qed.


       Lemma activest_interactionSuccession_reachable_via delta_usr addrs_usr delta_env addrs_env c:
    forall s0 s  s' tr tr' flag,
      readyToStepState c caddr s0 s  ->
      interleavedExecution delta_usr addrs_usr delta_env addrs_env s0 s tr flag s' tr' ->
      reachable_via c caddr s0 s s'.
      Proof.
      intros s0 s s' tr  tr' flag H_activest H_interaction.
      assert(transition_reachable c caddr s0 s).
      {
        unfold readyToStepState in H_activest.
        destruct_and_split.
        eauto.
      }
      induction H_interaction;eauto.
      (* - eapply reachable_via_timeDrive_reachable_via in H6;eauto. *)
      - eapply reachable_via_multiStratDrive_reachable_via in H4;eauto.
      - eapply reachable_via_stratDrive_reachable_via in H4;eauto.
    Qed.

    Lemma multiSuccTrace_trans :
      forall delta addrs s0 s1 s2 tr0 tr1 tr2 n m,
        multiStratDrive delta addrs s0 s0 tr0 s1 tr1 n ->
        multiStratDrive delta addrs s0 s1 tr1 s2 tr2 m->
        multiStratDrive delta addrs s0 s0 tr0 s2 tr2 (n + m).
    Proof.
      clear H H0 H1 H2.
      intros delta addrs s0 s1 s2 tr0 tr1 tr2 n m H1 H2.
      induction H2.
      - (* Case MS_Refl *)
        (* Since s1 = s2 and tr1 = tr2 *)
        assert(n + 0 = n) by lia.
        rewrite H.
        assumption.
      (* - Case multiStratDrive_end
        apply multiStratDrive_end with (s' := s') (tr' := tr').
        + lia.
        + eapply IHm0.
          assumption.
        + assumption. *)
      - (* Case MS_Step *)
        assert(multiStratDrive delta addrs s0 s0 tr0 s'' tr''  (n + count + 1)).
        {
          eapply MS_Step with (s' := s') (s'' := s'') (tr' := tr') (tr'' := tr'') (count := n + count).
          + apply IHm0; assumption.
          + assumption.
        }
        assert((n + count + 1) = (n + (count + 1))) by lia.
        rewrite <- H3.
        eauto.
    Qed.

  Lemma multiStratSucc_n_zero_s_eq:
  forall s0 s s' tr tr' n delta addrs,
    multiStratDrive delta addrs s0 s tr s' tr' n -> 
    n = 0 ->
    s = s' /\ existT s tr = existT s' tr'.
Proof.
  intros.
  induction H3;eauto;try lia.
Qed.

Section normal.

  Lemma reachable_via_impl_contract_deployed:
    forall c caddr s0 s s',
      is_init_state c caddr s0 ->
      reachable_via c caddr s0 s s' ->
      env_contracts s' caddr = Some (c : WeakContract).
  Proof.
    intros.
    decompose_is_init_state H3.
    assert(H_reachable_t : reachable s0) by eauto.
    destruct H_reachable_t as [tr0].
    decompose_reachable_via H4.
    decompose_transition_reachable H_reachable0.
    eapply ttrace_with_trace in tr, trace;eauto.
    assert(reachable_through s0 s').
    {
      econstructor;eauto.
      econstructor;eauto.
      eapply (clist_app trace tr).
    }
    eapply reachable_through_contract_deployed in H3;eauto.
    eapply ttrace_with_trace in trace;eauto.
    eapply (clist_app tr0 trace).
    eapply ttrace_with_trace in trace;eauto.
    econstructor;eauto.
    eapply (clist_app tr0 trace).
  Qed.
    
  Lemma reachable_via_impl_contract_state:
    forall c caddr s0 s s',
      is_init_state c caddr s0 ->
      reachable_via c caddr s0 s s' ->
      exists cstate,
        env_contract_states s' caddr = Some cstate.
  Proof.
    intros.
    decompose_is_init_state H3.
    assert(H_reachable_t : reachable s0) by eauto.
    destruct H_reachable_t as [tr0].
    decompose_reachable_via H4.
    decompose_transition_reachable H_reachable0.
    eapply ttrace_with_trace in tr, trace;eauto.
    assert(reachable_through s0 s').
    {
      econstructor;eauto.
      econstructor;eauto.
      eapply (clist_app trace tr).
    }
    eapply reachable_through_contract_state in H_env_states;eauto.
    eapply ttrace_with_trace in trace;eauto.
    eapply (clist_app tr0 trace).
    eapply ttrace_with_trace in trace;eauto.
    econstructor;eauto.
    eapply (clist_app tr0 trace).
  Qed.

  Lemma reachable_via_impl_reachable_through:
    forall c caddr s0 s s',
      is_init_state c caddr s0 ->
      reachable_via c caddr s0 s s' ->
      reachable_through s s'.
  Proof.
    intros.
    decompose_is_init_state H3.
    assert(H_reachable_t : reachable s0) by eauto.
    destruct H_reachable_t as [tr0].
    decompose_reachable_via H4.
    decompose_transition_reachable H_reachable0.
    pose proof H_reachable.
    destruct H_reachable as [tr_s].
    eapply ttrace_with_trace in tr, trace;eauto.
    econstructor;eauto.
    econstructor;eauto.
    eapply (clist_app tr0 trace).
    eapply ttrace_with_trace in trace;eauto.
    eapply (clist_app tr0 trace).
    eapply ttrace_with_trace in trace;eauto.
    econstructor;eauto.
    eapply (clist_app tr0 trace).
  Qed.

  Lemma transition_reachable_impl_reachable_through:
    forall c caddr s0 s,
      is_init_state c caddr s0 ->
      transition_reachable c caddr s0 s ->
      reachable_through s0 s.
  Proof.
    intros.
    decompose_is_init_state H3.
    assert(H_reachable_t : reachable s0) by eauto.
    destruct H_reachable_t as [tr0].
    decompose_transition_reachable H4.
    eapply ttrace_with_trace in trace;eauto.
    econstructor;eauto.
  Qed.

  Lemma transition_reachable_impl_reachable:
    forall c caddr s0 s,
      is_init_state c caddr s0 ->
      transition_reachable c caddr s0 s ->
      reachable s.
  Proof.
    intros.
    decompose_is_init_state H3.
    assert(H_reachable_t : reachable s0) by eauto.
    destruct H_reachable_t as [tr0].
    decompose_transition_reachable H4.
    eapply ttrace_with_trace in trace;eauto.
    econstructor;eauto.
    eapply (clist_app tr0 trace).
  Qed.

  Lemma reachable_via_impl_reachable:
    forall c caddr s0 s s',
      is_init_state c caddr s0 ->
      reachable_via c caddr s0 s s' ->
      reachable s'.
  Proof.
    intros.
    decompose_is_init_state H3.
    assert(H_reachable_t : reachable s0) by eauto.
    destruct H_reachable_t as [tr0].
    decompose_reachable_via H4.

    decompose_transition_reachable H_reachable0.
    eapply ttrace_with_trace in tr, trace;eauto.
    econstructor;eauto.
    assert(trace' : ChainTrace s0 s').
    {
    eapply (clist_app trace tr).
    }
    eapply (clist_app tr0 trace').
    eapply ttrace_with_trace in trace;eauto.
    eapply (clist_app tr0 trace).
    eapply ttrace_with_trace in trace;eauto.
    econstructor;eauto.
    eapply (clist_app tr0 trace).
  Qed.


  Lemma readyToStepState_transition_readyToStepState:
  forall (s0 s s' : ChainState) a c,
    readyToStepState c caddr s0 s  ->
    transition s a = Ok s' ->
    readyToStepState c caddr s0 s'  .
  Proof.
    intros.
    unfold readyToStepState in *.
    destruct_and_split.
    decompose_transition_reachable H3.
    assert(trace( s, s')).
    {
      econstructor;eauto.
      pose proof H4.
      decompose_transition H3.
      (* eapply is_wait_act_vo_true_a in Hcond0.
      subst.
      eapply (step_time H4). *)
      eapply (step_trans a Hcond0 H4).
    }
    econstructor;eauto.
    assert(trace(s0,s')).
    {
      eapply (clist_app trace X).
    }
    econstructor;eauto.
    assert(transition_reachable c caddr s0 s ) by eauto.
    eapply transition_reachable_impl_reachable in H3.
    destruct H3 as [trace].
    eapply transition_next_state_queue_empty in H4;eauto.
    decompose_transition_reachable H3.
    eauto.
  Qed.

  Lemma readyToStepState_ttrace_readyToStepState:
  forall (s0 s s' : ChainState) (tr_s : trace(s0,s)) contract,
    is_init_state contract caddr s0 ->
    readyToStepState contract caddr s0 s.
  Proof.
    intros.
    unfold readyToStepState.
    split.
    econstructor;eauto.
    induction tr_s.
    + decompose_is_init_state H3.
      eauto.
    + pose proof H3.
      eapply IHtr_s in H3.
      decompose_TransitionStep l.
      pose proof H4. 
      eapply init_ready in H4.
      assert ( readyToStepState contract caddr from mid).
      {
        unfold readyToStepState.
        split.
        econstructor;eauto.
        eauto.
      }
      eapply readyToStepState_transition_readyToStepState in Htrans;eauto.
      unfold readyToStepState in Htrans.
      destruct Htrans.
      eauto.

  Qed.

  Lemma address_not_contract_not_wc {to} (addr : Address):
    reachable to ->
    address_is_contract addr = false ->
    env_contracts to addr = None.
  Proof.
    intros [trace] contract_at_addr.
    remember empty_state eqn:eq.
    induction trace; rewrite eq in *; clear eq.
    - cbn in *; congruence.
    - destruct_chain_step;
      try now rewrite_environment_equiv.
      assert( env_contracts mid addr = None).
      eapply IHtrace;eauto.
    + 
      rewrite_environment_equiv; cbn in *; destruct_address_eq; subst; auto.
    +  destruct_action_eval; rewrite_environment_equiv; cbn in *;   
        destruct_address_eq; subst; auto.
        congruence.
  Qed.


End normal.
End Strat.


Global Ltac decompose_transition_reachable H :=
  unfold transition_reachable in H;
  destruct H as [init_bstate [trace]].


Global Ltac decompose_transition H :=
    unfold transition in H;
    repeat match type of H with
    | context[if ?cond then _ else _] =>
        let Hcond := fresh "Hcond" in
        destruct cond eqn:Hcond; try congruence
    | context[match get_wait_time ?act with | Ok _ => _ | Err _ => _ end] =>
        let Hres := fresh "Hres" in
        destruct (get_wait_time act) eqn:Hres; try congruence
    | context[match add_block_exec ?mode ?state ?header ?acts with | Ok _ => _ | Err _ => _ end] =>
        let Hexec := fresh "Hexec" in
        destruct (add_block_exec mode state header acts) eqn:Hexec; try congruence
    end;
    repeat match type of H with
    | Ok _ = Ok _ => inversion H; subst; clear H
    | Err _ = Err _ => inversion H; subst; clear H
    end.

Global Ltac decompose_reachable_via H :=
  match type of H with
  | reachable_via ?contract ?caddr ?s0 ?mid ?to =>
      unfold reachable_via in H;
      let H_reachable := fresh "H_reachable" in
      let tr := fresh "tr" in
      destruct H as [H_reachable H_trace];
      destruct H_trace as [tr] (* 只引入轨迹变量 tr，避免未使用的附加绑定 *)
  | _ => fail "The hypothesis" H "is not of the form reachable_via contract caddr s0 mid to."
  end.

Global Ltac decompose_is_init_state H :=
  match type of H with
  | is_init_state ?contract ?caddr ?init_state =>
      unfold is_init_state in H;
      let H_reachable := fresh "H_reachable" in
      let H_queue := fresh "H_queue" in
      let H_env_contracts := fresh "H_env_contracts" in
      let H_env_details := fresh "H_env_details" in
      destruct H as [H_reachable [H_queue [H_env_contracts H_env_details]]];
      let ctx := fresh "ctx" in
      let setup := fresh "setup" in
      let state := fresh "state" in
      let H_env_states := fresh "H_env_states" in
      let H_init := fresh "H_init" in
      destruct H_env_details as [ctx [setup [state [H_env_states H_init]]]]
  | _ => fail "The hypothesis" H "is not of the form is_init_state contract caddr init_state."
  end.


Global Ltac decompose_exists :=
    repeat match goal with
            | [ H : exists _, _ |- _ ] =>
                let x := fresh "x" in
                destruct H as [x H]
            end.

Global  Ltac decompose_stratDrive H :=
    match type of H with
    | stratDrive ?s0 ?delta ?addrs ?s ?tr ?s' ?tr' =>
        unfold stratDrive in H;
        let a := fresh "a" in
        let H_trans := fresh "H_transition" in
        destruct H as [a [H_trans [H_in H_trace]]]
    | _ => fail "The hypothesis" H "is not of the form stratDrive s0 delta addrs s tr s' tr'."
    end.


Global Ltac solve_facts :=
  repeat match goal with
    | H := ?f : nat -> nat -> nat -> nat -> nat -> nat -> Prop |- _ =>
        is_evar f; instantiate (H := fun _ _ _ _ _ _ => Logic.True)
    | H := ?f : _ -> ContractCallContext -> Prop |- _ =>
        is_evar f; instantiate (H := fun _ _ => Logic.True)
    | H := ?f : Chain -> ContractCallContext -> _ ->
    list ActionBody -> option (list (ContractCallInfo _)) -> Prop |- _ =>
        is_evar f; instantiate (H := fun _ _ _ _ _ => Logic.True)
    end;
    unset_all; subst;
    destruct_chain_step; [
       auto
     | destruct_action_eval; [
         auto
       | auto
       | auto; intros ?cstate ?deployed ?deployed_state;
          cbn; subst
       ]
    ].

Global Ltac decompose_wellStrat H :=
    unfold wellStrat in H;
    let Hs0 := fresh "Hs0" in
    let Hs := fresh "Hs" in
    let Htr_s := fresh "Htr_s" in
    intros Hs0 Hs Htr_s;
    match type of H with
    | context[let delta_actions := ?delta _ _ _ _ in _] =>
        let Hda := fresh "Hda" in
        set (delta_actions := delta _ _ _ _) in H;
        unfold delta_actions in H
    | _ => idtac
    end;
    match type of H with
    | _ -> Forall _ _ =>
        let Hq := fresh "Hq" in
        intros Hq; specialize (H Hq)
    | Forall _ ?l =>
        let Ha := fresh "Ha" in
        apply Forall_forall in H; intros Ha
    | _ => idtac
    end.

