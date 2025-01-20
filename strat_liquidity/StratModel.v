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
Require Import ModelBase.
From Coq Require Import List.
From Coq Require Import Bool.
From Coq Require Import ZArith.
From Coq Require Import Arith.
From Coq Require Import String.
From Coq Require Import Lia.
Import RecordSetNotations.
From Coq Require Import Permutation.
Import ListNotations.

Section Strat.

Local Open Scope bool.

Context {AddrSize : N}.
Context {DepthFirst : bool}.

Definition Error : Type := nat.
Definition default_error: Error := 1%nat.

  (* 添加记法，使得 tr ( s ) 可以被识别为 tr s *)
Notation "trace( s )" := (ChainTrace empty_state s) (at level 10).

Context {BaseTypes : ChainBase}.
Set Primitive Projections.
Set Nonrecursive Elimination Schemes.

Local Open Scope Z.

Hint Constructors ChainStep : core.
Hint Constructors ChainedList : core.
Hint Unfold ChainTrace : core.
  
Context {Setup Msg State Error : Type}
        `{Serializable Setup}
        `{Serializable Msg}
        `{Serializable State}
        `{Serializable Error}.
  
Variable miner_address : Address.

Hypothesis miner_always_eoa : address_is_contract miner_address = false.

Global Definition miner_reward := 10%Z.

Section transition_trace.
    
  Definition funds (env : ChainState) (caddr : Address) : Amount :=
    env_account_balances env caddr.

  Lemma reachable_funds_nonnegative:
    forall s caddr,
      reachable s ->
      (funds s caddr >= 0)%Z .
  Proof.
    intros.
    unfold funds.
    eapply account_balance_nonnegative;eauto.
  Qed.

  Definition safe_Z_to_nat (z : Z) : nat :=
    if Z.leb 0 z then Z.to_nat z else 0.
  
  
  Global Definition time_speed := 1%nat.

  Definition get_valid_header bstate : BlockHeader :=
    build_block_Header 
      (S (chain_height bstate))
      (current_slot bstate + 1)%nat
      (finalized_height bstate)
      miner_reward
      miner_address.

  Definition is_init_state 
              (contract : Contract Setup Msg State Error) 
              (caddr : Address)
              (init_state : ChainState) :=
      reachable init_state /\
      chain_state_queue init_state = [] /\
      env_contracts init_state caddr = Some (contract : WeakContract) /\
      let env := init_state.(chain_state_env) in
      exists ctx setup state,
        env_contract_states init_state caddr = Some (serialize state) /\
        init contract env ctx setup = Ok state.

  Definition is_call_act (a : Action) : bool :=
    match a with
    | build_act _ _ (act_call _ _ _) => true
    | _ => false
    end.

  Definition transition
              (prev_bstate : ChainState)
              (act : Action) 
              : result ChainState Strat.Error :=
    if (queue_isb_empty prev_bstate) then 
        if is_call_act act then
          let header := get_valid_header prev_bstate in
          match evaluate_action true prev_bstate header [act] with
          | Ok new_bstate => Ok new_bstate
          | Err _ => Err default_error
          end
        else 
          Err default_error
    else 
      Err default_error.

  Inductive TransitionStep (prev_bstate : ChainState) (next_bstate : ChainState) :=
  | step_trans :
      forall (a : Action),
        is_call_act a = true ->
        transition prev_bstate a = Ok next_bstate ->
        TransitionStep prev_bstate next_bstate.
  
  Global Arguments step_trans {_ _  }.

  Definition aux_trace := prefixTrace ChainState TransitionStep.

  Definition TransitionTrace := ChainedList ChainState TransitionStep.

  Notation "trace( from , to )" := (TransitionTrace from to)(at level 10).

  Definition transition_reachable 
              (contract : Contract Setup Msg State Error)
              (caddr :Address)
              (s0 s : ChainState) :=
    is_init_state contract caddr s0  /\
    inhabited (trace(s0, s)).

  Definition reachable_via 
              (contract : Contract Setup Msg State Error)
              (caddr :Address)
              (s0  mid to : ChainState) := 
   transition_reachable contract caddr s0  mid /\ inhabited (trace(mid, to)).
 
  (* 清算能力的存在性 *)
  Definition base_liquidity 
              (c : Contract Setup Msg State Error)
              (caddr : Address) 
              (s0 : ChainState)
              : Prop :=
    forall s ,
      is_init_state c caddr s0 ->
      transition_reachable c caddr s0  s ->
      exists s',
        (inhabited(trace( s, s')) /\ funds s' caddr = 0)%Z.
End transition_trace.

Section strat_model.

  Notation "trace( from , to )" := (TransitionTrace from to)(at level 10).

  Definition strat (addrs : list Address):= forall s0 s,trace(s0, s) -> list Action.

  Definition is_valid_action (s : ChainState) (a : Action) : bool :=
    match transition s a with
    | Ok _ => is_call_act a
    | Err _ => false
    end.

  (* delta 这些地址产生的动作中包含了所有的转换，其中包含空集的情况 *)
  Definition is_complete_strategy 
                  (addrs : list Address)
                  (delta : strat addrs)
                  (contract : Contract Setup Msg State Error)
                  (caddr : Address)
                  (s0 : ChainState) :=
    (forall s s' tr a,
      transition s a = Ok s' ->
       In a (delta s0 s tr)).

  Definition is_empty_strat (addrs : list Address) (delta : strat addrs) : Prop :=
    forall s0 s tr_s, delta s0 s tr_s = [].

  Definition incl {A : Type} (l1 l2 : list A) : Prop :=
    forall x, In x l1 -> In x l2.

  Definition stratDrive 
              (addrs : list Address)
              (delta : strat addrs)
              (s0 s : ChainState)
              (tr : trace(s0, s))
              (s' : ChainState)
              (tr' : trace(s0, s'))
              : Prop :=
    exists  (a : Action)
            (Hact : is_call_act a = true)
            (Htrans : transition s a = Ok s'),
      In a (delta s0 s tr) /\
      tr' = snoc tr (step_trans a Hact Htrans).

  Local Open Scope nat.
  Inductive multiStratDrive
            (addrs : list Address)
            (delta : strat addrs) 
            (s0 s : ChainState) 
            (tr : TransitionTrace s0 s) :
    forall s', TransitionTrace s0 s' -> nat -> Prop :=
    | MS_Refl :
        multiStratDrive addrs delta s0 s tr s tr 0
    | MS_Step :
        forall s' s'' tr' tr'' count ,
          multiStratDrive addrs delta  s0 s tr s' tr' count -> 
          stratDrive addrs delta s0  s' tr' s'' tr''-> 
          multiStratDrive addrs delta  s0 s tr s'' tr'' (count + 1).

  (* 表示该哪一方行动了 *)
  Inductive stratType :=
    | Tusr
    | Tenv.

  Inductive interleavedExecution 
              (addrs_usr : list Address)
              (delta_usr : strat addrs_usr)
              (addrs_env : list Address)
              (delta_env : strat addrs_env)
              (s0 s : ChainState)
              (tr : trace(s0, s)) :
    stratType -> forall s' : ChainState, trace(s0, s') -> Prop :=
    | IS_Refl : forall flag : stratType,
        interleavedExecution addrs_usr delta_usr addrs_env delta_env  s0 s tr flag s tr
    | ISE_Step : forall s' tr' s'' tr'' n,
        interleavedExecution addrs_usr delta_usr addrs_env delta_env s0 s tr Tenv s' tr' ->
        multiStratDrive addrs_env delta_env  s0 s' tr' s'' tr'' n ->
        interleavedExecution addrs_usr delta_usr addrs_env delta_env s0 s tr Tusr s'' tr''
    | ISU_Step : forall s' s'' tr' tr'',
        interleavedExecution addrs_usr delta_usr addrs_env delta_env s0 s tr Tusr s' tr' ->
        stratDrive  addrs_usr delta_usr s0  s' tr' s'' tr'' ->
        interleavedExecution addrs_usr delta_usr addrs_env delta_env s0 s tr Tenv s'' tr''.

  Local Open Scope nat.

  Inductive UserLiquidatesNSteps 
              (addrs_usr : list Address)
              (delta_usr : strat addrs_usr)
              (addrs_env : list Address)
              (delta_env : strat addrs_env)
              (caddr: Address)
              (s0 s : ChainState)
              (tr : trace(s0, s)) : Prop :=
    | ULM_Base: 
      (funds s caddr = 0)%Z ->
      UserLiquidatesNSteps addrs_usr delta_usr addrs_env delta_env caddr s0 s tr 
    | ULM_Step : forall s' tr',
      stratDrive addrs_usr delta_usr  s0 s tr s' tr' -> 
      envProgress_Mutual addrs_usr delta_usr addrs_env delta_env caddr s0 s' tr'  -> 
      UserLiquidatesNSteps addrs_usr delta_usr addrs_env delta_env caddr  s0 s tr 
  with envProgress_Mutual 
        (addrs_usr : list Address)
        (delta_usr : strat addrs_usr)
        (addrs_env : list Address)
        (delta_env : strat addrs_env)
        (caddr: Address)
        (s0 s : ChainState)
        (tr : trace(s0, s)) : Prop :=
    | EPM_Base :
      (funds s caddr = 0)%Z ->
      envProgress_Mutual addrs_usr delta_usr addrs_env delta_env caddr s0 s tr 
    | EPM_Step: 
      (funds s caddr > 0)%Z ->
      ( forall s' tr' n,
          multiStratDrive addrs_env delta_env s0 s tr s' tr' n -> 
          UserLiquidatesNSteps addrs_usr delta_usr addrs_env delta_env caddr s0 s' tr'  ) -> 
      envProgress_Mutual addrs_usr delta_usr addrs_env delta_env caddr s0 s tr.

  Scheme ul_mut := Induction for envProgress_Mutual Sort Prop
    with env_mut := Induction for UserLiquidatesNSteps Sort Prop.

  Combined Scheme ul_mutual_ind from ul_mut, env_mut.

  Local Open Scope nat.

  Definition strat_liquidity 
            (addrs_usr : list Address)
            (delta_usr : strat addrs_usr)
            (addrs_env : list Address)
            (delta_env : strat addrs_env)
            (c : Contract Setup Msg State Error)
            (caddr : Address)
            (s0 : ChainState) :=
    is_init_state c caddr s0 ->
    forall tr s' tr',
      interleavedExecution addrs_usr delta_usr addrs_env delta_env  s0 s0 tr Tusr s' tr' ->
      UserLiquidatesNSteps addrs_usr delta_usr addrs_env delta_env caddr s0 s' tr'.

End strat_model.
  
  Ltac decompose_exists :=
    repeat match goal with
            | [ H : exists _, _ |- _ ] =>
                let x := fresh "x" in
                destruct H as [x H]
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
    | context[if queue_isb_empty ?state then _ else _] =>
        let Hqueue := fresh "Hqueue" in
        destruct (queue_isb_empty state) eqn:Hqueue; try congruence
    | context[if is_call_act ?act then _ else _] =>
        let Hcall := fresh "Hcall" in
        destruct (is_call_act act) eqn:Hcall; try congruence
    | context[let header := get_valid_header ?state in _] =>
        let Hheader := fresh "Hheader" in
        remember (get_valid_header state) as header eqn:Hheader
    | context[match evaluate_action ?mode ?state ?header ?acts with | Ok _ => _ | Err _ => _ end] =>
        let Hexec := fresh "Hexec" in
        destruct (evaluate_action mode state header acts) eqn:Hexec; try congruence
    | context[match ?res with | Ok _ => _ | Err _ => _ end] =>
        let Hres := fresh "Hres" in
        destruct res eqn:Hres; try congruence
    end;
    repeat match type of H with
    | Ok _ = Ok _ => inversion H; subst; clear H
    | Err _ = Err _ => inversion H; subst; clear H
    end.

  Notation "trace( from , to )" := (TransitionTrace from to)(at level 10).

  Lemma transition_reachable_init_state c s0 caddr:
    is_init_state c caddr s0 ->
    transition_reachable c caddr s0 s0.
  Proof.
    intros.
    unfold transition_reachable.
    split.
    eauto.
    decompose_is_init_state H3.
    destruct H_reachable as [trace].
    econstructor.
    eauto.
    eapply clnil.
  Qed.

  Lemma transition_reachable_trans c s0 s s' caddr:
    transition_reachable c caddr s0 s -> 
    TransitionTrace s s' -> 
    transition_reachable c caddr s0 s'.
  Proof.
    intros H_reachable H_trace.
    decompose_transition_reachable H_reachable.
    econstructor;eauto.
    unfold transition_reachable in *.
    eauto.
    split.
    eapply clist_app;eauto.
  Qed.

  Lemma transition_reachable_step s0 c from to caddr:
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
  

  Lemma transition_trans_through c caddr:
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


  Hint Resolve reachable_via_refl
                reachable_via_trans'
                reachable_via_trans
                reachable_via_step
                transition_reachable_through_reachable 
                transition_trans_through : core.

  Local Open Scope nat.

  Lemma multiStratDrive_n_zero_s_eq:
    forall s0 s s' tr tr' n delta addrs,
      multiStratDrive delta addrs s0 s tr s' tr' n -> 
      (n = 0)%nat ->
      s = s' /\ existT s tr = existT s' tr'.
  Proof.
    intros s0 s s' tr tr' n delta addrs H_multi H_n.
    induction H_multi;eauto;try lia.
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
      forall (s0 s s' : ChainState) tr_s delta addrs c caddr tr_s' ,
        transition_reachable c caddr s0 s ->
        stratDrive addrs delta  s0  s tr_s s' tr_s' ->
        reachable_via c caddr s0 s s'.
    Proof.
      intros s0 s s' tr_s delta addrs c caddr tr_s' H_transition_reachable H_stratDrive.
      unfold stratDrive in H_stratDrive.
      destruct_and_split.
      eapply transition_trans_through;eauto.
    Qed.

  Lemma transition_reachable_stratDrive_transition_reachable_through:
    forall s0 s tr_s addrs delta s' c caddr tr' ,
      transition_reachable c caddr s0 s ->
      stratDrive addrs delta s0 s tr_s s' tr' ->
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

  Lemma transition_reachable_stratDrive_transition_reachable:
    forall s0 s tr_s addrs delta s' c caddr tr' ,
      transition_reachable c caddr s0 s ->
      stratDrive addrs delta s0 s tr_s s' tr' ->
      transition_reachable c caddr s0 s'.
  Proof.
    intros * H_transition_reachable H_stratDrive.
    eapply transition_reachable_stratDrive_transition_reachable_through in H_stratDrive;eauto.
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
    destruct (evaluate_action true s (get_valid_header s) [a]) eqn : H_exec;try congruence.
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
    forall (s0 s s' : ChainState) c caddr,
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

  Ltac decompose_TransitionStep H :=
    inversion H as [a Hcall_to_caddr Htrans ];
    subst;
    clear H.

    Lemma transition_reachable_multiStratDrive_transition_reachable:
      forall (s0 s s' : ChainState) (tr : trace(s0,s)) delta addrs contract caddr tr' n,
        transition_reachable contract caddr s0 s  ->
        multiStratDrive addrs delta  s0 s tr s' tr' n ->
        transition_reachable contract caddr s0 s'  .
    Proof.
        intros.
        induction H4;eauto.
        eapply transition_reachable_stratDrive_transition_reachable in H5;eauto.
    Qed.

    Lemma transition_reachable_interleavedExecution_transition_reachable:
      forall delta_usr delta_env (addrs_usr addrs_env : list Address) (s0 s : ChainState) (tr : TransitionTrace s0 s) (s' : ChainState) (tr' : TransitionTrace s0 s') contract caddr flag,
        transition_reachable contract caddr s0 s ->
        interleavedExecution addrs_usr delta_usr addrs_env delta_env  s0 s tr flag s' tr' ->
        transition_reachable contract caddr s0 s'.
    Proof.
      intros delta_usr delta_env addrs_usr addrs_env s0 s tr s' tr' contract caddr flag transition_reachable H_interaction .
      induction H_interaction;eauto.
      - eapply transition_reachable_multiStratDrive_transition_reachable in H3;eauto.
      - eapply transition_reachable_stratDrive_transition_reachable in H3;eauto.
    Qed.

    Lemma transition_reachable_multiStratDrive_reachable_via:
    forall (s0 s s' : ChainState) delta  addrs c caddr tr tr' n,
      transition_reachable c caddr s0 s   ->
      multiStratDrive addrs delta  s0 s tr s' tr' n ->
      reachable_via c caddr s0 s s'.
    Proof.
        intros.
        assert(Hacs:transition_reachable c caddr s0 s ) by eauto.
        unfold transition_reachable in H3.
        destruct_and_split.
        induction H4;eauto.
        assert (reachable_via c caddr s0 s' s'').
        {
          eapply stratDrive_reachable_via.
          eauto.
          eauto.    
        }
        assert(Hsss:stratDrive addrs delta  s0 s'  tr' s''  tr'') by eauto.
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

    Lemma reachable_via_stratDrive_reachable_via :
      forall s0 s s' s'' tr' tr'' delta addrs c caddr,
        reachable_via c caddr s0 s s' ->
        stratDrive  addrs delta  s0 s'  tr' s''  tr'' ->
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

    Lemma transition_reachable_interleavedExecution_reachable_via:
      forall delta_usr delta_env (addrs_usr addrs_env : list Address) (s0 s : ChainState) (tr : TransitionTrace s0 s) (s' : ChainState) (tr' : TransitionTrace s0 s') contract caddr flag,
        transition_reachable contract caddr s0 s ->
        interleavedExecution addrs_usr delta_usr addrs_env delta_env s0 s tr flag s' tr' ->
        reachable_via contract caddr s0 s s'.
    Proof.
      intros delta_usr delta_env addrs_usr addrs_env s0 s tr s' tr' contract caddr flag transition_reachable H_interaction .
      induction H_interaction.
      - eapply reachable_via_refl.
        eauto.
      - eapply transition_reachable_multiStratDrive_reachable_via in H3;eauto.
      - eapply reachable_via_stratDrive_reachable_via in H3;eauto.
    Qed.

    Lemma reachable_via_impl_reachable :
      forall s0 s s' caddr c,
        reachable_via c caddr s0 s s' ->
        transition_reachable c caddr s0 s'.
    Proof.
      intros.
      unfold reachable_via in *.
      destruct_and_split.
      destruct H4 as [tr].
      eapply transition_reachable_trans in H3;eauto.
    Qed.

    Lemma reachable_via_multiStratDrive_reachable_via:
    forall (s0 s s' s'' : ChainState) delta  addrs c caddr tr' tr'' n,
      reachable_via c caddr s0 s s'  ->
      multiStratDrive addrs delta  s0 s' tr' s'' tr'' n ->
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
      assert(transition_reachable c caddr s0 s' ).
      {
        eapply reachable_via_impl_reachable;eauto.
      }
      eapply transition_reachable_multiStratDrive_reachable_via in H_multi;eauto.
    Qed.

  Lemma UserLiquidatesNSteps_can_reachable_via :
    forall delta_usr delta_env addrs_usr addrs_env c caddr s0 s tr_s  ,
      is_init_state c caddr s0 ->
      UserLiquidatesNSteps addrs_usr delta_usr addrs_env delta_env caddr s0 s tr_s  ->
      exists s' ,
      (funds s' caddr = 0)%Z /\
      reachable_via c caddr s0 s s'.
  Proof.
    intros * Hinit Husr_liq.
    eapply (env_mut addrs_usr delta_usr addrs_env delta_env caddr s0  
        (fun s tr_s  (_ : envProgress_Mutual addrs_usr delta_usr addrs_env delta_env caddr s0 s tr_s ) => exists s' ,
        (funds s' caddr = 0)%Z /\
        reachable_via c caddr s0 s s' )
        (fun  s tr_s  (_ : UserLiquidatesNSteps addrs_usr delta_usr addrs_env delta_env caddr s0 s tr_s ) => exists s' ,
        (funds s' caddr = 0)%Z /\
        reachable_via c caddr s0 s s' )
        );intros;eauto.
        - exists s1.
          split.
          eauto.
          eapply reachable_via_refl;eauto.
        - specialize(H3 s1 tr 0).
          assert (multiStratDrive addrs_env delta_env s0 s1 tr s1 tr 0 ).
          eapply MS_Refl.
          eapply H3 in H4.
          eauto.
        - exists s1.
          split.
          eauto.
          eapply reachable_via_refl;eauto.
        - destruct H3.
          destruct H3.
          pose proof H4.
          decompose_reachable_via H4.
          rename x into s''.
          exists s''.
          split.
          eauto.
          assert (reachable_via c caddr s0 s1 s1).
          {
              eapply reachable_via_refl.
              econstructor;eauto.
          }
          assert(reachable_via c caddr s0 s1 s').
          {
            eapply reachable_via_stratDrive_reachable_via;eauto.
          }
          eapply reachable_via_trans;eauto.
    Qed.

  (* 正确性证明，以后证明 *)
  (* Lemma UserLiquidatesNSteps_can_liquid :
    forall delta_usr delta_env addrs_usr addrs_env c caddr s0 s tr0 tr_s  ,
      is_init_state c caddr s0 ->
      interleavedExecution addrs_usr delta_usr addrs_env delta_env s0 s0 tr0 Tusr s tr_s ->
      UserLiquidatesNSteps addrs_usr delta_usr addrs_env delta_env caddr s0 s tr_s ->
      exists s' tr' flag,
      interleavedExecution addrs_usr delta_usr addrs_env delta_env s0 s tr_s flag s' tr' /\
      funds s' caddr = 0%Z.
  Proof.
    intros * Hinit Hrc Husr_liq.
    eapply (env_mut addrs_usr delta_usr addrs_env delta_env caddr s0 
        (* P : For interleavedExecutionEnv *)
        (fun s tr_s  (_ : envProgress_Mutual addrs_usr delta_usr addrs_env delta_env caddr s0 s tr_s  ) =>  interleavedExecution addrs_usr delta_usr addrs_env delta_env s0 s tr_s Tenv s tr_s ->
        exists s' tr' flag,
        interleavedExecution addrs_usr delta_usr addrs_env delta_env s0 s tr_s flag s' tr' /\
        funds s' caddr = 0%Z)
        (* P0 : For interleavedExecutionUsr *)
        (fun s tr_s  (_ : UserLiquidatesNSteps addrs_usr delta_usr addrs_env delta_env caddr s0 s tr_s ) => interleavedExecution addrs_usr delta_usr addrs_env delta_env s0 s tr_s Tusr s tr_s ->
        exists s' tr' flag, 
        interleavedExecution addrs_usr delta_usr addrs_env delta_env s0 s tr_s flag s' tr' /\
        funds s' caddr = 0%Z)
        );intros;eauto;intuition.
    - specialize(H3 s1 tr 0).
      assert (multiStratDrive addrs_env delta_env s0 s1 tr s1 tr 0) by eapply MS_Refl.
      eapply H3 in H5 as Hnew;eauto.
      eapply IS_Refl.
    - assert (interleavedExecution addrs_usr delta_usr addrs_env delta_env s0 s' tr' Tenv s' tr') by eapply IS_Refl.
      eapply H3 in H5.
      destruct H5 as [s'' [tr'' [flag [Hint Hfund]]]].
    - eapply IS_Refl. 
  Qed. *)

  Lemma transition_determin:
    forall (s s1 s2  : ChainState) a,
      transition s a= Ok s1->
      transition s a= Ok s2->
      s1 = s2.
  Proof.
    intros.
    unfold transition in *.
    intuition.
  Qed.

  Lemma transition_prev_queue_empty:
    forall s s' a,
      transition s a  = Ok s' ->
      chain_state_queue s = [] .
  Proof.
    intros.
    unfold transition in H3.
    destruct (queue_isb_empty s) eqn : He;try congruence.
    unfold queue_isb_empty  in He.
    destruct (chain_state_queue s) ;try congruence;eauto.
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

  Lemma multiStratSucc_n_zero_s_eq:
    forall s0 s s' tr tr' n delta addrs,
      multiStratDrive delta addrs s0 s tr s' tr' n -> 
      n = 0 ->
      s = s' /\ existT s tr = existT s' tr'.
  Proof.
    intros.
    induction H3;eauto;try lia.
  Qed.

  Lemma multiSuccTrace_delta_empty_refl_multr_s_tr :
    forall (s0 s : ChainState) (tr : trace(s0,s)) (s' : ChainState) (tr' : trace(s0 ,s')) addrs delta  n,
      delta s0 s tr = [] ->
      multiStratDrive addrs  delta  s0 s tr s' tr' n ->
      s = s' /\ existT s tr = existT s' tr'.
  Proof.
    intros.
    induction H4;eauto.
    destruct IHmultiStratDrive.
    eauto.
    subst.
    unfold stratDrive in H5.
    do 4 destruct H5.
    assert(delta s0 s' tr' = []).
    {
      inversion H7.
      eauto.
    }
    destruct_and_split.
    rewrite H8 in H5.
    inversion H5.
    rewrite H8 in H5.
    inversion H5.
  Qed.

  Lemma transition_reachable_queue_is_empty:
  forall s0 s (c : Contract Setup Msg State Error) addr,
    is_init_state c addr s0 ->
    transition_reachable c addr s0 s ->
    chain_state_queue s = [].
Proof.
  intros.
  decompose_transition_reachable H4.
  induction trace.
  - eapply (transition_reachable_init_state) in H3;eauto.
    decompose_is_init_state init_bstate.
    eauto.
  - inversion l.
    assert (transition_reachable c addr from mid);eauto.
    eapply transition_reachable_impl_reachable in H6;eauto.
    destruct H6 as [tr].
    eapply transition_next_state_queue_empty in H5;eauto. 
Qed.


  Lemma transition_reachable_transition_transition_reachable:
  forall (s0 s s' : ChainState) a c caddr,
    transition_reachable c caddr s0 s  ->
    transition s a = Ok s' ->
    transition_reachable c caddr s0 s'  .
  Proof.
    intros.
    decompose_transition_reachable H3. 
    destruct_and_split.
    assert(trace( s, s')).
    {
      econstructor;eauto.
      pose proof H4.
      decompose_transition H3.
      (* eapply is_wait_act_vo_true_a in Hcond0.
      subst.
      eapply (step_time H4). *)
      eapply (step_trans a Hcall H4).
    }
    econstructor;eauto.
    assert(trace(s0,s')).
    {
      eapply (clist_app trace X).
    }
    econstructor;eauto.
  Qed.

  Lemma transition_reachable_ttrace_transition_reachable:
  forall (s0 s s' : ChainState) (tr_s : trace(s0,s)) contract caddr,
    is_init_state contract caddr s0 ->
    transition_reachable contract caddr s0 s.
  Proof.
    intros.
    eapply transition_reachable_trans;eauto.
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

Global Ltac decompose_TransitionStep H :=
  inversion H as [a Hcall_to_caddr Htrans ];
  subst;
  clear H.

Global Ltac decompose_transition_reachable H :=
  unfold transition_reachable in H;
  destruct H as [init_bstate [trace]].

Global Ltac decompose_transition H :=
  unfold transition in H;
  repeat match type of H with
  | context[if queue_isb_empty ?state then _ else _] =>
      let Hqueue := fresh "Hqueue" in
      destruct (queue_isb_empty state) eqn:Hqueue; try congruence
  | context[if is_call_act ?act then _ else _] =>
      let Hcall := fresh "Hcall" in
      destruct (is_call_act act) eqn:Hcall; try congruence
  | context[let header := get_valid_header ?state in _] =>
      let Hheader := fresh "Hheader" in
      remember (get_valid_header state) as header eqn:Hheader
  | context[match evaluate_action ?mode ?state ?header ?acts with | Ok _ => _ | Err _ => _ end] =>
      let Hexec := fresh "Hexec" in
      destruct (evaluate_action mode state header acts) eqn:Hexec; try congruence
  | context[match ?res with | Ok _ => _ | Err _ => _ end] =>
      let Hres := fresh "Hres" in
      destruct res eqn:Hres; try congruence
  end;
  repeat match type of H with
  | Ok _ = Ok _ => inversion H; subst; clear H
  | Err _ = Err _ => inversion H; subst; clear H
  end.

Global Ltac decompose_reachable_via H :=
  match type of H with
  | reachable_via ?miner_address ?contract ?caddr ?s0 ?mid ?to =>
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
    | stratDrive ?miner_address ?addrs ?delta  ?s0 ?s ?tr ?s' ?tr' =>
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