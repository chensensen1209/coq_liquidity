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

Section equiv.
  





Lemma delta_all_is_wellStrat:
forall delta addrs contract s0 ,
  is_init_state contract caddr s0 ->
  is_complete_strategy delta addrs contract s0 ->
  wellStrat delta addrs contract s0.
Proof.
  intros * H_init H_complete_strategy.
  edestruct H_complete_strategy;eauto.
Qed.

Lemma multiStratDrive_n_zero_s_eq:
  forall s0 s s' tr tr' n delta addrs,
    multiStratDrive delta addrs s0 s tr s' tr' n -> 
    n = 0 ->
    s = s' /\ existT s tr = existT s' tr'.
Proof.
  intros s0 s s' tr tr' n delta addrs H_multi H_n.
  induction H_multi;eauto;try lia.
Qed.

Lemma delta_empty_is_wellStrat delta addrs contract s0 :
is_empty_strat delta addrs -> 
wellStrat delta addrs contract s0.
Proof.
  unfold wellStrat, is_empty_strat.
  intros.
  split.
  intros.
  specialize(H3 s0 s tr_s).
  rewrite H3.
  unfold is_valid_action.
  eapply Forall_forall.
  intros.
  inversion H5.
  eapply Forall_forall.
  intros.
  specialize(H3 s0 s tr_s).
  rewrite H3 in H4.
  inversion H4.
Qed.

Lemma wait_action_vo_in_list_no_call :
forall x,
  In x [wait_action_vo] ->
  is_call_act x = false.
Proof.
  intros.
  inversion H3.
  unfold is_call_act.
  rewrite <- H4.
  unfold wait_action_vo.
  unfold wait_action.
  eauto.
  inversion H4.
Qed.

Lemma multiSuccTrace_delta_empty_refl_multr :
  forall (s0 s : ChainState) (tr : trace(s0,s)) (s' : ChainState) (tr' : trace(s0 ,s')) delta addrs n,
    is_empty_strat delta addrs ->
    multiStratDrive delta addrs s0 s tr s' tr' n ->
    n = 0 /\ multiStratDrive delta addrs s0 s tr s tr n.
Proof.
  intros s0 s tr s' tr' delta addrs n H_empty H_multi.
  induction H_multi;try lia;eauto.
  - split.
    eauto.
    apply MS_Refl.
  - unfold stratDrive in H3.
    do 4 destruct H3.
    unfold is_empty_strat in H_empty.
    specialize(H_empty s0 s' tr').
    rewrite H_empty in H3.
    inversion H3.
Qed.

Lemma multiSuccTrace_delta_empty_refl_multr_end :
forall (s0 s : ChainState) (tr : trace(s0,s)) (s' : ChainState) (tr' : trace(s0 ,s')) delta addrs n,
  is_empty_strat delta addrs ->
  multiStratDrive delta addrs s0 s tr s' tr' n ->
  n = 0 /\ 
  multiStratDrive delta addrs s0 s' tr' s' tr' n /\ 
  s = s' /\
  existT s' tr' = existT s tr.
Proof.
intros s0 s tr s' tr' delta addrs n H_empty H_multi.
induction H_multi;try lia;eauto.
- split.
  lia.
  split.
  eapply MS_Refl.
  eauto.
- unfold stratDrive in H3.        
  do 3 destruct H3.
  unfold is_empty_strat in H_empty.
  specialize(H_empty s0 s' tr').
  rewrite H_empty in H3.
  destruct_and_split.
  inversion H3.
  inversion H3.
  inversion H3.
  inversion H3.
Qed.

Lemma multiSuccTrace_delta_empty_refl_multr_s_tr :
forall (s0 s : ChainState) (tr : trace(s0,s)) (s' : ChainState) (tr' : trace(s0 ,s')) delta addrs n,
  delta s0 s tr addrs = [] ->
  multiStratDrive delta addrs s0 s tr s' tr' n ->
  s = s' /\ existT s tr = existT s' tr'.
Proof.
  intros.
  induction H4;eauto.
  destruct IHmultiStratDrive.
  eauto.
  subst.
  unfold stratDrive in H5.
  do 4 destruct H5.
  assert(delta s0 s' tr' addrs = []).
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


Lemma transition_reachable_can_Inter_usr_all:
forall s0 s (tr:trace(s0,s0))  c delta_usr delta_env addrs_usr addrs_env,
  is_complete_strategy delta_usr addrs_usr c s0->
  is_empty_strat delta_env addrs_env ->
  is_init_state c caddr s0  ->
  transition_reachable c caddr s0 s ->
  exists (trace:trace(s0,s)),
    interleavedExecution delta_usr addrs_usr delta_env addrs_env s0 s0 tr Tusr s trace.
Proof.
intros s0 s tr c delta_usr delta_env addrs_usr addrs_env
H_complete_strategy H_empty_delta H_init_state H_transition_reachable.
assert(H_temp: transition_reachable c caddr s0 s) by eauto.
decompose_transition_reachable H_temp.
induction trace.
+ exists tr.
  eapply IS_Refl.
+ assert (transition_reachable c caddr from mid).
  {
    econstructor;eauto.
  }
  specialize(IHtrace tr H_complete_strategy init_bstate  H3 init_bstate).
  destruct IHtrace as [tr' IHtrace].
  pose proof l.
  inversion X.
  * set(tr'' := snoc tr' (step_trans a H4 H5)).
    exists tr''.
    pose proof H4.
    (* assert(delta_env from mid tr' addrs_env = [wait_action_vo]).
    {
      eauto.
    } *)
    assert(In a (delta_usr from mid tr' addrs_usr)).
    {
      unfold is_complete_strategy in H_complete_strategy.
      destruct_and_split.
      specialize(H8 mid to tr' a H5).
      eauto.
    }
    assert(stratDrive from delta_usr addrs_usr mid tr' to tr'').
    {
      unfold stratDrive.
      exists a , H4, H5.
      split.
      eauto.
      eauto.
    }
    eapply ISU_Step in H8;eauto.
    assert (multiStratDrive delta_env addrs_env from to tr'' to tr'' 0).
    eapply MS_Refl.
    eapply ISE_Step in H9;eauto.
  Qed.

      Lemma BL_implies_SL_with_empty_env_and_complete_user:
      forall delta_usr delta_env addrs_usr addrs_env c s0,
        is_init_state c caddr s0 ->
        is_empty_strat delta_env addrs_env->
        is_complete_strategy delta_usr addrs_usr c s0->
        strat_liquidity delta_usr addrs_usr delta_env addrs_env caddr c s0 ->
        base_liquidity c caddr s0.
    Proof.
      intros * H_init H_empty H_complete H_liquidity.
      unfold base_liquidity.
      intros.
      assert(trace(s0,s0)).
      {
        eapply clnil.
      }
      unfold readyToStepState in H4.
      destruct H4 as [Htr_reachable Hqueue].
      assert(H':transition_reachable c caddr s0 s) by eauto.
      eapply (transition_reachable_can_Inter_usr_all s0 s X c delta_usr delta_env)in H';eauto.
      destruct H'.
      unfold strat_liquidity in H_liquidity.
      assert(Hwell : wellDefinedSystem delta_usr addrs_usr delta_env addrs_env caddr c s0).
      {
        unfold wellDefinedSystem.
        split.
        eapply delta_all_is_wellStrat;eauto.
        split.
        eapply delta_empty_is_wellStrat;eauto.
        split.
        
        eapply is_delta_empty_max_succ;eauto.
        eauto.
      }
      specialize(H_liquidity Hwell X s x).
      rename X into tr_s0.
      rename x into tr_s.
      unfold isReachableUnderInterleavedExecution in H_liquidity.
      specialize(H_liquidity H4).
      decompose_exists.
      assert(UserLiquidatesNSteps delta_usr addrs_usr delta_env addrs_env caddr s0
      s tr_s x x0) by eauto.
      eapply UserLiquidatesNSteps_can_reachable_via in H5;eauto.
      eapply UserLiquidatesNSteps_can_liquid in H_liquidity;eauto;eauto.
      exists x.
      unfold reachable_via  in H5.
      destruct_and_split.
      eauto.
      lia.
      eapply delta_all_is_wellStrat;eauto.
      eapply delta_empty_is_wellStrat;eauto.
      eapply delta_all_is_wellStrat;eauto.
      eapply delta_empty_is_wellStrat;eauto.
    Qed.

  Lemma SL_implies_BL_with_empty_env_and_complete_user:
    forall delta_usr delta_env addrs_usr addrs_env c s0,
      is_empty_strat delta_env addrs_env ->
      is_complete_strategy delta_usr addrs_usr c s0 ->
      base_liquidity c caddr s0 ->
      strat_liquidity delta_usr addrs_usr delta_env addrs_env caddr c s0.
  Proof.
      intros * Henv_empty Husr_complete Hbase_liq.
      unfold base_liquidity in Hbase_liq.
      unfold strat_liquidity.
      intros.
      rename H3 into Hwell_sys.
      rename tr into tr_s0_s0.
      rename tr' into tr_s0_s'.
      rename H4 into H_interleaved.
      decompose_wellDefinedSystem Hwell_sys.
      specialize(Hbase_liq s' H_init).
      assert(Hready_state_s':readyToStepState c caddr s0 s' ).
      {
        unfold readyToStepState.
        split.
        assert(transition_reachable c caddr s0 s').
        {
        unfold transition_reachable.
        split.
        eauto.
        econstructor.
        eauto.
        }
        eauto.
        assert(transition_reachable c caddr s0 s').
        {
          unfold transition_reachable.
          split.
          eauto.
          econstructor.
          eauto.
        }
        eapply (transition_reachable_readyToStepState s0 s' c) in H3;eauto.
        unfold readyToStepState in H3.
        destruct_and_split.
        eauto.
      }
      specialize (Hbase_liq Hready_state_s').
      destruct Hbase_liq as [s'' [H_reach H_s''_funds]].
      assert(Hvia_s'_s' : reachable_via c caddr s0 s' s').
      {
        unfold readyToStepState in Hready_state_s'.
        destruct_and_split.
        econstructor;eauto.
        econstructor;eauto.
        eapply clnil.
      }
      assert(H_t : reachable_via c caddr s0 s' s'').
      {
        econstructor;eauto.
      }
      unfold reachable_via in H_t.
      destruct H_t as [Hrc_s' [tr_s'_s'']].
      assert(tr_s0_s'' : trace(s0,s'')).
      {
        eapply (clist_app tr_s0_s' tr_s'_s'').
      }
      assert(traux_s'_s'' : aux_trace s' s'').
      {
        eapply cl_to_pt_lm.
        eauto.
      }
      induction traux_s'_s''.
      (* - exists (time_speed + time_speed). *)
      -  exists p.
        exists tr_s0_s'.
        eapply ULM_Base;eauto.
      - destruct ((funds mid caddr =? 0)%Z) eqn:H_mid_funds;propify.
        + 
          exists mid.
          assert(tl : TransitionStep from mid) by eauto.
          decompose_TransitionStep tl.
          * set(tr_s0_mid:= snoc tr_s0_s' (step_trans a Hcall_to_caddr Htrans)).
            exists (tr_s0_mid).
            eapply (ULM_Step delta_usr addrs_usr delta_env addrs_env caddr s0 from tr_s0_s' mid mid (snoc tr_s0_s' (step_trans a Hcall_to_caddr Htrans)) tr_s0_mid) ;eauto;try lia.
            **  econstructor;eauto.
                exists Hcall_to_caddr, Htrans.
                split.
                unfold is_complete_strategy in Husr_complete.
                destruct Husr_complete as [Hwell_usr Hact_in].
                specialize(Hact_in from mid tr_s0_s' a Htrans).
                eauto.
                eauto.
            **  eapply EPM_Base.
                eauto.
        + assert(H_mid_funds_gt_zero : (funds mid caddr > 0)%Z ).
          {
            assert(tr_s0_mid :trace(s0,mid)) by eapply (snoc tr_s0_s' l).
            assert (H_t:is_init_state c caddr s0) by eauto.
            decompose_is_init_state H_init.
            assert(tr_s0 : reachable s0) by eauto.
            destruct tr_s0 as [tr_s0].
            assert(Hrc_mid : reachable mid).
            {
              eapply ttrace_with_trace in tr_s0_mid;eauto.
              econstructor;eauto.
              eapply (clist_app tr_s0 tr_s0_mid).
            }
            assert(H_fund_non_neg : (funds mid caddr >= 0)%Z).
            {
              eapply reachable_funds_nonnegative;eauto.
            }
            lia.
          }
          assert(tr_mid_to:trace(mid,to)).
          {
            eapply pt_to_cl_lm.
            eauto.
          }
          assert(tr_s0_mid : trace(s0,mid)) by eapply (snoc tr_s0_s' l).
          assert(step_from_mid : TransitionStep from mid) by eauto.
          assert(Hvia_mid_to : reachable_via c caddr s0 mid to).
          {
            unfold reachable_via in Hvia_s'_s'.
            destruct_and_split.
            destruct H4 as [tr_s_from].
            assert(tr_s_mid:trace(from,mid)).
            {
              eapply (snoc tr_s_from step_from_mid).
            }
            econstructor.
            econstructor.
            eauto.
            eauto.
            eauto.
          }
          assert(tr_s0_to : trace(s0,to)).
          {
            eapply (clist_app tr_s0_mid tr_mid_to).
          }
          assert(Hready_mid : readyToStepState c caddr s0 mid).
          {
            eapply transition_reachable_readyToStepState;eauto.
          }
          assert(tl:TransitionStep from mid) by eauto.
          decompose_TransitionStep tl.
          * set(sn_tr_s0_mid:= snoc tr_s0_s' (step_trans a Hcall_to_caddr Htrans)).
            assert(Hinter:interleavedExecution delta_usr addrs_usr delta_env addrs_env s0 s0 tr_s0_s0 Tenv mid sn_tr_s0_mid).
            {
              eapply (ISU_Step delta_usr addrs_usr delta_env addrs_env s0 s0 tr_s0_s0 from mid tr_s0_s' sn_tr_s0_mid).
              intuition.
              unfold stratDrive.
              exists a,Hcall_to_caddr, Htrans.
              split.

              unfold is_complete_strategy in Husr_complete.
              destruct_and_split.
              specialize(H4 from mid tr_s0_s' a Htrans).
              destruct_and_split.
              eauto.
              eauto.
            }
            assert(His_r_inter:isReachableUnderInterleavedExecution delta_usr delta_env addrs_usr
            addrs_env s0 tr_s0_s0 mid sn_tr_s0_mid).
            {
              unfold isReachableUnderInterleavedExecution.
              eauto.
              assert(multiStratDrive delta_env addrs_env s0 mid sn_tr_s0_mid mid sn_tr_s0_mid 0) by eapply MS_Refl.
              eapply ISE_Step;eauto.
              (* eapply (empty_strat_passive s0 mid sn_tr_s0_mid)  in Henv_empty.
              unfold passive_delta in Henv_empty.
              rewrite  Henv_empty.
              intuition. *)
            }
            assert(Hvia_mid_mid : reachable_via c caddr s0 mid mid).
            {
              econstructor.
              eauto.
              econstructor.
              apply clnil.
            }
            assert(Htc_mid: transition_reachable c caddr s0 mid).
            {
              econstructor;eauto.
            }
            assert(Hihb_mid_to:inhabited (trace( mid, to))) by eauto.
            specialize(IHtraux_s'_s'' Hihb_mid_to H_s''_funds sn_tr_s0_mid His_r_inter Hready_mid Hvia_mid_mid Htc_mid tr_mid_to tr_s0_to).
            decompose_exists.
            rename x0 into x1.
            rename x into x0.
            
            (* exists (n+1). *)
            exists x0, x1.
            rename tr_s0_s' into tr_s0_from.
            eapply (ULM_Step delta_usr addrs_usr delta_env addrs_env caddr s0 from tr_s0_from mid x0 (snoc tr_s0_from (step_trans a Hcall_to_caddr Htrans)) x1) ;eauto;try lia.
            unfold stratDrive.
            exists a,Hcall_to_caddr, Htrans.
            intuition.
            unfold is_complete_strategy  in Husr_complete.
            destruct Husr_complete.
            specialize(H4 from mid tr_s0_from a Htrans).
            destruct_and_split.
            eauto.
            eauto.
            eapply EPM_Step.
            eauto.
            intros.
            pose proof H3.
            eapply multiSuccTrace_delta_empty_refl_multr in H3;eauto.
            destruct_and_split.
            eapply multiStratSucc_n_zero_s_eq in H4;eauto.
            destruct_and_split.
          subst.
          inversion H6.
          eauto.
            
  Qed.
     
  Lemma SL_equiv_BL_with_empty_env_and_complete_user:
    forall delta_usr delta_env addrs_usr addrs_env c s0,
      is_init_state c caddr s0 ->
      is_empty_strat delta_env addrs_env ->
      is_complete_strategy delta_usr addrs_usr c s0 ->
      base_liquidity c caddr s0 <->
      strat_liquidity delta_usr addrs_usr delta_env addrs_env caddr c s0.
  Proof.
    intros.
    split.
    intros.
    eapply SL_implies_BL_with_empty_env_and_complete_user;eauto.
    intros.
    eapply BL_implies_SL_with_empty_env_and_complete_user;eauto.
  Qed.


End equiv.