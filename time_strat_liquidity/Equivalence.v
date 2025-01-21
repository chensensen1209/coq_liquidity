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
Require Import TimeStratModel.
From Coq Require Import List.
From Coq Require Import Bool.
From Coq Require Import ZArith.
From Coq Require Import Arith.
From Coq Require Import String.
From Coq Require Import Lia.
Import RecordSetNotations.
From Coq Require Import Permutation.
Import ListNotations.

Section Equiv.

Context {BaseTypes : ChainBase}.
Variable miner_address : Address.
Hypothesis miner_always_eoa : address_is_contract miner_address = false.
Global Definition miner_reward := 10%Z.

Notation "trace( from , to )" := (TransitionTrace miner_address from to)(at level 10).

    
Lemma multiSuccTrace_delta_empty_refl_multr :
    forall (s0 s : ChainState) (tr : trace(s0,s)) (s' : ChainState) (tr' : trace(s0 ,s')) delta addrs n,
      is_empty_strat miner_address delta addrs ->
      multiStratDrive miner_address delta addrs s0 s tr s' tr' n ->
      n = 0 /\ multiStratDrive miner_address delta addrs s0 s tr s tr n.
Proof.
  intros s0 s tr s' tr' delta addrs n H_empty H_multi.
  induction H_multi;try lia;eauto.
  - split.
    eauto.
    apply MS_Refl.
  - unfold stratDrive in H.
    do 4 destruct H.
    unfold is_empty_strat in H_empty.
    specialize(H_empty s0 s' tr').
    rewrite H_empty in H.
    simpl in H.
    destruct H;try congruence.
    pose proof x0.
    rewrite <- H in H1.
    assert (is_wait_act (wait_forever_action miner_address)= true).
    {
      eapply wait_forever_action_instance_is_wait_act;eauto.
    }
    eapply wait_action_not_call_act in H2.
    congruence.
    inversion H.
Qed.

Lemma transition_reachable_can_Inter_usr_all:
  forall s0 s (tr:trace(s0,s0)) c caddr delta_usr delta_env addrs_usr addrs_env,
    is_complete_strategy miner_address addrs_usr delta_usr c caddr s0->
    is_empty_strat miner_address addrs_env delta_env  ->
    is_init_state c caddr s0  ->
    transition_reachable miner_address c caddr s0 s ->
    exists (trace:trace(s0,s)),
      interleavedExecution miner_address addrs_usr delta_usr addrs_env delta_env  s0 s0 tr Tusr s trace.
Proof.
  intros s0 s tr c caddr delta_usr delta_env addrs_usr addrs_env
  H_complete_strategy H_empty_delta H_init_state H_transition_reachable.
  assert(H_temp: transition_reachable miner_address c caddr s0 s) by eauto.
  decompose_transition_reachable H_temp.
  induction trace.
  + exists tr.
    eapply IS_Refl.
  + assert (transition_reachable miner_address c caddr from mid).
    {
      econstructor;eauto.
    }
    specialize(IHtrace  tr H_complete_strategy init_bstate  H init_bstate).
    destruct IHtrace as [tr' IHtrace].
    pose proof l.
    inversion X.
    * set(tr'' := snoc tr' (step_trans miner_address a H0 H1)).
      exists tr''.
      pose proof H1.
      assert(In a (packe miner_address (delta_usr from mid tr'))).
      {
        unfold is_complete_strategy in H_complete_strategy.
        destruct_and_split.
        specialize(H_complete_strategy mid to tr' a H2).
        eauto.
      }
      assert(stratDrive  miner_address addrs_usr delta_usr from mid tr' to tr'').
      {
        unfold stratDrive.
        exists a , H0, H1.
        split.
        eauto.
        eauto.
      }
      eapply ISU_Step in H4;eauto.
      assert (multiStratDrive miner_address addrs_env delta_env  from to tr'' to tr'' 0).
      eapply MS_Refl.
      eapply ISE_Step in H5;eauto.
    * set(tr'' := snoc tr' (step_time miner_address a H0 H1)).
      exists tr''.
      pose proof H1.
      assert((packe miner_address (delta_env from mid tr' )) = [wait_forever_action miner_address]).
      {
        unfold is_empty_strat in H_empty_delta.
        specialize (H_empty_delta from mid tr').
        rewrite H_empty_delta.
        simpl.
        eauto.
      }
      assert(timeDrive miner_address from mid tr' a to tr'').
      {
        unfold timeDrive.
        exists H0, H1.
        split.
      }
      eapply (IS_Wait_Step_Once miner_address addrs_usr delta_usr addrs_env
      delta_env from from tr Tusr mid tr' to tr'' a (wait_forever_action miner_address)) in IHtrace as Hist;eauto.
      eapply (ISE_Turn_Step miner_address addrs_usr delta_usr addrs_env
      delta_env from from tr to tr'' (wait_forever_action miner_address) );eauto.
      eapply wait_forever_action_instance_is_wait_act;eauto.
      unfold is_empty_strat in H_empty_delta.
      specialize (H_empty_delta from to tr'').
      rewrite H_empty_delta.
      simpl.
      eauto.
      eapply normal_wait_action_is_wait_act;eauto.
      eapply wait_forever_action_instance_is_wait_act;eauto.
      unfold is_empty_strat in H_empty_delta.
      rewrite H3;eauto;intuition.
      assert (is_normal_wait_act (generate_new_wait_act miner_address a (wait_forever_action miner_address)) =
      true).
      {
        unfold generate_new_wait_act .
        eapply normal_wait_action_is_wait_act in H0 as Ha.
        rewrite Ha.
        specialize( wait_forever_action_instance_is_wait_act ) as Hfa.
        rewrite Hfa.
        eapply is_normal_act_forward_time_gt_zero in H0 as Hatime.
        destruct (get_wait_time a) eqn : He;try congruence;try lia.
        assert (is_forever_wait_act (wait_forever_action miner_address) = true).
        {
          eapply wait_forever_action_is_wait_forever_act;eauto.
        }
        eapply (is_forever_wait_act_forward_time_eq_zero (wait_forever_action miner_address)) in H5 as Hfatime.
        destruct (get_wait_time (wait_forever_action miner_address)).
        eauto.
        lia.
      }
      eauto.
      assert ((generate_new_wait_act miner_address a (wait_forever_action miner_address)) = a).
      {
        unfold generate_new_wait_act .
        eapply normal_wait_action_is_wait_act in H0 as Ha.
        rewrite Ha.
        specialize( wait_forever_action_instance_is_wait_act ) as Hfa.
        rewrite Hfa.
        eapply is_normal_act_forward_time_gt_zero in H0 as Hatime.
        destruct (get_wait_time a) eqn : He;try congruence;try lia.
        assert (is_forever_wait_act (wait_forever_action miner_address)  = true).
        {
          eapply wait_forever_action_is_wait_forever_act;eauto.
        }
        eapply (is_forever_wait_act_forward_time_eq_zero (wait_forever_action miner_address)) in H5 as Hfatime.
        destruct (get_wait_time (wait_forever_action miner_address)).
        eauto.
        lia.
      }
      rewrite H5.
      eauto.
Qed.

Lemma BL_implies_SL_with_empty_env_and_complete_user:
  forall delta_usr delta_env addrs_usr addrs_env c caddr s0,
    is_init_state c caddr s0 ->
    is_empty_strat miner_address addrs_env delta_env ->
    is_complete_strategy miner_address addrs_usr delta_usr  c caddr s0->
    strat_liquidity miner_address addrs_usr delta_usr addrs_env delta_env  c caddr s0 ->
    base_liquidity miner_address c caddr s0.
Proof.
  intros * H_init H_empty H_complete H_liquidity.
  unfold base_liquidity.
  intros.
  assert(trace(s0,s0)).
  {
    eapply clnil.
  }
  assert(H':transition_reachable miner_address c caddr s0 s) by eauto.
  eapply (transition_reachable_can_Inter_usr_all s0 s X c caddr delta_usr delta_env)in H';eauto.
  destruct H'.
  unfold strat_liquidity in H_liquidity.
  pose proof H_init as Hwell.
  specialize(H_liquidity Hwell X s x).
  rename X into tr_s0.
  rename x into tr_s.
  specialize(H_liquidity H1).
  decompose_exists.
  assert(UserLiquidatesNSteps miner_address addrs_usr delta_usr addrs_env delta_env caddr s0
  s tr_s) by eauto.
  eapply UserLiquidatesNSteps_can_reachable_via in H2;eauto.
  destruct H2.
  exists x.
  unfold reachable_via  in H2.
  destruct_and_split.
  eauto.
  lia.
Qed.

Ltac decompose_TransitionStep H :=
  inversion H as [a Hcall_to_caddr Htrans | a Hnormal_wait Htrans];
  subst;
  clear H.

Lemma SL_implies_BL_with_empty_env_and_complete_user:
  forall delta_usr delta_env addrs_usr addrs_env c caddr s0,
    is_empty_strat miner_address addrs_env delta_env  ->
    is_complete_strategy miner_address addrs_usr delta_usr  c caddr s0 ->
    base_liquidity miner_address c caddr s0 ->
    strat_liquidity miner_address addrs_usr delta_usr addrs_env delta_env  c caddr s0.
Proof.
  intros * Henv_empty Husr_complete Hbase_liq.
  unfold base_liquidity in Hbase_liq.
  unfold strat_liquidity.
  intros.
  rename H into H_init.
  rename tr into tr_s0_s0.
  rename tr' into tr_s0_s'.
  rename H0 into H_interleaved.
  specialize(Hbase_liq s' H_init).
  assert(Hready_state_s':transition_reachable miner_address c caddr s0 s' ).
  {
    unfold transition_reachable.
    split.
    assert(transition_reachable miner_address c caddr s0 s').
    {
    unfold transition_reachable.
    split.
    eauto.
    econstructor.
    eauto.
    }
    eauto.
    assert(transition_reachable miner_address c caddr s0 s').
    {
      unfold transition_reachable.
      split.
      eauto.
      econstructor.
      eauto.
    }
    unfold transition_reachable in H.
    destruct_and_split.
    eauto.
  }
  specialize (Hbase_liq Hready_state_s').
  destruct Hbase_liq as [s'' [H_reach H_s''_funds]].
  assert(Hvia_s'_s' : reachable_via miner_address c caddr s0 s' s').
  {
    unfold transition_reachable in Hready_state_s'.
    destruct_and_split.
    econstructor;eauto.
    econstructor;eauto.
    econstructor;eauto.
    eapply clnil.
  }
  assert(H_t : reachable_via miner_address c caddr s0 s' s'').
  {
    econstructor;eauto.
  }
  unfold reachable_via in H_t.
  destruct H_t as [Hrc_s' [tr_s'_s'']].
  assert(tr_s0_s'' : trace(s0,s'')).
  {
    eapply (clist_app tr_s0_s' tr_s'_s'').
  }
  assert(traux_s'_s'' : aux_trace miner_address s' s'').
  {
    eapply cl_to_pt_lm.
    eauto.
  }
  induction traux_s'_s''.
  - 
    eapply ULM_Base;eauto.
  - destruct ((funds mid caddr =? 0)%Z) eqn:H_mid_funds;propify.
    + 
      assert(tl : TransitionStep miner_address from mid) by eauto.
      decompose_TransitionStep tl.
      * set(tr_s0_mid:= snoc tr_s0_s' (step_trans miner_address a Hcall_to_caddr Htrans)).
        eapply (ULM_Step miner_address addrs_usr delta_usr addrs_env delta_env caddr s0 from tr_s0_s' mid  (snoc tr_s0_s' (step_trans miner_address a Hcall_to_caddr Htrans)) ) ;eauto;try lia.
        **  econstructor;eauto.
        **  eapply EPM_Base.
            eauto.
      * set(tr_s0_mid:= snoc tr_s0_s' (step_time miner_address a Hnormal_wait Htrans)).
        pose proof Henv_empty as Ht.
        unfold is_empty_strat in Ht.
        specialize (Ht s0 from tr_s0_s').
        eapply (ULM_Time miner_address addrs_usr delta_usr addrs_env delta_env  caddr s0 from tr_s0_s' mid (snoc tr_s0_s' (step_time miner_address a Hnormal_wait Htrans))a (wait_forever_action miner_address)).
        **  eapply normal_wait_action_is_wait_act;eauto.
        **  unfold is_complete_strategy in Husr_complete.
            specialize(Husr_complete from mid tr_s0_s' a Htrans).
            eauto.
        **  eapply wait_forever_action_instance_is_wait_act.
        **  rewrite Ht.
            simpl.
            intuition.
        **  assert (generate_new_wait_act miner_address a (wait_forever_action miner_address) = a).
            {
              eapply generate_new_wait_act_forever_normal.
              eauto.
              eapply wait_forever_action_is_wait_forever_act.
            }
            rewrite H.
            eauto.
        **  assert (generate_new_wait_act miner_address a (wait_forever_action miner_address) = a).
            {
              eapply generate_new_wait_act_forever_normal.
              eauto.
              eapply wait_forever_action_is_wait_forever_act.
            }
            rewrite H.
            unfold timeDrive .
            exists Hnormal_wait, Htrans.
            eauto.
        **  eapply EPM_Base.
            eauto.
    + assert(H_mid_funds_gt_zero : (funds mid caddr > 0)%Z ).
      {
        assert(tr_s0_mid :trace(s0,mid)) by eapply (snoc tr_s0_s' l).
        assert (H_t:is_init_state c caddr s0) by eauto.

        decompose_is_init_state H_t.
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
      assert(step_from_mid : TransitionStep miner_address from mid) by eauto.
      assert(Hvia_mid_to : reachable_via miner_address c caddr s0 mid to).
      {
        unfold reachable_via in Hvia_s'_s'.
        destruct_and_split.
        destruct H0 as [tr_s_from].
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
      assert(Hready_mid : transition_reachable miner_address c caddr s0 mid).
      {
        unfold reachable_via  in Hvia_mid_to.
        eauto.
        econstructor;eauto.
      }
      assert(tl:TransitionStep miner_address from mid) by eauto.
      decompose_TransitionStep tl.
      * set(sn_tr_s0_mid:= snoc tr_s0_s' (step_trans miner_address a Hcall_to_caddr Htrans)).
        assert(Hinter:interleavedExecution miner_address addrs_usr delta_usr addrs_env delta_env  s0 s0 tr_s0_s0 Tenv mid sn_tr_s0_mid).
        {
          eapply (ISU_Step miner_address addrs_usr delta_usr addrs_env delta_env  s0 s0 tr_s0_s0 from mid tr_s0_s' sn_tr_s0_mid).
          intuition.
          unfold stratDrive.
          exists a,Hcall_to_caddr, Htrans.
          split.
          unfold is_complete_strategy in Husr_complete.
          destruct_and_split.
          specialize(Husr_complete from mid tr_s0_s' a Htrans).
          destruct_and_split.
          eauto.
          eauto.
        }
        assert(His_r_inter:interleavedExecution miner_address addrs_usr delta_usr
        addrs_env delta_env s0 s0 tr_s0_s0 Tusr mid sn_tr_s0_mid).
        {
          assert(multiStratDrive miner_address addrs_env delta_env  s0 mid sn_tr_s0_mid mid sn_tr_s0_mid 0) by eapply MS_Refl.
          eapply ISE_Step;eauto.
        }
        assert(Hvia_mid_mid : reachable_via miner_address c caddr s0 mid mid).
        {
          econstructor.
          eauto.
          econstructor.
          apply clnil.
        }
        assert(Htc_mid: transition_reachable miner_address c caddr s0 mid).
        {
          econstructor;eauto.
        }
        assert(Hihb_mid_to:inhabited (trace( mid, to))) by eauto.
        specialize(IHtraux_s'_s'' Hihb_mid_to H_s''_funds sn_tr_s0_mid His_r_inter Hready_mid Hvia_mid_mid Htc_mid tr_mid_to tr_s0_to).
        decompose_exists.
        rename tr_s0_s' into tr_s0_from.
        eapply (ULM_Step miner_address addrs_usr delta_usr addrs_env delta_env caddr s0 from tr_s0_from mid (snoc tr_s0_from (step_trans miner_address a Hcall_to_caddr Htrans))) ;eauto;try lia.
        unfold stratDrive.
        exists a,Hcall_to_caddr, Htrans.
        intuition.
        unfold is_complete_strategy  in Husr_complete.
        (* destruct Husr_complete. *)
        specialize(Husr_complete from mid tr_s0_from a Htrans).
        destruct_and_split.
        eauto.
        eauto.
        eapply EPM_Step.
        eauto.
        intros.
        pose proof H.
        eapply multiSuccTrace_delta_empty_refl_multr in H;eauto.
        destruct_and_split.
        eapply multiStratSucc_n_zero_s_eq in H0;eauto.
        destruct_and_split.
        subst.
        inversion H2.
        eauto.
      * set(sn_tr_s0_mid:= snoc tr_s0_s' (step_time miner_address a Hnormal_wait Htrans)).
        assert(Hinter:interleavedExecution miner_address addrs_usr delta_usr addrs_env delta_env  s0 s0 tr_s0_s0 Tenv mid sn_tr_s0_mid).
        {
          eapply (IS_Wait_Step_Once miner_address addrs_usr delta_usr addrs_env delta_env  s0 s0 tr_s0_s0 Tusr from  tr_s0_s' mid sn_tr_s0_mid a (wait_forever_action miner_address)).
          
          eauto.
          eapply normal_wait_action_is_wait_act;eauto.
          pose proof Husr_complete.
          unfold is_complete_strategy in H.
          destruct_and_split.
          specialize(H from mid tr_s0_s' a Htrans).
          eauto.
          eapply wait_forever_action_instance_is_wait_act;eauto.
          pose proof Henv_empty.
          unfold is_empty_strat in H.
          specialize (H s0 from tr_s0_s').
          rewrite H.
          simpl.
          eauto.
          assert (generate_new_wait_act miner_address a (wait_forever_action  miner_address)= a).
          {
            eapply generate_new_wait_act_forever_normal.
            eauto.
            eapply wait_forever_action_is_wait_forever_act.
          }
          rewrite H.
          eauto.
          assert (generate_new_wait_act miner_address a (wait_forever_action miner_address) = a).
          {
            eapply generate_new_wait_act_forever_normal.
            eauto.
            eapply wait_forever_action_is_wait_forever_act.
          }
          rewrite H.
          unfold timeDrive.
          exists Hnormal_wait,Htrans.
          eauto.
        }
        assert(His_r_inter:interleavedExecution miner_address addrs_usr delta_usr
        addrs_env delta_env s0 s0 tr_s0_s0 Tusr mid sn_tr_s0_mid).
        {
          assert(multiStratDrive miner_address addrs_env delta_env  s0 mid sn_tr_s0_mid mid sn_tr_s0_mid 0) by eapply MS_Refl.
          eapply ISE_Step;eauto.
        }
        assert(Hvia_mid_mid : reachable_via miner_address c caddr s0 mid mid).
        {
          econstructor.
          eauto.
          econstructor.
          apply clnil.
        }
        assert(Htc_mid: transition_reachable miner_address c caddr s0 mid).
        {
          econstructor;eauto.
        }
        assert(Hihb_mid_to:inhabited (trace( mid, to))) by eauto.
        specialize(IHtraux_s'_s'' Hihb_mid_to H_s''_funds sn_tr_s0_mid His_r_inter Hready_mid Hvia_mid_mid Htc_mid tr_mid_to tr_s0_to).
        decompose_exists.
        rename tr_s0_s' into tr_s0_from.
        eapply (ULM_Time miner_address addrs_usr delta_usr addrs_env delta_env caddr s0 from tr_s0_from mid (snoc tr_s0_from (step_time miner_address a Hnormal_wait Htrans)) a (wait_forever_action miner_address)).
        eapply normal_wait_action_is_wait_act;eauto.
        unfold is_complete_strategy  in Husr_complete.
        (* destruct Husr_complete. *)
        specialize(Husr_complete from mid tr_s0_from a Htrans).
        destruct_and_split.
        eauto.
        eapply wait_forever_action_instance_is_wait_act;eauto.
        pose proof Henv_empty.
        unfold is_empty_strat in H.
        specialize(H s0 from tr_s0_from).
        rewrite H.
        simpl.
        intuition.
        assert (generate_new_wait_act miner_address a (wait_forever_action  miner_address )= a).
        {
          eapply generate_new_wait_act_forever_normal.
          eauto.
          eapply wait_forever_action_is_wait_forever_act.
        }
        rewrite H.
        eauto.
        assert (generate_new_wait_act miner_address a (wait_forever_action miner_address) = a).
        {
          eapply generate_new_wait_act_forever_normal.
          eauto.
          eapply wait_forever_action_is_wait_forever_act.
        }
        rewrite H.
        unfold timeDrive.
        exists Hnormal_wait,Htrans.
        eauto.
        eapply EPM_Step.
        eauto.
        intros.
        pose proof H.
        eapply multiSuccTrace_delta_empty_refl_multr in H;eauto.
        destruct_and_split.
        eapply multiStratSucc_n_zero_s_eq in H0;eauto.
        destruct_and_split.
        subst.
        inversion H2.
        eauto.
Qed.

Lemma SL_equiv_BL_with_empty_env_and_complete_user:
  forall delta_usr delta_env addrs_usr addrs_env c caddr s0,
    is_init_state c caddr s0 ->
    is_empty_strat miner_address addrs_env delta_env  ->
    is_complete_strategy miner_address addrs_usr delta_usr c caddr s0 ->
    (base_liquidity miner_address c caddr s0 <->
      strat_liquidity miner_address addrs_usr delta_usr addrs_env delta_env c caddr s0).
Proof.
  intros.
  split.
  intros.
  eapply SL_implies_BL_with_empty_env_and_complete_user;eauto.
  intros.
  eapply BL_implies_SL_with_empty_env_and_complete_user;eauto.
Qed.

End Equiv.