Require Import Blockchain.
Require Import Serializable.
Require Import RecordUpdate.
Require Import Automation.
Require Import ResultMonad.
Require Import ChainedList.
Require Import StratModel.
From Coq Require Import List.
From Coq Require Import ZArith.
From Coq Require Import Lia.
Import RecordSetNotations.
Import ListNotations.

Section equiv.
  
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

  Context {Setup Msg State Error : Type}
          `{Serializable Setup}
          `{Serializable Msg}
          `{Serializable State}
          `{Serializable Error}.
    
  Variable miner_address : Address.

  Hypothesis miner_always_eoa : address_is_contract miner_address = false.

  
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
    - unfold stratDrive in H3.
      do 4 destruct H3.
      unfold is_empty_strat in H_empty.
      specialize(H_empty s0 s' tr').
      rewrite H_empty in H3.
      inversion H3.
  Qed.

  Lemma multiSuccTrace_delta_empty_refl_multr_end :
    forall (s0 s : ChainState) (tr : trace(s0,s)) (s' : ChainState) (tr' : trace(s0 ,s')) delta addrs n,
      is_empty_strat miner_address delta addrs ->
      multiStratDrive  miner_address delta addrs s0 s tr s' tr' n ->
      n = 0 /\ 
      multiStratDrive miner_address delta addrs s0 s' tr' s' tr' n /\ 
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

   Lemma transition_reachable_can_Inter_usr_all:
      forall s0 s (tr:trace(s0,s0)) c caddr delta_usr delta_env addrs_usr addrs_env,
        is_complete_strategy miner_address addrs_usr delta_usr  c caddr s0->
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
      specialize(IHtrace tr H_complete_strategy init_bstate  H3 init_bstate).
      destruct IHtrace as [tr' IHtrace].
      pose proof l.
      inversion X.
      * set(tr'' := snoc tr' (step_trans miner_address a H4 H5)).
        exists tr''.
        pose proof H4.
        (* assert(delta_env from mid tr' addrs_env = [wait_action_vo]).
        {
          eauto.
        } *)
        assert(In a (delta_usr from mid tr')).
        {
          unfold is_complete_strategy in H_complete_strategy.
          destruct_and_split.
          specialize(H_complete_strategy mid to tr' a H5).
          eauto.
        }
        assert(stratDrive  miner_address addrs_usr delta_usr from mid tr' to tr'').
        {
          unfold stratDrive.
          exists a , H4, H5.
          split.
          eauto.
          eauto.
        }
        eapply ISU_Step in H8;eauto.
        assert (multiStratDrive miner_address addrs_env delta_env  from to tr'' to tr'' 0).
        eapply MS_Refl.
        eapply ISE_Step in H9;eauto.
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
      specialize(H_liquidity H5).
      decompose_exists.
      assert(UserLiquidatesNSteps miner_address addrs_usr delta_usr addrs_env delta_env caddr s0
      s tr_s) by eauto.
      eapply UserLiquidatesNSteps_can_reachable_via in H6;eauto.
      destruct H6.
      exists x.
      unfold reachable_via  in H6.
      destruct_and_split.
      eauto.
      lia.
    Qed.

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
      rename H3 into H_init.
      rename tr into tr_s0_s0.
      rename tr' into tr_s0_s'.
      rename H4 into H_interleaved.
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
        unfold transition_reachable in H3.
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
      forall delta_usr delta_env addrs_usr addrs_env c caddr s0,
        is_init_state c caddr s0 ->
        is_empty_strat miner_address addrs_env delta_env  ->
        is_complete_strategy miner_address addrs_usr delta_usr  c caddr s0 ->
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

End equiv.