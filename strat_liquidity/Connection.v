
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

Require Import LibTactics. 

Section connection.
  
  Local Open Scope bool.

  Context {AddrSize : N}.
  Context {DepthFirst : bool}.

  Definition Error : Type := nat.
  Definition default_error: Error := 1%nat.

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

  Notation "trace( from , to )" := (TransitionTrace miner_address from to) (at level 10). 

  Lemma multiStratDrive_empty_refl :
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
      do 3 destruct H3. (* 4 -> 3 *) 
      unfold is_empty_strat in H_empty.
      specialize(H_empty s0 s' tr').
      rewrite H_empty in H3.
      destruct H3.
      false. 
  Qed.

  Lemma multiStratDrive_empty_refl_end :
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

  Definition has_all_user_addrs (adrs: list Address) : Prop :=
    forall (a: Address), address_is_contract a = false -> In a adrs. 
  
  Lemma interleaved_execution_reachable_with_complete_and_empty:
    forall s0 s (tr:trace(s0,s0)) c caddr delta_usr delta_env addrs_usr addrs_env,
      has_all_user_addrs addrs_usr -> 
      is_complete_strategy miner_address addrs_usr delta_usr s0 ->  
      is_empty_strat miner_address addrs_env delta_env ->
      is_init_state c caddr s0 -> 
      transition_reachable miner_address c caddr s0 s ->
      exists (trace:trace(s0,s)),
        interleavedExecution miner_address addrs_usr delta_usr addrs_env delta_env  s0 s0 tr Tusr s trace.
  Proof.
    intros s0 s tr c caddr delta_usr delta_env addrs_usr addrs_env
      Hall H_complete_strategy H_empty_delta H_init_state H_transition_reachable.
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
      * set(tr'' := snoc tr' (step_trans miner_address a _ H4 (* H5 *))).
        exists tr''.
        pose proof H4.
        (* assert(delta_env from mid tr' addrs_env = [wait_action_vo]).
             { eauto. } *)
        assert(In a (delta_usr from mid tr')).
        {
          unfold is_complete_strategy in H_complete_strategy.
          assert (Hfrm: act_orig_frms a addrs_usr).
          {
            unfold act_orig_frms.
            lets H__: transition_orig_frm_neq H5; eauto.
            lets H_: transition_frm_usr_addr H5; eauto.
            destruct a.
            destruct act_body; simpl in H5; tryfalse; unfold act_orig_frm.
            {
              simpl in H__. subst.
              exists act_from.
              splits; eauto.
            }
            {
              simpl in H__. subst.
              exists act_from.
              splits; eauto.              
            }
            {
              simpl in H__. subst.
              exists act_from.
              splits; eauto.              
            }
          }
          (* destruct_and_split. *) 
          specialize(H_complete_strategy mid to tr' a _ H5).
          eauto.
        }
        assert(stratDrive  miner_address addrs_usr delta_usr from mid tr' to tr'').
        {
          unfold stratDrive.
          exists a. eexists. eexists H4.
          split.
          eauto.
          eauto.
        }
        eapply ISU_Step in H7;eauto.
        assert (multiStratDrive miner_address addrs_env delta_env  from to tr'' to tr'' 0).
        eapply MS_Refl.
        eapply ISE_Step; eauto.
        (* eapply ISE_Step in H9;eauto. *)
  Qed.

  Lemma BL_implies_SL_with_empty_env_and_complete_user:
    forall delta_usr delta_env addrs_usr addrs_env c caddr s0 phi,
      is_init_state c caddr s0 ->
      is_empty_strat miner_address addrs_env delta_env ->
      has_all_user_addrs addrs_usr -> 
      is_complete_strategy miner_address addrs_usr delta_usr s0 ->
      strategy_aware_liquidity miner_address addrs_usr delta_usr addrs_env delta_env c caddr s0 phi ->
      basic_liquidity miner_address c caddr s0 phi.
  Proof.
    intros * H_init H_empty Hall H_complete H_liquidity.
    unfold basic_liquidity.
    intros.
    assert(trace(s0,s0)).
    {
      eapply clnil.
    }
    assert(H':transition_reachable miner_address c caddr s0 s) by eauto.
    eapply (interleaved_execution_reachable_with_complete_and_empty s0 s X c caddr delta_usr delta_env) in H';eauto.
    destruct H'.
    unfold strategy_aware_liquidity in H_liquidity. 
    pose proof H_init as Hwell.
    specialize(H_liquidity Hwell X s x).
    rename X into tr_s0.
    rename x into tr_s.
    specialize(H_liquidity H5).
    (* decompose_exists. *)
    assert(userLiquidates miner_address addrs_usr delta_usr addrs_env delta_env caddr s0
             s s tr_s phi) by eauto.
    eapply userLiquidates_can_reachable_via in H6;eauto.
    destruct H6.
    exists x.
    unfold reachable_via  in H6.
    destruct_and_split.
    eauto.
    auto.
  Qed.

  Require Import Classical.

  Lemma uliq:
    forall c caddr s0 s' s'' s tr_s0_s' (phi: ChainState -> ChainState -> Prop)
           addrs_usr delta_usr addrs_env delta_env (tr_s0_s0 : trace( s0, s0)),
      is_complete_strategy miner_address addrs_usr delta_usr s0 ->
      is_empty_strat miner_address addrs_env delta_env -> 
      has_all_user_addrs addrs_usr -> 
      is_init_state c caddr s0 -> 
      interleavedExecution miner_address addrs_usr delta_usr addrs_env delta_env s0 s0 tr_s0_s0 Tusr s' tr_s0_s' -> 
      reachable_via miner_address c caddr s0 s' s' -> 
      aux_trace miner_address s' s'' ->
      inhabited (trace( s', s'')) ->
      phi s s'' ->
      userLiquidates miner_address addrs_usr delta_usr addrs_env delta_env caddr s0 s' s
        tr_s0_s' phi.
  Proof.
    intros * Husr_complete Henv_empty Hall H_init H_interleaved.
    introv Hvia_s'_s' traux_s'_s''.
    induction traux_s'_s''; introv H_reach H_s''_funds.
    -
      eapply U_Base;eauto.
    -
      assert (H_mid_funds: phi s mid \/ ~ phi s mid) by apply classic.
      destruct H_mid_funds. 
      + 
        assert(tl : TransitionStep miner_address from mid) by eauto.
        decompose_TransitionStep tl.
        * set(tr_s0_mid := snoc tr_s0_s' (step_trans miner_address a n (* Hcall_to_caddr *) Htrans)).
          eapply (U_Step miner_address addrs_usr delta_usr addrs_env delta_env caddr s0 from s tr_s0_s' phi mid
                    (snoc tr_s0_s' (step_trans miner_address a _ (* Hcall_to_caddr *) Htrans))); eauto; try lia.
          **
            exists a. exists n.
            lets H__: transition_frm_usr_addr Htrans.
            apply Hall in H__.
            lets H_: transition_orig_frm_neq Htrans.
            (* do 2 eexists. *)
            eexists. 
            split; eauto.
            {
              eapply Husr_complete; eauto.
              exists (act_from a).
              split; auto.
              unfolds.
              destruct a; destruct act_body; (* simpl in Hcall_to_caddr;  *)tryfalse.
              { simpl. simpl in H_; subst. split; eauto. }
              { simpl. simpl in H_; subst. split; eauto. }
              { simpl. simpl in H_; subst. split; eauto. }
            }
          ** eapply E_Base.
             eauto.
             
      + assert(H_mid_funds_gt_zero : ~phi s mid) by auto.
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
          destruct H5 as [tr_s_from].
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
        * set(sn_tr_s0_mid := snoc tr_s0_s' (step_trans miner_address a n (* Hcall_to_caddr  *)Htrans)).
          assert(Hinter: interleavedExecution miner_address addrs_usr delta_usr addrs_env delta_env
                           s0 s0 tr_s0_s0 Tenv mid sn_tr_s0_mid). 
          {
            eapply (ISU_Step miner_address addrs_usr delta_usr addrs_env delta_env  s0 s0 tr_s0_s0 from mid tr_s0_s' sn_tr_s0_mid).
            intuition.
            unfold stratDrive.
            exists a n (* Hcall_to_caddr  *)Htrans.
            split; eauto.
            {
              unfold is_complete_strategy in Husr_complete.
              lets H_: transition_frm_usr_addr Htrans.
              apply Hall in H_.
              eapply Husr_complete; eauto.
              lets H__: transition_orig_frm_neq Htrans; eauto.
              unfolds.
              exists (act_from a).
              split; eauto.
              unfolds.
              destruct a; simpl in H__; tryfalse; subst. 
              { simpl; split; auto. } 
            }
          }
          assert(His_r_inter: interleavedExecution miner_address addrs_usr delta_usr
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
          specialize(IHtraux_s'_s'' _ His_r_inter Hvia_mid_mid Hihb_mid_to H_s''_funds).
          decompose_exists.
          rename tr_s0_s' into tr_s0_from.
          eapply (U_Step miner_address addrs_usr delta_usr addrs_env delta_env
                    caddr s0 from s tr_s0_from phi mid
                    (snoc tr_s0_from (step_trans miner_address a _ (* Hcall_to_caddr  *)Htrans)));
            eauto; try lia.
          unfold stratDrive.
          exists a. eexists.
          exists (* Hcall_to_caddr  *)Htrans.
          intuition.
          {
            unfold is_complete_strategy in Husr_complete.
            eapply Husr_complete; eauto.
            lets H_: transition_frm_usr_addr Htrans.
            apply Hall in H_.
            lets H__: transition_orig_frm_neq Htrans.
            unfolds.
            exists (act_from a).
            split; auto.
            unfolds.
            destruct a; simpl in H__; tryfalse; subst.
            { simpl. split; eauto. }
          }
          eapply E_Step.
          eauto.
          intros.
          pose proof H4.
          eapply multiStratDrive_empty_refl in H4;eauto.
          destruct_and_split.
          eapply multiStratSucc_n_zero_s_eq in H5;eauto.
          destruct_and_split.
          subst.
          inversion H7.
          eauto.
  Qed.
  
  Lemma SL_implies_BL_with_empty_env_and_complete_user:
    forall delta_usr delta_env addrs_usr addrs_env c caddr s0 phi,
      is_empty_strat miner_address addrs_env delta_env ->
      has_all_user_addrs addrs_usr -> 
      is_complete_strategy miner_address addrs_usr delta_usr s0 ->
      basic_liquidity miner_address c caddr s0 phi ->
      strategy_aware_liquidity miner_address addrs_usr delta_usr addrs_env delta_env c caddr s0 phi.
  Proof.
    intros * Henv_empty Hall Husr_complete Hbase_liq.
    unfold basic_liquidity in Hbase_liq.
    unfold strategy_aware_liquidity.
    intros.
    rename H3 into H_init.
    rename tr into tr_s0_s0.
    rename tr' into tr_s0_s'.
    rename H4 into H_interleaved.
    specialize(Hbase_liq s' H_init).
    assert(Hready_state_s':transition_reachable miner_address c caddr s0 s').
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

    eapply uliq; eauto.
  Qed. 

  Theorem SL_equiv_BL_with_empty_env_and_complete_user:
    forall delta_usr delta_env addrs_usr addrs_env c caddr s0 phi,
      is_init_state c caddr s0 ->
      has_all_user_addrs addrs_usr ->       
      is_empty_strat miner_address addrs_env delta_env  ->
      is_complete_strategy miner_address addrs_usr delta_usr s0 ->
      (basic_liquidity miner_address c caddr s0 phi <->
         strategy_aware_liquidity miner_address addrs_usr delta_usr addrs_env delta_env c caddr s0 phi).
  Proof.
    intros.
    split.
    intros.
    eapply SL_implies_BL_with_empty_env_and_complete_user;eauto.
    intros.
    eapply BL_implies_SL_with_empty_env_and_complete_user;eauto.
  Qed.

End connection. 
