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

Section Monotonicity.

    Definition addrs_subset (addrs1: list Address) (addrs2 : list Address) :=
      incl addrs1 addrs2.
  
    Definition acts_subset_strict (acts1 acts2 : list Action) : Prop :=
      incl acts1 acts2. 
  
    Definition strat_subset_strict 
      (delta1 : strat) (addrs1 : list Address)
      (delta2 : strat) (addrs2 : list Address) 
      s0: Prop :=
      forall s tr,
          acts_subset_strict
          (delta1 s0 s tr addrs1)
          (delta2 s0 s tr addrs2).
  
  
    Lemma in_empty_false : forall (A : Type) (x : A), ~ In x [].
    Proof.
      intros A x H4.
      inversion H4. (* 空列表中不可能有元素，因此直接矛盾。 *)
    Qed.
  
    Lemma in_nonempty_to_empty_contradiction : forall (A : Type) (a : A) (l : list A),
      (forall x, In x (a :: l) -> In x []) -> False.
    Proof.
      intros A a l H4.
      (* 选择一个具体的元素 a，它在 a :: l 中。 *)
      specialize (H4 a).
      simpl in H4.
      destruct H4.
      eauto.
    Qed.
  
  
    Lemma  strat_subset_strict_no_empty:
      forall (delta1 : strat) (addrs1 : list Address) (delta2 : strat) (addrs2 : list Address) s s' tr',
        strat_subset_strict (delta1 : strat) (addrs1 : list Address) (delta2 : strat) (addrs2 : list Address)  s->
        delta1 s s' tr' addrs1 <> [] ->
        delta2 s s' tr' addrs2 <> [].
    Proof.
      intros * Hsbt_delta H_delta.
      unfold strat_subset_strict in Hsbt_delta.
      specialize(Hsbt_delta s' tr').
      unfold acts_subset_strict in Hsbt_delta.
      destruct (delta1 s s' tr' addrs1) ;try congruence.
      unfold incl in Hsbt_delta.
      intuition.
      rewrite H3 in Hsbt_delta.
      destruct (a :: l ) eqn : Hqu.
      intuition.
      eapply in_nonempty_to_empty_contradiction ;eauto.
    Qed.
  
    Lemma  strat_subset_strict_empty_re:
      forall (delta1 : strat) (addrs1 : list Address) (delta2 : strat) (addrs2 : list Address) s s' tr',
        strat_subset_strict (delta1 : strat) (addrs1 : list Address) (delta2 : strat) (addrs2 : list Address)  s ->
        delta2 s s' tr' addrs2 = [] ->
        delta1 s s' tr' addrs1 = [].
    Proof.
      intros * Hsbt_delta H_delta.
      unfold strat_subset_strict in Hsbt_delta.
      unfold acts_subset_strict in Hsbt_delta.
      specialize(Hsbt_delta s' tr').
      destruct (delta1 s s' tr' addrs1) ;try congruence.
      rewrite H_delta in Hsbt_delta.
      unfold incl in *.
      eapply in_nonempty_to_empty_contradiction in Hsbt_delta.
      inversion Hsbt_delta.
    Qed.
  
  
      Lemma stratDrive_subset:
        forall s0 s s' tr tr' delta_usr1 addrs_usr1 delta_usr2 addrs_usr2,
          strat_subset_strict delta_usr2 addrs_usr2 delta_usr1 addrs_usr1 s0 ->
          stratDrive s0 delta_usr2 addrs_usr2 s tr s' tr' ->
          stratDrive s0 delta_usr1 addrs_usr1 s tr s' tr'.
      Proof.
        unfold stratDrive.
        unfold strat_subset_strict.
        unfold acts_subset_strict.
        intros.
        decompose_exists.
        destruct_and_split. 
        specialize(H3 s tr).
        exists x, x0 , x1.
        split.
        eauto.
        destruct (delta_usr2 s0 s tr addrs_usr2).
        inversion H5.
        eauto.
        eauto.
      Qed.
  
      Lemma multiStratDrive_subset:
        forall s0 s s' tr tr' delta_usr1 addrs_usr1 delta_usr2 addrs_usr2 n,
          strat_subset_strict delta_usr2 addrs_usr2 delta_usr1 addrs_usr1 s0 ->
          multiStratDrive delta_usr2 addrs_usr2 s0 s tr s' tr' n ->
          multiStratDrive delta_usr1 addrs_usr1 s0 s tr s' tr' n.
      Proof.
        intros.
        induction H4.
        - eapply MS_Refl.
        - eapply stratDrive_subset in H5;eauto.
          eapply MS_Step;eauto.
      Qed.
  
  
  
  
      (* 少的能到，多的也能到 *)
      Lemma interleavedExecution_mono_incl_usr_unchanging (delta_usr : strat) (addrs_usr: list Address)  (delta_env1 : strat) (addrs_env1: list Address) (delta_env2 : strat) (addrs_env2: list Address) :
        forall s0 s' c flag tr tr',
          wellDefinedSystem delta_usr addrs_usr delta_env1 addrs_env1 caddr c s0 ->
          wellDefinedSystem delta_usr addrs_usr delta_env2 addrs_env2 caddr c s0 ->
          strat_subset_strict delta_env1 addrs_env1 delta_env2 addrs_env2 s0 ->
          interleavedExecution delta_usr addrs_usr delta_env1 addrs_env1 s0 s0 tr flag s' tr' ->
          interleavedExecution delta_usr addrs_usr delta_env2 addrs_env2 s0 s0 tr flag s' tr'.
      Proof.
        intros * Hwell_sys1 Hwell_sys2 Hsbt_delta Hrc_itv.
        induction Hrc_itv;eauto;try intuition.
        - eapply IS_Refl.
        - eapply ISE_Step;eauto.
          pose proof Hsbt_delta as Hst.
          unfold strat_subset_strict in Hsbt_delta.
          specialize(Hsbt_delta  s' tr').
          unfold acts_subset_strict in Hsbt_delta.
          destruct (delta_env1 s0 s' tr' addrs_env1) eqn : He;try congruence.
          intuition.
          eapply multiStratDrive_subset;eauto.
          eapply multiStratDrive_subset;eauto.
        - eapply ISU_Step;eauto.
      Qed.
  
      Lemma userLiquidatesNSteps_incl_usr_unchanging (delta_usr : strat) (addrs_usr: list Address)  (delta_env1 : strat) (addrs_env1: list Address) (delta_env2 : strat) (addrs_env2: list Address) :
        forall s0 s s' c tr tr',
          wellDefinedSystem delta_usr addrs_usr delta_env1 addrs_env1 caddr c s0 ->
          wellDefinedSystem delta_usr addrs_usr delta_env2 addrs_env2 caddr c s0 ->
          strat_subset_strict delta_env1 addrs_env1 delta_env2 addrs_env2 s0->
          UserLiquidatesNSteps delta_usr addrs_usr delta_env2 addrs_env2 caddr s0 s tr s' tr'->
          UserLiquidatesNSteps delta_usr addrs_usr delta_env1 addrs_env1 caddr s0 s tr s' tr'.
      Proof.
        intros * Hwell_sys1 Hwell_sys2 Hsbt_delta_pro Hrc_itv.
        decompose_wellDefinedSystem Hwell_sys1.
        decompose_wellDefinedSystem Hwell_sys2.
        rename H_finite0 into H_finite2.
        rename H_finite into H_finite1.
        eapply (env_mut delta_usr addrs_usr delta_env2 addrs_env2 caddr s0 
        (fun s tr  s' tr' (_ : envProgress_Mutual delta_usr addrs_usr delta_env2 addrs_env2 caddr s0 s tr s' tr') =>  
        envProgress_Mutual delta_usr addrs_usr delta_env1 addrs_env1 caddr s0 s tr s' tr')
        (fun  s tr s' tr' (_ : UserLiquidatesNSteps delta_usr addrs_usr delta_env2 addrs_env2 caddr  s0 s tr s' tr') => 
        UserLiquidatesNSteps delta_usr addrs_usr delta_env1 addrs_env1 caddr s0 s tr s' tr')
        );intros;subst;eauto.
        - apply EPM_Base. assumption.
        -  
          eapply EPM_Step.
          eauto.
          intros.
          assert (multiStratDrive delta_env2 addrs_env2 s0 s1 tr0 s'0 tr'0 n).
          {
            eapply multiStratDrive_subset;eauto.
          }
          specialize (H3 s'0 tr'0 n).
          eapply H3;eauto.
        - eapply ULM_Base;eauto.
        - eapply ULM_Step;eauto.
  
      Qed.
  
      Lemma userLiquidatesNSteps_incl_usr_unchanging_empty 
        (delta_usr : strat) (addrs_usr: list Address)
        (delta_env1 : strat) (addrs_env1: list Address) 
        (delta_env2 : strat) (addrs_env2: list Address) :
        forall s0 s s' c tr tr',
          wellDefinedSystem delta_usr addrs_usr delta_env1 addrs_env1 caddr c s0 ->
          wellDefinedSystem delta_usr addrs_usr delta_env2 addrs_env2 caddr c s0 ->
          is_empty_strat delta_env1 addrs_env1 ->
          strat_subset_strict delta_env1 addrs_env1 delta_env2 addrs_env2 s0->
          UserLiquidatesNSteps delta_usr addrs_usr delta_env2 addrs_env2 caddr s0 s tr s' tr'->
          UserLiquidatesNSteps delta_usr addrs_usr delta_env1 addrs_env1 caddr s0 s tr s' tr'.
      Proof.
        intros * Hwell_sys1 Hwell_sys2 Hsbt_delta Hrc_itv.
        decompose_wellDefinedSystem Hwell_sys1.
        decompose_wellDefinedSystem Hwell_sys2.
        rename H_finite0 into H_finite2.
        rename H_finite into H_finite1.
        eapply (env_mut delta_usr addrs_usr delta_env2 addrs_env2 caddr s0 
        (fun s tr  s' tr' (_ : envProgress_Mutual delta_usr addrs_usr delta_env2 addrs_env2 caddr s0 s tr s' tr') =>  
        envProgress_Mutual delta_usr addrs_usr delta_env1 addrs_env1 caddr s0 s tr  s' tr')
        (fun  s tr s' tr' (_ : UserLiquidatesNSteps delta_usr addrs_usr delta_env2 addrs_env2 caddr  s0 s tr s' tr') => 
        UserLiquidatesNSteps delta_usr addrs_usr delta_env1 addrs_env1 caddr s0 s tr  s' tr')
        );intros;subst;eauto.
        - apply EPM_Base. assumption.
        - 
          eapply EPM_Step.
          eauto.
          intros.
          assert (multiStratDrive delta_env2 addrs_env2 s0 s1 tr0 s'0 tr'0 n).
          {
            eapply multiStratDrive_subset;eauto.
          }
          specialize (H3 s'0 tr'0 n).
          eapply H3;eauto.
        - eapply ULM_Base;eauto.
        - eapply ULM_Step;eauto.
      Qed.
  
      Lemma usr_liquid_Mono_env_unchanging (delta_usr : strat) (addrs_usr: list Address)  (delta_env1 : strat) (addrs_env1: list Address) (delta_env2 : strat) (addrs_env2: list Address) :
        forall s0 c, 
          wellDefinedSystem delta_usr addrs_usr delta_env1 addrs_env1 caddr c s0 ->
          wellDefinedSystem delta_usr addrs_usr delta_env2 addrs_env2 caddr c s0 ->
          strat_subset_strict delta_env1 addrs_env1 delta_env2 addrs_env2 s0 -> 
          strat_liquidity delta_usr addrs_usr delta_env2 addrs_env2 caddr c s0 ->
          strat_liquidity delta_usr addrs_usr delta_env1 addrs_env1 caddr c s0.
      Proof.
        intros * Hwell_sys1 Hwell_sys2 Hstrat_refines Hliq_delta2.
        unfold strat_liquidity in *.
        intros Hwell_sys * Hrc_itv.
        unfold isReachableUnderInterleavedExecution in Hrc_itv.
        specialize(Hliq_delta2 Hwell_sys2 tr s' tr').
        assert (interleavedExecution delta_usr addrs_usr delta_env2 addrs_env2 s0 s0
        tr Tusr s' tr').
        eapply interleavedExecution_mono_incl_usr_unchanging;eauto.
        unfold isReachableUnderInterleavedExecution in Hliq_delta2.
        specialize (Hliq_delta2 H3).
        decompose_exists.
        exists x, x0.
        eapply userLiquidatesNSteps_incl_usr_unchanging in Hliq_delta2;eauto.
      Qed.
  
      Lemma strat_liquidity_Mono_env_unchanging_empty 
          (delta_usr : strat) (addrs_usr: list Address)  
          (delta_env1 : strat) (addrs_env1: list Address) 
          (delta_env2 : strat) (addrs_env2: list Address) :
        forall s0 c, 
          wellDefinedSystem delta_usr addrs_usr delta_env1 addrs_env1 caddr c s0 ->
          wellDefinedSystem delta_usr addrs_usr delta_env2 addrs_env2 caddr c s0 ->
          is_empty_strat delta_env1 addrs_env1 ->
          strat_subset_strict delta_env1 addrs_env1 delta_env2 addrs_env2 s0 -> 
          strat_liquidity delta_usr addrs_usr delta_env2 addrs_env2 caddr c s0 ->
          strat_liquidity delta_usr addrs_usr delta_env1 addrs_env1 caddr c s0.
      Proof.
        intros * Hwell_sys1 Hwell_sys2 Hstrat_refines Hliq_delta2.
        unfold strat_liquidity in *.
        intros.
        unfold isReachableUnderInterleavedExecution in H5.
        specialize(H3 Hwell_sys2 tr s' tr').
        assert (interleavedExecution delta_usr addrs_usr delta_env2 addrs_env2 s0 s0
        tr Tusr s' tr').
        eapply interleavedExecution_mono_incl_usr_unchanging;eauto.
        unfold isReachableUnderInterleavedExecution in Hliq_delta2.
        specialize (H3 H6).
        decompose_exists.
        exists x, x0.
        eapply userLiquidatesNSteps_incl_usr_unchanging_empty in Hliq_delta2;eauto.
      Qed.
  
  End Monotonicity.