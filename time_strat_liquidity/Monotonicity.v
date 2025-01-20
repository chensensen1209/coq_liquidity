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
Section Monotonicity.
  Context {BaseTypes : ChainBase}.
  Variable miner_address : Address.
  Hypothesis miner_always_eoa : address_is_contract miner_address = false.
  Global Definition miner_reward := 10%Z.

  Notation "trace( from , to )" := (TransitionTrace miner_address from to)(at level 10).

  Definition acts_subset (acts1 acts2 : list Action) : Prop :=
    incl acts1 acts2. 

  Definition acts_subset_time (acts1 acts2 : list Action) : Prop :=
  (acts_subset acts1 acts2 ) /\ 
  (forall a, is_wait_act a = true -> 
              In a acts2 -> 
              In a acts1).

  Definition strat_subset 
              (addrs1 : list Address)
              (delta1 : strat miner_address addrs1) 
              (addrs2 : list Address) 
              (delta2 : strat miner_address addrs1) 
    s0: Prop :=
    forall s tr,
        acts_subset
        (packe miner_address (delta1 s0 s tr))
        (packe miner_address (delta2 s0 s tr)). 

  Definition strat_subset_time 
    (addrs1 : list Address)
    (delta1 : strat miner_address addrs1) 
    (addrs2 : list Address) 
    (delta2 : strat miner_address addrs1) 
    s0: Prop :=
    forall s tr,
        acts_subset_time
        (packe miner_address (delta1 s0 s tr))
        (packe miner_address (delta2 s0 s tr)).

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

  Lemma stratDrive_subset:
    forall s0 s s' tr tr' delta_usr1 addrs_usr1 delta_usr2 addrs_usr2,
      strat_subset addrs_usr2 delta_usr2 addrs_usr1 delta_usr1  s0 ->
      stratDrive miner_address addrs_usr2 delta_usr2 s0 s tr s' tr' ->
      stratDrive miner_address addrs_usr1 delta_usr1 s0 s tr s' tr'.
  Proof.
    unfold stratDrive.
    unfold strat_subset.
    unfold acts_subset.
    intros.
    decompose_exists.
    destruct_and_split. 
    specialize(H s tr).
    exists x, x0 , x1.
    split.
    eauto.
    destruct (packe miner_address (delta_usr2 s0 s tr)).
    inversion H1.
    eauto.
    eauto.
  Qed.

  Lemma stratDrive_subset_time:
    forall s0 s s' tr tr' delta_usr1 addrs_usr1 delta_usr2 addrs_usr2,
      strat_subset_time addrs_usr2 delta_usr2 addrs_usr1 delta_usr1  s0 ->
      stratDrive miner_address addrs_usr2 delta_usr2 s0 s tr s' tr' ->
      stratDrive miner_address addrs_usr1 delta_usr1 s0 s tr s' tr'.
  Proof.
    unfold strat_subset_time.
    unfold acts_subset_time.
    intros.
    decompose_exists.
    destruct_and_split. 
    specialize(H s tr).
    destruct_and_split.
    unfold stratDrive  in H0.
    decompose_exists.
    destruct_and_split.
    exists x, x0 , x1.
    split.
    eauto.
    destruct (packe miner_address (delta_usr2 s0 s tr)).
    inversion H0.
    eauto.
  Qed.

  Lemma multiStratDrive_subset:
    forall s0 s s' tr tr' delta_usr1 addrs_usr1 delta_usr2 addrs_usr2 n,
      strat_subset delta_usr2 addrs_usr2 delta_usr1 addrs_usr1 s0 ->
      multiStratDrive miner_address delta_usr2 addrs_usr2 s0 s tr s' tr' n ->
      multiStratDrive miner_address delta_usr1 addrs_usr1 s0 s tr s' tr' n.
  Proof.
    intros.
    induction H0.
    - eapply MS_Refl.
    - eapply stratDrive_subset in H1;eauto.
      eapply MS_Step;eauto.
  Qed.

  Lemma multiStratDrive_subset_time:
    forall s0 s s' tr tr' delta_usr1 addrs_usr1 delta_usr2 addrs_usr2 n,
      strat_subset_time delta_usr2 addrs_usr2 delta_usr1 addrs_usr1 s0 ->
      multiStratDrive miner_address delta_usr2 addrs_usr2 s0 s tr s' tr' n ->
      multiStratDrive miner_address delta_usr1 addrs_usr1 s0 s tr s' tr' n.
  Proof.
    intros.
    induction H0.
    - eapply MS_Refl.
    - eapply stratDrive_subset_time in H1;eauto.
      eapply MS_Step;eauto.
  Qed.

  Lemma interleavedExecution_mono_incl_usr_unchanging (addrs_usr: list Address) (delta_usr : strat miner_address addrs_usr)  (addrs_env1: list Address) (delta_env1 : strat miner_address addrs_env1) (addrs_env2: list Address) (delta_env2 : strat miner_address addrs_env2) :
    forall s0 s' flag tr tr',
      strat_subset addrs_env1 delta_env1 addrs_env2 delta_env2  s0 ->
      interleavedExecution miner_address addrs_usr delta_usr addrs_env1 delta_env1  s0 s0 tr flag s' tr' ->
      interleavedExecution miner_address addrs_usr delta_usr addrs_env2 delta_env2 s0 s0 tr flag s' tr'.
  Proof.
    intros * Hsbt_delta Hrc_itv.
    induction Hrc_itv;eauto;try intuition.
    - eapply IS_Refl.
    - eapply (IS_Wait_Step_Once miner_address addrs_usr delta_usr addrs_env2 delta_env2 s0 s0 tr flag s' tr' s'' tr'' a1 a2);eauto.
      unfold strat_subset in Hsbt_delta.
      specialize (Hsbt_delta s' tr').
      unfold acts_subset in Hsbt_delta.
      intuition.
    - eapply ISE_Step;eauto.
      pose proof Hsbt_delta as Hst.
      unfold strat_subset in Hsbt_delta.
      specialize(Hsbt_delta  s' tr').
      unfold acts_subset in Hsbt_delta.
      destruct (delta_env1 s0 s' tr') eqn : He;try congruence.
      intuition.
      eapply multiStratDrive_subset;eauto.
      eapply multiStratDrive_subset;eauto.
    - eapply ISE_Turn_Step;eauto.
      unfold strat_subset in Hsbt_delta.
      specialize (Hsbt_delta s' tr').
      unfold acts_subset in Hsbt_delta.
      intuition.
    - eapply ISU_Step;eauto.
    - eapply ISU_Turn_Step;eauto.
  Qed.

  Lemma interleavedExecution_mono_incl_usr_unchanging_time (addrs_usr: list Address) (delta_usr : strat miner_address addrs_usr)  (addrs_env1: list Address) (delta_env1 : strat miner_address addrs_env1) (addrs_env2: list Address) (delta_env2 : strat miner_address addrs_env2) :
    forall s0 s' flag tr tr',
      strat_subset_time addrs_env1 delta_env1 addrs_env2 delta_env2  s0 ->
      interleavedExecution miner_address addrs_usr delta_usr addrs_env1 delta_env1  s0 s0 tr flag s' tr' ->
      interleavedExecution miner_address addrs_usr delta_usr addrs_env2 delta_env2 s0 s0 tr flag s' tr'.
  Proof.
    intros *  Hsbt_delta Hrc_itv.
    induction Hrc_itv;eauto;try intuition.
    - eapply IS_Refl.
    - eapply (IS_Wait_Step_Once miner_address addrs_usr delta_usr addrs_env2 delta_env2 s0 s0 tr flag s' tr' s'' tr'' a1 a2);eauto.
      unfold strat_subset_time in Hsbt_delta.
      specialize (Hsbt_delta s' tr').
      unfold acts_subset_time in Hsbt_delta.
      destruct Hsbt_delta as [Hsbt_delta _].
      unfold acts_subset in Hsbt_delta.
      intuition.
    - eapply ISE_Step;eauto.
      pose proof Hsbt_delta as Hst.
      unfold strat_subset_time in Hsbt_delta.
      specialize (Hsbt_delta s' tr').
      unfold acts_subset_time in Hsbt_delta.
      destruct Hsbt_delta as [Hsbt_delta _].
      unfold acts_subset in Hsbt_delta.
      destruct (delta_env1 s0 s' tr') eqn : He;try congruence.
      intuition.
      eapply multiStratDrive_subset_time;eauto.
      eapply multiStratDrive_subset_time;eauto.
    - eapply ISE_Turn_Step;eauto.
      unfold strat_subset_time in Hsbt_delta.
      specialize (Hsbt_delta s' tr').
      unfold acts_subset_time in Hsbt_delta.
      destruct Hsbt_delta as [Hsbt_delta _].
      unfold acts_subset in Hsbt_delta.
      intuition.
    - eapply ISU_Step;eauto.
    - eapply ISU_Turn_Step;eauto.
  Qed.

  Lemma userLiquidatesNSteps_incl_usr_unchanging (addrs_usr: list Address) (delta_usr : strat miner_address addrs_usr)  (addrs_env1: list Address) (delta_env1 : strat miner_address addrs_env1) (addrs_env2: list Address) (delta_env2 : strat miner_address addrs_env2) :
    forall s0 s  c caddr tr ,
      is_init_state c caddr s0 ->
      strat_subset_time addrs_env1 delta_env1 addrs_env2 delta_env2  s0 ->
      UserLiquidatesNSteps miner_address addrs_usr delta_usr addrs_env2 delta_env2  caddr s0 s tr ->
      UserLiquidatesNSteps miner_address addrs_usr delta_usr addrs_env1 delta_env1  caddr s0 s tr .
  Proof.
    intros * Hinit Hsbt_delta Hrc_itv.
    eapply (env_mut miner_address addrs_usr delta_usr addrs_env2 delta_env2  caddr s0 
    (fun s tr   (_ : envProgress_Mutual miner_address addrs_usr delta_usr addrs_env2 delta_env2  caddr s0 s tr ) =>  
    envProgress_Mutual miner_address addrs_usr delta_usr addrs_env1 delta_env1  caddr s0 s tr )
    (fun  s tr  (_ : UserLiquidatesNSteps miner_address addrs_usr delta_usr addrs_env2 delta_env2  caddr  s0 s tr ) => 
    UserLiquidatesNSteps miner_address addrs_usr delta_usr addrs_env1 delta_env1  caddr s0 s tr )
    );intros;subst;eauto.
    - apply EPM_Base. assumption.
    - eapply EPM_Step.
      eauto.
      intros.
      assert (multiStratDrive miner_address addrs_env2 delta_env2 s0 s1 tr0 s' tr' n).
      {
        eapply multiStratDrive_subset_time;eauto.
      }
      specialize (H s' tr' n).
      eapply H;eauto.
    - eapply (EPM_Time miner_address addrs_usr delta_usr addrs_env1 delta_env1 caddr s0 s1 tr0  s' tr'  a1 a2);eauto.
      unfold strat_subset_time in Hsbt_delta.
      specialize (Hsbt_delta s1 tr0).
      unfold acts_subset_time in Hsbt_delta.
      destruct Hsbt_delta as [Hsbt_delta Hsbt_delta_time].
      specialize (Hsbt_delta_time a2 e0 i0).
      unfold acts_subset in Hsbt_delta.
      intuition.
    - eapply EPM_Turn;eauto.
      unfold strat_subset_time in Hsbt_delta.
      specialize (Hsbt_delta s1 tr0).
      unfold acts_subset_time in Hsbt_delta.
      destruct Hsbt_delta as [Hsbt_delta Hsbt_delta_time].
      specialize (Hsbt_delta_time a e i).
      unfold acts_subset in Hsbt_delta.
      intuition.
    - eapply ULM_Base;eauto.
    - eapply ULM_Step;eauto.
    - eapply (ULM_Time miner_address addrs_usr delta_usr addrs_env1 delta_env1 caddr s0 s1 tr0  s' tr'  a1 a2);eauto.
      unfold strat_subset_time in Hsbt_delta.
      specialize (Hsbt_delta s1 tr0).
      unfold acts_subset_time in Hsbt_delta.
      destruct Hsbt_delta as [Hsbt_delta Hsbt_delta_time].
      specialize (Hsbt_delta_time a2 e0 i0).
      unfold acts_subset in Hsbt_delta.
      intuition.
    - eapply ULM_Turn;eauto.
  Qed.

  Lemma strat_liquid_Mono_usr_unchanging 
      (addrs_usr: list Address) (delta_usr : strat miner_address addrs_usr) 
      (addrs_env1: list Address)  (delta_env1 : strat miner_address addrs_env1) 
      (addrs_env2: list Address)  (delta_env2 : strat miner_address addrs_env2) :
    forall s0 c caddr, 
      is_init_state c caddr s0 ->
      strat_subset_time addrs_env1 delta_env1 addrs_env2 delta_env2  s0->
      strat_liquidity miner_address addrs_usr delta_usr  addrs_env2 delta_env2 c caddr  s0 ->
      strat_liquidity miner_address addrs_usr delta_usr  addrs_env1 delta_env1 c caddr  s0.
  Proof.
    intros * Hinit Hstrat_refines Hliq_delta2.
    unfold strat_liquidity in *.
    intros Hwell_sys * Hrc_itv.
    specialize(Hliq_delta2 Hinit tr s' tr').
    assert (interleavedExecution miner_address addrs_usr delta_usr addrs_env2 delta_env2  s0 s0
    tr Tusr s' tr').
    eapply interleavedExecution_mono_incl_usr_unchanging_time;eauto.
    specialize (Hliq_delta2 H).
    decompose_exists.
    eapply userLiquidatesNSteps_incl_usr_unchanging in Hliq_delta2;eauto.
  Qed.

End Monotonicity.