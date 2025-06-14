
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

Section Monotonicity.

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

  Definition addrs_subset (addrs1: list Address) (addrs2 : list Address) :=
    incl addrs1 addrs2.

  Definition acts_subset (acts1 acts2 : list Action) : Prop :=
    incl acts1 acts2. 

  Global Definition miner_reward := 10%Z.

  Definition strat_subset 
    (addrs : list Address)
    (delta1 : strat miner_address addrs) 
    (delta2 : strat miner_address addrs) 
    s0: Prop :=
    forall s tr,
      acts_subset
        (delta1 s0 s tr)
        (delta2 s0 s tr).

  Lemma in_empty_false : forall (A : Type) (x : A), ~ In x [].
  Proof.
    intros A x H4.
    inversion H4. 
  Qed.

  Lemma in_nonempty_to_empty_contradiction : forall (A : Type) (a : A) (l : list A),
      (forall x, In x (a :: l) -> In x []) -> False.
  Proof.
    intros A a l H4.
    specialize (H4 a).
    simpl in H4.
    destruct H4.
    eauto.
  Qed.

  Lemma stratDrive_subset:
    forall s0 s s' tr tr' delta_usr1 addrs_usr delta_usr2,
      strat_subset addrs_usr delta_usr2 delta_usr1  s0 ->
      stratDrive miner_address addrs_usr delta_usr2  s0 s tr s' tr' ->
      stratDrive miner_address addrs_usr delta_usr1  s0 s tr s' tr'.
  Proof.
    unfold stratDrive.
    unfold strat_subset.
    unfold acts_subset.
    intros.
    decompose_exists.
    destruct_and_split. 
    specialize(H3 s tr).
    exists x, x0, x1.
    split.
    eauto.
    destruct (delta_usr2 s0 s tr).
    inversion H4.
    eauto.
  Qed.

  Lemma multiStratDrive_subset:
    forall s0 s s' tr tr' delta_usr1 addrs_usr delta_usr2 n,
      strat_subset addrs_usr delta_usr2 delta_usr1 s0 ->
      multiStratDrive miner_address addrs_usr delta_usr2 s0 s tr s' tr' n ->
      multiStratDrive miner_address addrs_usr delta_usr1 s0 s tr s' tr' n.
  Proof.
    intros.
    induction H4.
    - eapply MS_Refl.
    - eapply stratDrive_subset in H5;eauto.
      eapply MS_Step;eauto.
  Qed.

  Lemma interleavedExecution_mono_incl_wrt_env 
    (addrs_usr: list Address) (delta_usr : strat miner_address addrs_usr)  
    (addrs_env: list Address)
    (delta_env1 : strat miner_address addrs_env) 
    (delta_env2 : strat miner_address addrs_env) :
    forall s0 s' flag tr tr',
      strat_subset addrs_env delta_env1 delta_env2  s0 ->
      interleavedExecution miner_address addrs_usr delta_usr addrs_env delta_env1  s0 s0 tr flag s' tr' ->
      interleavedExecution miner_address addrs_usr delta_usr addrs_env delta_env2 s0 s0 tr flag s' tr'.
  Proof.
    intros * Hsbt_delta Hrc_itv.
    induction Hrc_itv;eauto;try intuition.
    - eapply IS_Refl.
    - eapply ISE_Step;eauto.
      pose proof Hsbt_delta as Hst.
      unfold strat_subset in Hsbt_delta.
      specialize(Hsbt_delta  s' tr').
      unfold acts_subset in Hsbt_delta.
      destruct (delta_env1 s0 s' tr') eqn : He;try congruence.
      intuition.
      eapply multiStratDrive_subset;eauto.
      eapply multiStratDrive_subset;eauto.
    - eapply ISU_Step;eauto.
  Qed.

  Lemma userLiquidates_incl_wrt_env 
    (addrs_usr: list Address)
    (delta_usr : strat miner_address addrs_usr)  
    (addrs_env: list Address)
    (delta_env1 : strat miner_address addrs_env) 
    (delta_env2 : strat miner_address addrs_env)
    phi ss:
    forall s0 s  c caddr tr ,
      is_init_state c caddr s0 ->
      strat_subset addrs_env delta_env1 delta_env2 s0 ->
      userLiquidates miner_address addrs_usr delta_usr addrs_env delta_env2 caddr s0 s ss tr phi ->
      userLiquidates miner_address addrs_usr delta_usr addrs_env delta_env1 caddr s0 s ss tr phi.
  Proof.
    intros * Hinit Hsbt_delta_pro Hrc_itv.
    eapply (envp_mut miner_address addrs_usr delta_usr addrs_env delta_env2 caddr s0 
              (fun s ss tr phi (_ : envProgress miner_address addrs_usr delta_usr addrs_env delta_env2 caddr s0 s ss tr phi) =>  
                 envProgress miner_address addrs_usr delta_usr addrs_env delta_env1 caddr s0 s ss tr phi) 
              (fun s ss tr phi (_ : userLiquidates miner_address addrs_usr delta_usr addrs_env delta_env2  caddr s0 s ss tr phi) => 
                 userLiquidates miner_address addrs_usr delta_usr addrs_env delta_env1 caddr s0 s ss tr phi)
           );intros;subst;eauto.
    - apply E_Base. assumption.
    -  
      eapply E_Step.
      eauto.
      intros.
      assert (multiStratDrive miner_address addrs_env delta_env2  s0 s1 tr0 s' tr' n0).
      {
        eapply multiStratDrive_subset;eauto.
      }
      specialize (H3 s' tr' n0).
      eapply H3;eauto.
    - eapply U_Base;eauto.
    - eapply U_Step;eauto.
  Qed.   

  Theorem strat_liquidity_mono_wrt_env 
    (addrs_usr: list Address) (delta_usr : strat miner_address addrs_usr) 
    (addrs_env: list Address)
    (delta_env1 : strat miner_address addrs_env) 
    (delta_env2 : strat miner_address addrs_env)
    phi: 
    forall s0 c caddr, 
      is_init_state c caddr s0 ->
      strat_subset addrs_env delta_env1 delta_env2  s0 ->
      strategy_aware_liquidity miner_address addrs_usr delta_usr addrs_env delta_env2 c caddr s0 phi ->
      strategy_aware_liquidity miner_address addrs_usr delta_usr addrs_env delta_env1 c caddr s0 phi.
  Proof.
    intros * Hinit Hstrat_refines Hliq_delta2.
    unfold strat_liquidity in *.
    intros Hwell_sys * Hrc_itv.

    specialize(Hliq_delta2 Hinit tr s' tr').
    assert (interleavedExecution miner_address addrs_usr delta_usr addrs_env delta_env2  s0 s0
              tr Tusr s' tr').
    eapply interleavedExecution_mono_incl_wrt_env;eauto.
    specialize (Hliq_delta2 H3).
    decompose_exists.
    eapply userLiquidates_incl_wrt_env in Hliq_delta2;eauto.
  Qed.

End Monotonicity.
