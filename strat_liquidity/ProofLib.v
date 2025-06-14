
Require Import BuildUtils.
Require Import Blockchain.
Require Import StratModel. 

Require Import LibTactics. 

Definition ProtectWrapper (a:Type) : Type :=a.
Lemma MakeProtectWrapper : forall H, H -> ProtectWrapper H.
Proof.
  auto.
Qed.
Ltac protect H := let H' := fresh in rename H into H'; lets H : MakeProtectWrapper H'; clear H'.
Ltac unprotect H := unfold ProtectWrapper in H.


Context {BaseTypes : ChainBase}.

Lemma address_not_contract_negb:
  forall addr,
    address_not_contract addr= true -> address_is_contract addr = false.
Proof.
  intros.
  unfold address_not_contract in H.
  destruct ((address_is_contract addr)) eqn : H'; try congruence.
  simpl in H.
  congruence.
Qed.

Lemma addr_ctr_diff:
  forall a1 a2, 
    address_is_contract a1 = true ->
    address_not_contract a2 = true ->
    (a1 =? a2)%address = false.
Proof.
  introv Hc1 Hc2.
  eapply address_not_contract_negb in Hc2; eauto.
  destruct (a1 =? a2)%address eqn: E; auto.
  lets H__: address_eqb_spec a1 a2.
  inverts H__; 
    tryfalse.
Qed.         

Lemma addr_ctr_neq:
  forall a1 a2, 
    address_is_contract a1 = true ->
    address_not_contract a2 = true ->
    a1 <> a2. 
Proof.
  introv Hc1 Hc2.
  pose proof addr_ctr_diff a1 a2.
  specializes H; eauto.
  rewrite <- address_eq_ne' in H.
  auto.
Qed.         

Lemma impl_lem:
  forall P Q,
    (P /\ ~Q) -> ~(P->Q).
Proof.
  intros.
  introv Hf.
  destruct H.
  tauto.
Qed.


  
