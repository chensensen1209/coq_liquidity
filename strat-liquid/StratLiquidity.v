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
(* Require Import BaseLiquidity. *)
From Coq Require Import List.
From Coq Require Import Bool.
From Coq Require Import ZArith.
From Coq Require Import Arith.
From Coq Require Import String.
From Coq Require Import Lia.
Import RecordSetNotations.
From Coq Require Import Permutation.
Import ListNotations.

Section stratLiquidity.

Variable miner_address : Address.

Hypothesis miner_always_eoa : address_is_contract miner_address = false.

Global Definition miner_reward := 10%Z.

Definition strat := forall s0 s, trace(s0, s) -> list Address -> list Action.

Definition is_valid_action (s : ChainState) (a : Action) : bool :=
  match transition s a with
  (* 包含等待动作以及caddr的act_call *)
  | Ok _ => is_call_or_wait a
  | Err _ => false
  end.

Fixpoint at_most_one_wait (l : list Action) : Prop :=
  match l with
  | [] => True
  | x :: xs =>
      if is_wait_act_vo x then
        (forall y, In y xs -> is_wait_act_vo y = false)
      else
        at_most_one_wait xs
  end.

Lemma head_wait_implies_tail_no_wait :
  forall (l : list Action) (a : Action) (l' : list Action),
  at_most_one_wait l ->
    l = a :: l' ->
    is_wait_act_vo a = true ->
    (forall x, In x l' -> is_wait_act_vo x = false).
Proof.
  intros l a l' Hamt Hcons Hwait x Hin.
  rewrite Hcons in Hamt.
  simpl in Hamt.
  rewrite Hwait in Hamt.
  apply Hamt. assumption.
Qed.


  Definition wellStrat (delta : strat)
                     (addrs : list Address)
                     (contract : Contract Setup Msg State Error)
                     (s0 : ChainState)
                     : Prop :=
  forall (s: ChainState) (tr_s : trace(s0, s)) ,
    let delta_actions := (delta s0 s tr_s addrs) in
    ( readyToStepState contract caddr s0 s -> 
      Forall (fun a => is_valid_action s a = true) delta_actions) /\
    Forall (fun a => In (get_act_origin a) addrs)delta_actions.

(* delta 这些地址产生的动作中包含了所有的转换，其中包含空集的情况 *)
Definition is_complete_strategy  
                (delta : strat)
                (addrs : list Address)
                (contract : Contract Setup Msg State Error)
                (s0 : ChainState) :=
  wellStrat delta addrs contract s0  /\ 
  (forall s s' tr a,
    transition s a = Ok s' ->
    (* 包含了等待动作，主动选择 *)
     In a (delta s0 s tr addrs)).

Definition is_empty_strat (delta : strat) (addrs : list Address): Prop :=
  forall s0 s tr_s, delta s0 s tr_s addrs = [].

Definition incl {A : Type} (l1 l2 : list A) : Prop :=
  forall x, In x l1 -> In x l2.

Definition stratDrive (s0 : ChainState)
                      (delta : strat)
                      (addrs : list Address)
                      (s : ChainState)
                      (tr : trace(s0, s))
                      (s' : ChainState)
                      (tr' : trace(s0, s'))
                      : Prop :=
  exists  (a : Action)
          (Hact : is_call_act a = true)
          (Htrans : transition s a = Ok s'),
    (* 只包含了act——call *)
    In a (delta s0 s tr addrs) /\
    tr' = snoc tr (step_trans a Hact Htrans).


Local Open Scope nat.
(* MS_Refl 和 multiStratDrive_end并不清楚 *)
Inductive multiStratDrive (delta : strat) 
                         (addrs : list Address)
                         (s0 s : ChainState) 
                         (tr : TransitionTrace s0 s) :
  forall s', TransitionTrace s0 s' -> nat -> Prop :=
  | MS_Refl :
      multiStratDrive delta addrs s0 s tr s tr 0
  | MS_Step :
      forall s' s'' tr' tr'' count ,
        multiStratDrive delta addrs s0 s tr s' tr' count -> 
        stratDrive s0 delta addrs s' tr' s'' tr''-> 
        multiStratDrive delta addrs s0 s tr s'' tr'' (count + 1).

Definition passive_delta (delta : strat) (addrs : list Address) (s0 s : ChainState) (tr : trace(s0,s)):=
  delta s0 s tr addrs  = [wait_action_vo].

Definition maxMultiStratDrive (delta : strat) 
                              (addrs : list Address)
                              (s0 s : ChainState) 
                              (tr : TransitionTrace s0 s)
                              (s' : ChainState)
                              (tr' : TransitionTrace s0 s')
                              (n : nat) := 
  multiStratDrive delta addrs s0 s tr s' tr' n /\ 
  delta s0 s' tr' addrs = [].

(* 通过限制maxMultiStratDriveSteps限制环境的干扰能力 *)
Definition strat_finite (delta : strat) 
                        (addrs : list Address)
                        (maxMultiStratDriveSteps : nat) :=
  forall (s0 s : ChainState) (tr : TransitionTrace s0 s) ,
    exists (n : nat) (s' : ChainState) (tr' : TransitionTrace s0 s'),
      ( n <= maxMultiStratDriveSteps /\
        maxMultiStratDrive delta addrs s0 s tr s' tr' n).

(* 表示该哪一方行动了 *)
Inductive stratType :=
  | Tusr
  | Tenv.

Definition negate_stratType (t : stratType) : stratType :=
  match t with
  | Tusr => Tenv   (* If it's Tusr, return Tenv *)
  | Tenv => Tusr   (* If it's Tenv, return Tusr *)
  end.

Inductive interleavedExecution (delta_usr : strat)
                              (addrs_usr : list Address)
                              (delta_env : strat)
                              (addrs_env : list Address)
                              (s0 s : ChainState)
                              (tr : trace(s0, s)) :
  stratType -> forall s' : ChainState, trace(s0, s') -> Prop :=
  | IS_Refl : forall flag : stratType,
      interleavedExecution delta_usr addrs_usr delta_env addrs_env s0 s tr flag s tr
  | ISE_Step : forall s' tr' s'' tr'' n,
      interleavedExecution delta_usr addrs_usr delta_env addrs_env s0 s tr Tenv s' tr' ->
      multiStratDrive delta_env addrs_env s0 s' tr' s'' tr'' n ->
      interleavedExecution delta_usr addrs_usr delta_env addrs_env s0 s tr Tusr s'' tr''
  | ISU_Step : forall s' s'' tr' tr'',
      interleavedExecution delta_usr addrs_usr delta_env addrs_env s0 s tr Tusr s' tr' ->
      stratDrive s0 delta_usr addrs_usr s' tr' s'' tr'' ->
      interleavedExecution delta_usr addrs_usr delta_env addrs_env s0 s tr Tenv s'' tr''.

Local Open Scope nat.

Inductive UserLiquidatesNSteps (delta_usr : strat)
                              (addrs_usr : list Address)
                              (delta_env : strat)
                              (addrs_env : list Address)
                              (caddr : Address)
                              (s0 s: ChainState)
                              (tr : trace(s0, s)):
  forall s' : ChainState, trace(s0, s') -> Prop :=
  | ULM_Base: 
    (funds s caddr = 0)%Z ->
    UserLiquidatesNSteps delta_usr addrs_usr delta_env addrs_env caddr  s0 s tr s tr 
  | ULM_Step : forall s' s'' tr' tr'',
    stratDrive s0 delta_usr addrs_usr s tr s' tr' -> (* 用户执行一次策略 *)
    envProgress_Mutual delta_usr addrs_usr delta_env addrs_env caddr s0 s' tr' s'' tr'' -> (* 时间减少 *)
    UserLiquidatesNSteps delta_usr addrs_usr delta_env addrs_env caddr  s0 s tr  s'' tr'' 
with envProgress_Mutual (delta_usr : strat)
                        (addrs_usr : list Address)
                        (delta_env : strat)
                        (addrs_env : list Address)
                        (caddr: Address)
                        (s0 s: ChainState)
                        (tr : trace(s0, s)) :
  forall s' : ChainState, trace(s0, s') -> Prop :=
  | EPM_Base :
    (funds s caddr = 0)%Z ->
    envProgress_Mutual delta_usr addrs_usr delta_env addrs_env caddr s0 s tr  s tr 
  | EPM_Step: forall s'' tr'',
    (funds s caddr > 0)%Z ->
    ( forall s' tr' n,
        multiStratDrive delta_env addrs_env s0 s tr s' tr' n -> 
        UserLiquidatesNSteps delta_usr addrs_usr delta_env addrs_env caddr s0 s' tr'  s'' tr'' ) ->
    envProgress_Mutual delta_usr addrs_usr delta_env addrs_env caddr s0 s tr s'' tr'' .


Scheme ul_mut := Induction for envProgress_Mutual Sort Prop
  with env_mut := Induction for UserLiquidatesNSteps Sort Prop.

Combined Scheme ul_mutual_ind from ul_mut, env_mut.

(* 由于下面的清零过程要用户先开始，那么此处需要是Tusr *)
Definition isReachableUnderInterleavedExecution
          (delta_usr delta_env : strat)
          (addrs_usr addrs_env : list Address)
          (s0 : ChainState)
          (tr : trace(s0,s0))
          (s' : ChainState)
          (tr' : trace(s0,s')) :=
  interleavedExecution delta_usr addrs_usr delta_env addrs_env s0 s0 tr Tusr s' tr'.

Local Open Scope nat.

Definition maxMultiStratDriveSteps := 1024.

Definition wellDefinedSystem
        (delta_usr : strat)
        (addrs_usr : list Address)
        (delta_env : strat)
        (addrs_env : list Address)
        (caddr : Address)
        (c : Contract Setup Msg State Error)
        (s0 : ChainState) :=
  wellStrat delta_usr addrs_usr c s0  /\
  wellStrat delta_env addrs_env c s0 /\
  strat_finite delta_env addrs_env maxMultiStratDriveSteps /\
  is_init_state c caddr s0.

(*  *)
Definition strat_liquidity 
          (delta_usr : strat)
          (addrs_usr : list Address)
          (delta_env : strat)
          (addrs_env : list Address)
          (caddr : Address)
          (c : Contract Setup Msg State Error)
          (s0 : ChainState) :=
  wellDefinedSystem delta_usr addrs_usr delta_env addrs_env caddr c s0 ->
  forall tr s' tr',
    isReachableUnderInterleavedExecution delta_usr delta_env addrs_usr addrs_env s0 tr s' tr' ->
    (exists s'' tr'',
      UserLiquidatesNSteps delta_usr addrs_usr delta_env addrs_env caddr  s0 s' tr' s'' tr'').
  
End stratLiquidity.
