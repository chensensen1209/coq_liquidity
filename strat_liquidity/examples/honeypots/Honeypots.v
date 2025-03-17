
Require Import Blockchain.
Require Import Serializable.
Require Import Extras.
Require Import BuildUtils.
Require Import RecordUpdate.
Require Import Automation.
Require Import ContractCommon.
Require Import ResultMonad.
Require Import ChainedList.
Require Import ModelBase.
Require Import StratModel.
From Coq Require Import List.
From Coq Require Import Bool.
From Coq Require Import ZArith.
From Coq Require Import Arith.
From Coq Require Import String.
Import ListNotations.
Require Import Lia.
Import RecordSetNotations.


Section Gift1ETH.
  Context {BaseTypes : ChainBase}.
  Set Primitive Projections.
  Set Nonrecursive Elimination Schemes.
  Context {AddrSize : N}.

  Local Open Scope Z.

  Definition Error : Type := nat.
  Definition default_error : Error := 1%nat.

  Definition bytes := N.

  Definition bytes32 := N.

  Definition sha3 (n : bytes)  : N :=
    Npos (countable.encode n).


  Inductive Msg :=
  | SetPass (h : bytes32)
  | GetGift (pass : bytes)
  | PassHasBeenSetMsg (h : bytes32).


  Global Instance Msg_serializable : Serializable Msg :=
  Derive Serializable Msg_rect<SetPass, GetGift, PassHasBeenSetMsg>.

  Record State := build_state {
    passHasBeenSet : bool;
    hashPass       : N;
    balance        : Z
  }.

  Record Setup := build_setup {
    setup_passHasBeenSet : bool
  }.

  Instance state_settable : Settable State :=
  settable! build_state
    <passHasBeenSet; hashPass; balance>.

  Instance setup_settable : Settable Setup :=
  settable! build_setup
    <setup_passHasBeenSet>.


  Section Serialization.
    Global Instance State_serializable : Serializable State :=
      Derive Serializable State_rect<build_state>.

    Global Instance Setup_serializable : Serializable Setup :=
      Derive Serializable Setup_rect<build_setup>.
  End Serialization.

  (* 初始化 *)
  Definition init
             (chain : Chain)
             (ctx : ContractCallContext)
             (setup : Setup)
    : result State Error :=
    if ( negb (setup_passHasBeenSet setup)) then
      Ok (build_state (setup_passHasBeenSet setup) 0 ctx.(ctx_amount))
    else
      Err default_error.

  Definition one_ether : Z := 1.

  Definition require_zero (ctx : ContractCallContext) : bool :=
    (ctx_amount ctx =? 0) .

  (* fallback函数 *)
  Definition fallback_handler
             (ctx : ContractCallContext)
             (st : State)
    : State :=
    st <| balance := st.(balance) + ctx.(ctx_amount) |>.

  (* 设置密码，如果没人有设置密码 *)
  (* h是自己的hash密码，转入1eth后有资格设置 *)
  Definition setPass
             (ctx : ContractCallContext)
             (st : State)
             (h : bytes32)
    : result (State * list ActionBody) Error :=
    if negb st.(passHasBeenSet) && (ctx.(ctx_amount) >=? one_ether)
    then
      Ok ( st <| hashPass := h|> 
              <| balance  := st.(balance) + ctx.(ctx_amount) |>
         , [])
    else
      Ok ( st <| balance  := st.(balance) + ctx.(ctx_amount) |>
          , []).

  (* pass普通密码 *)
  Definition getGift
             (ctx : ContractCallContext)
             (st : State)
             (pass : bytes)
    : result (State * list ActionBody) Error :=
    if (require_zero ctx) then
      if (st.(hashPass) =? (sha3 pass))%N
      then
        let amt := st.(balance) in
        Ok ( st <| balance := 0 |> , [ act_transfer (ctx_from ctx) amt ] )
      else
        Err default_error
    else
      Err default_error.

  Definition passHasBeenSet_fn
             (ctx : ContractCallContext)
             (st : State)
             (h : bytes32)
    : result (State * list ActionBody) Error :=
    if (require_zero ctx) then
      if (h =? st.(hashPass))%N 
      then Ok (st <| passHasBeenSet := true |>, [])
      else Err default_error
    else
      Err default_error.

  Definition receive
             (chain : Chain)
             (ctx : ContractCallContext)
             (st : State)
             (msg : option Msg)
    : result (State * list ActionBody) Error :=
    match msg with
    | Some (SetPass h) =>
        setPass ctx st h
    | Some (GetGift p) =>
        getGift ctx st p
    | Some (PassHasBeenSetMsg h) =>
        passHasBeenSet_fn ctx st h
    | None =>
        (* 无消息可处理，可视需求处理，执行 fallback。 *)
        let new_st := fallback_handler ctx st in
        Ok (new_st, [])
    end.

  Definition contract : Contract Setup Msg State Error :=
    build_contract init receive.
    
End Gift1ETH.

Section Liqiuidity.
  
  Context {BaseTypes : ChainBase}.
  Set Primitive Projections.
  Set Nonrecursive Elimination Schemes.
  Context {AddrSize : N}.

  Ltac reduce_init :=
    match goal with
    | H: init ?chain ?ctx ?setup = Ok ?st |- _ =>
      unfold init in H;
      (* 这里的 'if (negb (setup_passHasBeenSet setup)) then ... else ...' *)
      destruct (negb (setup_passHasBeenSet setup)) eqn:Einit in H;
      try discriminate;
      simpl in H
    end.

  Ltac reduce_fallback_handler :=
    match goal with
    | H: fallback_handler ?ctx ?st = ?st' |- _ =>
      unfold fallback_handler in H;
      simpl in H
    end.

  Ltac reduce_setPass :=
    match goal with
    | H: setPass ?ctx ?st ?h = Ok (?new_st, ?acts) |- _ =>
      unfold setPass in H;
      destruct (negb (passHasBeenSet st) && (ctx_amount ctx >=? one_ether)%Z) eqn:EsetPass in H;
      try discriminate;
      simpl in H
    end.

  Ltac reduce_getGift :=
    match goal with
    | H: getGift ?ctx ?st ?pass = Ok (?new_st, ?acts) |- _ =>
      unfold getGift in H;
      destruct ((require_zero ctx)) eqn : Ezero in H;
      try discriminate;
      (* 'if N.eqb st.(hashPass) (sha3 pass) then ... else ...' *)
      destruct ((st.(hashPass) =? (sha3 pass))%N) eqn:EgetGift in H;
      try discriminate;
      simpl in H
    end.

  Ltac reduce_passHasBeenSet_fn :=
    match goal with
    | H: passHasBeenSet_fn ?ctx ?st ?h = Ok (?new_st, ?acts) |- _ =>
      unfold passHasBeenSet_fn in H;
      (* 'if N.eqb h st.(hashPass) then ... else ...' *)
      destruct ((require_zero ctx)) eqn : Ezero in H;
      try discriminate;
      destruct ( (h  =? (hashPass st))%N) eqn:Ephs in H;
      try discriminate;
      simpl in H
    end.

  Ltac reduce_receive :=
    match goal with
    | H: receive ?chain ?ctx ?st ?msg = Ok (?new_st, ?acts) |- _ =>
      unfold receive in H;
      destruct msg eqn:Emsg in H;
      try discriminate;
      simpl in H
    end.

  Tactic Notation "contract_simpl" := contract_simpl @receive @init.


  Ltac destruct_message :=
    repeat match goal with
      | H : Blockchain.receive _ _ _ _ _ = Ok _ |- _ => unfold Blockchain.receive in H; cbn in H
      | msg : option Msg |- _ => destruct msg
      | msg : Msg |- _ => destruct msg
      | H : Blockchain.receive _ _ _ _ None = Ok _ |- _ => now contract_simpl
      | H : receive _ _ _ None = Ok _ |- _ => now contract_simpl
      end.

  Definition get_contract_state (state : ChainState) (addr : Address) : option State :=
    match env_contract_states state addr with
    | Some serialized_state =>
      deserialize serialized_state
    | None => None
    end.

  Context `{caddr : Address} `{miner : Address}.

  Variable s0 : ChainState.

  Hypothesis H_init: is_init_state contract caddr s0.

  Hypothesis H_miner : address_not_contract miner= true.

  Lemma get_contract_state_correct :
    exists cstate, get_contract_state s0 caddr = Some cstate.
  Proof.
    intros.
    decompose_is_init_state H_init.
    exists state.
    unfold get_contract_state .
    rewrite H_env_states.
    setoid_rewrite deserialize_serialize.
    reflexivity.
  Qed.

  Variable init_cstate : State.

  Hypothesis H_state : get_contract_state s0 caddr = Some init_cstate.

  Variable user1 : Address.
  Variable user2 : Address.

  Variable correct_pass : N.

  (* 一个假设，每个状态中正确的密码 *)
  Hypothesis hashPass_kown_all_state :
    forall (s:ChainState) (cstate : State),
      contract_state s caddr = Some cstate ->
      cstate.(hashPass) = sha3 correct_pass.
  
  Hypothesis user1_eoa : address_not_contract user1 = true.
  Hypothesis user2_eoa : address_not_contract user2 = true.

  Variable attacker : Address.
  Variable honest : Address.

  Hypothesis attacker_eoa : address_not_contract attacker = true.
  Hypothesis honest_eoa : address_not_contract honest = true.
  Hypothesis H_honest_bal_ge_1 : forall (s:ChainState), (funds s honest >= 1)%Z.

  Hypothesis H_attack_bal_ge_1 : forall (s:ChainState), (funds s attacker >= 1)%Z.

  Variable attacker_pass : N.

  Variable honest_pass : N.

  Hypothesis pass_neq : attacker_pass <> honest_pass.

  Hypothesis honest_pass_neq : (sha3 honest_pass <> 0)%N.
  Hypothesis attacker_pass_neq : (sha3 attacker_pass <> 0)%N.

  Section sha3_coorect.

  Lemma pos_inj : forall p q : positive, N.pos p = N.pos q -> p = q.
  Proof.
    intros p q H. inversion H. reflexivity.
  Qed.

    
  Require  Coq.NArith.NArith.
  Require  stdpp.countable.


  Lemma sha3_pass_neq :sha3 attacker_pass <> sha3 honest_pass.
  Proof.
    intros H.
    eauto.
    
    unfold sha3.
    apply pos_inj in H.
    eapply stdpp.countable.encode_inj in H.
    unfold countable.encode in H.
    simpl in H.
    intuition.
  Qed.

  End sha3_coorect.

  Definition attacker_call_SetPass (state : State): Action :=
    build_call attacker caddr 1 (SetPass (sha3 attacker_pass)).

  Definition attacker_call_PassHasBeenSetMsg (state : State): Action :=
    build_call attacker caddr 0 (PassHasBeenSetMsg (sha3 attacker_pass)).

  Definition honest_call_SetPass (state : State): Action :=
    build_call honest caddr 1 (SetPass (sha3 honest_pass)).

  Definition honest_call_GetGift (state : State): Action :=
    build_call honest caddr 0 (GetGift honest_pass).

  Definition honest_call_PassHasBeenSetMsg  (state : State): Action :=
      build_call honest caddr 0 (PassHasBeenSetMsg  (sha3 honest_pass)).

  Definition attacker_strat : (strat miner [attacker]) :=
    fun s0 s tr =>
      match get_contract_state s caddr with
      | Some state =>
          if ((state.(hashPass) =? sha3 attacker_pass)%N) then
            [attacker_call_PassHasBeenSetMsg state]
          else if (negb state.(passHasBeenSet)) then
            [attacker_call_SetPass state]
          else 
            []
      | None => []
      end.
  
  Definition honest_strat : (strat miner [honest]) :=
    fun s0 s tr =>
      match get_contract_state s caddr with
      | Some state =>
        [honest_call_SetPass state;honest_call_GetGift state;honest_call_PassHasBeenSetMsg state]
      | None => []
      end.

  Definition user_call_GetGift (state : State): Action :=
    build_call user1 caddr 0 (GetGift correct_pass).

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
  

  Lemma balance_on_chain' :
    forall bstate caddr,
      reachable bstate ->
      let effective_balance := (env_account_balances bstate caddr - (sumZ (fun act => act_body_amount act) (outgoing_acts bstate caddr)))%Z in
      env_contracts bstate caddr = Some (contract : WeakContract) ->
      exists cstate,
        contract_state bstate caddr = Some cstate /\
        effective_balance = cstate.(balance).
  Proof.
    intros.
    unfold effective_balance.
    contract_induction; intros; auto; cbn in *;try congruence;try lia;eauto.
    - reduce_init.
      inversion init_some.
      simpl.
      lia.
    - reduce_receive.
      destruct_message;try congruence.
      + reduce_setPass. cbn in *.
        propify.
        destruct_and_split.
        inversion receive_some. simpl.
        propify.
        destruct_and_split.
        unfold one_ether in *.
        lia.
        inversion receive_some. simpl.
        propify.
        destruct_and_split.
        unfold one_ether in *.
        lia.
      + reduce_getGift . cbn in *.
        inversion receive_some. simpl.
        propify.
        unfold require_zero in Ezero.
        lia.
      + reduce_passHasBeenSet_fn. cbn in *.
        inversion receive_some. simpl.
        unfold require_zero in Ezero.
        propify.
        lia.
      + inversion receive_some. simpl.
        propify.
        lia.
    - reduce_receive.
      destruct_message;try congruence.
      + reduce_setPass. cbn in *.
        propify.
        destruct_and_split.
        inversion receive_some. simpl.
        propify.
        destruct_and_split.
        unfold one_ether in *.
        inversion receive_some; destruct head; cbn in *; lia.
        inversion receive_some. simpl.
        propify.
        destruct_and_split.
        unfold one_ether in *.
        inversion receive_some; destruct head; cbn in *; lia.
      + reduce_getGift . cbn in *.
        inversion receive_some. simpl.
        propify.
        unfold require_zero in Ezero.
        inversion receive_some; destruct head; cbn in *; lia.
      + reduce_passHasBeenSet_fn. cbn in *.
        inversion receive_some. simpl.
        unfold require_zero in Ezero.
        propify.
        inversion receive_some; destruct head; cbn in *; try lia.
      + inversion receive_some. simpl.
        propify.
        inversion receive_some; destruct head; cbn in *; lia.
    - now erewrite sumZ_permutation in IH by eauto.
    - solve_facts.
  Qed.

  Lemma balance_on_chain:
    forall bstate caddr,
      reachable bstate ->
      env_contracts bstate caddr = Some (contract : WeakContract) ->
      outgoing_acts bstate caddr = [] ->
      exists cstate,
        contract_state bstate caddr = Some cstate /\
        env_account_balances bstate caddr = cstate.(balance).
  Proof.
    intros * reach deployed.
    specialize balance_on_chain' as (cstate & balance); eauto.
    eauto.
    intros Hact. rewrite Hact in balance. cbn in *.
    exists cstate. destruct balance.
    split.
    eauto.
    lia.
  Qed.

  Lemma balance_on_chain_forall :
    forall bstate caddr cstate,
      reachable bstate ->
      env_contracts bstate caddr = Some (contract : WeakContract) ->
      outgoing_acts bstate caddr = [] ->
      contract_state bstate caddr = Some cstate ->
      env_account_balances bstate caddr = cstate.(balance).
  Proof.
    intros.
    eapply balance_on_chain in H;eauto.
    destruct H;
    destruct_and_split.
    rewrite H2 in H.
    inversion H; subst;
    eauto.
  Qed.

  Lemma get_valid_header_is_valid_header s:
    validate_header( get_valid_header miner s )  s = true.
  Proof.
    intros.
    unfold get_valid_header.
    unfold validate_header.
    propify.
    repeat split;cbn ;try lia;eauto.
    unfold miner_reward.
    lia.
  Qed.

  Lemma user_call_GetGift_is_call_act cstate:
    is_call_act (user_call_GetGift cstate) = true .
  Proof.
    unfold is_call_act.
    unfold user_call_GetGift.
    simpl.
    destruct_address_eq;eauto.
  Qed.

  Lemma honest_call_GetGift_is_call_act cstate:
    is_call_act (honest_call_GetGift cstate) = true .
  Proof.
    unfold is_call_act.
    unfold honest_call_GetGift.
    simpl.
    destruct_address_eq;eauto.
  Qed.

  Lemma attacker_call_SetPass_is_call_act cstate:
    is_call_act (attacker_call_SetPass cstate) = true .
  Proof.
    unfold is_call_act.
    unfold attacker_call_SetPass.
    simpl.
    destruct_address_eq;eauto.
  Qed.

  Lemma attacker_call_PassHasBeenSetMsg_is_call_act cstate:
    is_call_act (attacker_call_PassHasBeenSetMsg cstate) = true .
  Proof.
    unfold is_call_act.
    unfold attacker_call_PassHasBeenSetMsg.
    simpl.
    destruct_address_eq;eauto.
  Qed.

  
  Lemma honest_call_SetPass_is_call_act cstate:
    is_call_act (honest_call_SetPass cstate) = true .
  Proof.
    unfold is_call_act.
    unfold honest_call_SetPass.
    simpl.
    destruct_address_eq;eauto.
  Qed.

  Lemma honest_call_PassHasBeenSetMsg_is_call_act cstate:
    is_call_act ( honest_call_PassHasBeenSetMsg cstate) = true .
  Proof.
    unfold is_call_act.
    unfold honest_call_PassHasBeenSetMsg.
    simpl.
    destruct_address_eq;eauto.
  Qed.

  Local Open Scope Z.

  Lemma user_call_GetGift_is_call_act_transition_correct:
    forall (s:ChainState) cstate,
      contract_state s caddr = Some cstate ->
      transition_reachable miner contract caddr s0 s ->
      exists s', 
        transition miner s (user_call_GetGift cstate) = Ok s'.
  Proof.
    intros * Hcs_s Htrc_s.
    eexists.
    unfold transition.
    unfold queue_isb_empty.
    eapply transition_reachable_queue_is_empty in Htrc_s as Hqueue_s;eauto.
    rewrite Hqueue_s.
    rewrite user_call_GetGift_is_call_act.
    unfold evaluate_action.
    rewrite get_valid_header_is_valid_header.
    unfold user_call_GetGift .
    simpl.
    destruct_address_eq;try congruence.
    simpl.
    assert (Hec_s:env_contracts s caddr = Some (contract:WeakContract)).
    {
      eapply transition_reachable_impl_reachable_through in Htrc_s.
      eapply reachable_through_contract_deployed in Htrc_s;eauto.
      decompose_is_init_state H_init.
      eauto.
      eauto.
    }
    eapply address_not_contract_negb in user1_eoa.
    rewrite user1_eoa.
    unfold send_or_call.
    simpl.
    assert( H_caddr_not_EOA : address_is_contract caddr = true).
    {
      eapply contract_addr_format in Hec_s;eauto.
      eapply transition_reachable_impl_reachable in Htrc_s;eauto.  
    }
    assert(Hrc_s:reachable s).
    {
      eapply transition_reachable_impl_reachable in Htrc_s;eauto.
    }
    assert(Hbal:env_account_balances s caddr = cstate.(balance)).
    {
      eapply balance_on_chain_forall;eauto.
      unfold outgoing_acts.
      rewrite Hqueue_s.
      simpl.
      eauto.
    }
    destruct_address_eq;try congruence.
    + assert ((0 >? miner_reward + env_account_balances s user1 )%Z 
                = false).
      {
        unfold miner_reward.
        eapply (account_balance_nonnegative s user1) in Hrc_s.
        lia.
      }
      rewrite H.
      rewrite Hec_s.
      unfold contract_state in Hcs_s.
      simpl in Hcs_s.
      destruct (env_contract_states s caddr) eqn : Hecs_s;try congruence.
      simpl.
      rewrite Hcs_s.
      simpl.
      setoid_rewrite deserialize_serialize.
      simpl.
      cbn in *.
      unfold receive.
      simpl.
      unfold address_not_contract.
      specialize(hashPass_kown_all_state s cstate).
      rewrite Hecs_s in hashPass_kown_all_state.
      specialize(hashPass_kown_all_state Hcs_s).
      rewrite <- hashPass_kown_all_state.
      simpl.
      simpl.
      assert (Hn_eq : N.eqb (hashPass cstate) (hashPass cstate) = true).
      {
        apply N.eqb_refl.
      }
      rewrite Hn_eq.
      simpl.
      unfold send_or_call.
      assert(balance cstate <? 0 = false).
      {
        eapply (account_balance_nonnegative s caddr) in Hrc_s.
        propify.
        lia.
      }
      rewrite H0.
      simpl.
      destruct_address_eq;try congruence.
      assert(balance cstate >? 0 + (env_account_balances s caddr) = false)%Z.
      {
        propify.
        lia.
      }
      rewrite H1.
      assert (H_sender_none: env_contracts s user1 = None).
      { 
        destruct (env_contracts s user1) eqn:H_env.
        - exfalso.
          apply (contract_addr_format user1 w) in H_env; eauto.
          congruence.
        - reflexivity.
      }
      rewrite H_sender_none.
      rewrite user1_eoa.
      simpl.
      eauto.
    + assert ((0 >?  env_account_balances s user1 )%Z 
                = false).
      {
        unfold miner_reward.
        eapply (account_balance_nonnegative s user1) in Hrc_s.
        lia.
      }
      rewrite H.
      rewrite Hec_s.
      unfold contract_state in Hcs_s.
      simpl in Hcs_s.
      destruct (env_contract_states s caddr) eqn : Hecs_s;try congruence.
      simpl.
      rewrite Hcs_s.
      simpl.
      setoid_rewrite deserialize_serialize.
      simpl.
      cbn in *.
      unfold receive.
      simpl.
      unfold address_not_contract.
      specialize(hashPass_kown_all_state s cstate).
      rewrite Hecs_s in hashPass_kown_all_state.
      specialize(hashPass_kown_all_state Hcs_s).
      rewrite <- hashPass_kown_all_state.
      simpl.
      simpl.
      assert (Hn_eq : N.eqb (hashPass cstate) (hashPass cstate) = true).
      {
        apply N.eqb_refl.
      }
      rewrite Hn_eq.
      simpl.
      unfold send_or_call.
      assert(balance cstate <? 0 = false).
      {
        eapply (account_balance_nonnegative s caddr) in Hrc_s.
        propify.
        lia.
      }
      rewrite H0.
      simpl.
      destruct_address_eq;try congruence.
      assert(balance cstate >? 0 + (miner_reward + env_account_balances s caddr) =false)%Z.
      {
        unfold miner_reward.
        lia.
      }
      rewrite H1.
      assert (H_sender_none: env_contracts s user1 = None).
      { 
        destruct (env_contracts s user1) eqn:H_env.
        - exfalso.
          apply (contract_addr_format user1 w) in H_env; eauto.
          congruence.
        - reflexivity.
      }
      rewrite H_sender_none.
      rewrite user1_eoa.
      simpl.
      eauto.
    + assert ((0 >?  env_account_balances s user1 )%Z 
                = false).
      {
        unfold miner_reward.
        eapply (account_balance_nonnegative s user1) in Hrc_s.
        lia.
      }
      rewrite H.
      rewrite Hec_s.
      unfold contract_state in Hcs_s.
      simpl in Hcs_s.
      destruct (env_contract_states s caddr) eqn : Hecs_s;try congruence.
      simpl.
      rewrite Hcs_s.
      simpl.
      setoid_rewrite deserialize_serialize.
      simpl.
      cbn in *.
      unfold receive.
      simpl.
      unfold address_not_contract.
      specialize(hashPass_kown_all_state s cstate).
      rewrite Hecs_s in hashPass_kown_all_state.
      specialize(hashPass_kown_all_state Hcs_s).
      rewrite <- hashPass_kown_all_state.
      simpl.
      simpl.
      assert (Hn_eq : N.eqb (hashPass cstate) (hashPass cstate) = true).
      {
        apply N.eqb_refl.
      }
      rewrite Hn_eq.
      simpl.
      unfold send_or_call.
      assert(balance cstate <? 0 = false).
      {
        eapply (account_balance_nonnegative s caddr) in Hrc_s.
        propify.
        lia.
      }
      rewrite H0.
      simpl.
      destruct_address_eq;try congruence.
      assert(balance cstate >? 0 + ( env_account_balances s caddr) =false)%Z.
      {
        unfold miner_reward.
        lia.
      }
      rewrite H1.
      assert (H_sender_none: env_contracts s user1 = None).
      { 
        destruct (env_contracts s user1) eqn:H_env.
        - exfalso.
          apply (contract_addr_format user1 w) in H_env; eauto.
          congruence.
        - reflexivity.
      }
      rewrite H_sender_none.
      rewrite user1_eoa.
      simpl.
      eauto.
  Qed.

  Lemma user_call_GetGift_is_call_act_state_correct:
   forall (s s':ChainState) cstate,
      contract_state s caddr = Some cstate ->
      transition_reachable miner contract caddr s0 s ->
      transition miner s (user_call_GetGift cstate) = Ok s' ->
      exists cstate',
        contract_state s' caddr = Some cstate' /\
        cstate'.(balance) = 0.
  Proof.
    intros * Hcs_s Htrc_s Htrans.
    eapply transition_reachable_queue_is_empty in Htrc_s as Hqueue_s;eauto.
    assert (Hact_call : is_call_act ((user_call_GetGift cstate)) = true).
    {
      unfold is_call_act.
      unfold user_call_GetGift.
      unfold build_call.
      destruct_address_eq;eauto.
    }
    assert(ttrace_s_s : TransitionTrace miner s s) by eapply clnil.
    assert(ttrace_s_s' : TransitionTrace miner s s').
    {
      econstructor;eauto.
      eapply step_trans;eauto.

    }
    assert(Htrct_s_s' : reachable_via miner contract caddr s0 s s').
    {
      econstructor;eauto.
    }
    assert(Hrt : reachable_through s s').
    {
      eapply reachable_via_impl_reachable_through in Htrct_s_s';eauto.
    }
    assert(H_t: reachable s') by eauto.
    destruct H_t as [trace].
    assert (Hec_s : env_contracts s caddr = Some ((contract : WeakContract))).
    {
      pose proof H_init.
      decompose_is_init_state H_init.
      eapply reachable_through_contract_deployed in H_env_contracts.
      eauto.
      eapply transition_reachable_impl_reachable_through in Htrc_s;eauto.
    }
    assert (Hec_s' : env_contracts s' caddr = Some ((contract : WeakContract))).
    {
      pose proof H_init.
      decompose_is_init_state H_init.
      eapply reachable_through_contract_deployed in H_env_contracts.
      eauto.
      eapply transition_reachable_impl_reachable_through in Htrc_s;eauto.
    }
    eapply deployed_contract_state_typed in Hec_s';eauto.
    destruct Hec_s' as [cstate_s' Hcs_s'].
    exists cstate_s'.
    split.
    eauto.
    unfold transition in Htrans.
    unfold queue_isb_empty in Htrans.
    rewrite Hqueue_s in Htrans.
    rewrite Hact_call in Htrans.
    destruct (evaluate_action true s (get_valid_header miner s)
    [user_call_GetGift cstate ]) eqn : H_exec;try congruence.
    unfold evaluate_action in H_exec.
    rewrite get_valid_header_is_valid_header in H_exec.
    destruct (find_origin_neq_from [user_call_GetGift cstate]) ; try congruence.
    destruct (find_invalid_root_action [user_call_GetGift cstate]);try congruence.
    set (mid_state := {|
      chain_state_env := add_new_block_to_env (get_valid_header miner s) s;
      chain_state_queue := [user_call_GetGift cstate]
    |}) in H_exec.
    simpl in *.
    destruct(send_or_call user1 user1 caddr 0
    (Some (serialize (GetGift correct_pass)))
    (add_new_block_to_env (get_valid_header miner s) s)) eqn : H_send_or_call_GetGift;try congruence.
    unfold send_or_call in  H_send_or_call_GetGift.
    simpl in H_send_or_call_GetGift.
    eapply address_not_contract_negb in H_miner.
    assert( H_caddr_not_EOA : address_is_contract caddr = true).
    {
      eapply contract_addr_format in Hec_s;eauto.
      eapply transition_reachable_impl_reachable in Htrc_s;eauto.  
    }
    destruct_address_eq;simpl in *;try congruence.
    
    (* 
      e: sender cstate = miner
      n: caddr <> sender cstate
      e0: caddr = caddr
      n0: caddr <> miner 
    *)
    destruct(0 >? miner_reward + env_account_balances s user1)%Z;try congruence.
    rewrite Hec_s in H_send_or_call_GetGift.
    assert(Hcstate_s_t0:contract_state s caddr = Some cstate) by eauto.
    unfold contract_state in Hcstate_s_t0.
    simpl in Hcstate_s_t0.
    destruct (env_contract_states s caddr) eqn : Hcstate_s_t0';try congruence.
    destruct (weak_error_to_error_receive
    (wc_receive contract
        (s <| chain_height := S (chain_height s) |> <|
        current_slot := (current_slot s + 1)%nat |> <|
        finalized_height := finalized_height s |>)
        {|
          ctx_origin := user1;
          ctx_from := user1;
          ctx_contract_address := caddr;
          ctx_contract_balance := 0 + env_account_balances s caddr;
          ctx_amount := 0
        |} s1 (Some (serialize (GetGift correct_pass))))) eqn : H_wc_receive_s1;try congruence.
    unfold weak_error_to_error_receive in H_wc_receive_s1.
    unfold bind_error in H_wc_receive_s1.
    destruct (wc_receive contract
    (s <| chain_height := S (chain_height s) |> <| current_slot :=
      (current_slot s + 1)%nat |> <| finalized_height :=
      finalized_height s |>)
    {|
      ctx_origin := user1;
      ctx_from := user1;
      ctx_contract_address := caddr;
      ctx_contract_balance := 0 + env_account_balances s caddr;
      ctx_amount := 0
    |} s1 (Some (serialize (GetGift correct_pass))))
      eqn : H_wc_receive_s1';try congruence.
    
    set (cchain := s <| chain_height := S (chain_height s) |> <| current_slot :=
    (current_slot s + 1)%nat |> <| finalized_height :=
    finalized_height s |>) in H_wc_receive_s1'.
    set (cctx := {|
    ctx_origin := user1;
    ctx_from := user1;
    ctx_contract_address := caddr;
    ctx_contract_balance := 0 + env_account_balances s caddr;
    ctx_amount := 0
    |}) in H_wc_receive_s1'.
    
    destruct t2 as [new_state new_acts].

    destruct (wc_receive_strong ltac:(try eassumption))
    as (prev_state_strong & msg_strong & resp_state_strong &
      deser_state & deser_msg & <- & receive).

    simpl in deser_msg.
    destruct (msg_strong) eqn : H_msg;try congruence.
    rewrite deserialize_serialize in deser_msg.
    rewrite <- deser_msg in receive.
    rewrite deser_state in Hcstate_s_t0.
    simpl in receive.
    rename receive into receive_some.
    unfold receive in receive_some.
    reduce_getGift.
    (* 111 *)
    inversion receive_some.
    subst.
    inversion H_wc_receive_s1;subst.
    inversion H_send_or_call_GetGift;subst.
    simpl in H_exec.
    destruct (  send_or_call (user1) caddr ((user1))
    (balance prev_state_strong) None
    (set_contract_state caddr
       (serialize
          (prev_state_strong <| balance := 0 |>))
       (transfer_balance (user1) caddr 0
          (add_new_block_to_env (get_valid_header (user1) s) s)))) eqn : H_send_or_call_None;try congruence.
    unfold send_or_call in H_send_or_call_None.
    destruct_match in H_send_or_call_None;try congruence.
    destruct_match in H_send_or_call_None;try congruence.
    destruct (
      env_contracts
      (set_contract_state caddr
         (serialize
            (prev_state_strong <| balance := 0 |>))
         (transfer_balance (user1) caddr 0
            (add_new_block_to_env
               (get_valid_header (user1) s) s)))
      ((user1)) ) 
    eqn : H_none_wc.
    set (
        mid_env:=(set_contract_state caddr
          (serialize (prev_state_strong <| balance := 0 |>))
          (transfer_balance (user1) caddr 0
              (add_new_block_to_env (get_valid_header (user1) s) s)))) 
    in H_none_wc.
    set (
      mid_mid_end_state := {|
      chain_state_env :=
      mid_env;
      chain_state_queue :=
        [{|
            act_origin := user1;
            act_from := caddr;
            act_body :=
              act_transfer ((user1))
                (balance prev_state_strong)
          |}]
      |}
    ).
    assert(Hreachable_through_s'_mid_mid_end_state : reachable_through s mid_mid_end_state).
    {
      assert(step_s'_mid : ChainStep s mid_state).
      {
        eapply (step_block s mid_state  (get_valid_header (user1) s));eauto.
        unfold get_valid_header.
        eapply build_is_valid_next_block;simpl;intuition;eauto.
        unfold miner_reward.
        lia.
        eapply Forall_forall.
        intros.
        simpl in H.
        destruct H.
        rewrite <- H.
        unfold act_is_from_account.
        simpl.
        intuition.
        intuition.
        eapply Forall_forall;eauto.
        intros.
        simpl in H.
        destruct H;eauto;intuition.
        rewrite <- H.
        unfold act_origin_is_eq_from.
        simpl.
        destruct_address_eq;try congruence.
        eapply build_env_equiv;eauto.
      }
      assert(reachable_through s mid_state).
      {
        assert(tt:ChainTrace s s) by eapply clnil.
        assert(tt' : ChainTrace s mid_state).
        {
          eapply snoc;eauto.
        }
        econstructor;eauto.
        eapply transition_reachable_impl_reachable in Htrc_s;eauto.
      }
      assert(step_mid_end : ChainStep mid_state mid_mid_end_state).
      {
        eapply (step_action mid_state mid_mid_end_state (user_call_GetGift cstate) [] 
        [{|
          act_origin := user1;
          act_from := caddr;
          act_body :=
            act_transfer ((user1))
              (balance prev_state_strong)
        |}] )
        ;eauto.
        eapply (eval_call (user1) (user1) caddr 0 
          (contract:WeakContract) (Some (serialize (GetGift correct_pass)))
          ( s1) (serialize (prev_state_strong <| balance := 0 |>)) 
          [act_transfer ((user1)) (balance prev_state_strong)]);eauto;intuition.
        eapply reachable_through_reachable in H.
        eapply (account_balance_nonnegative mid_state (user1)) in H.
        lia.
        eauto.
        unfold user_call_GetGift.
        unfold build_call.
        intuition.
        eapply build_env_equiv;eauto.
      }
      assert(reachable mid_state).
      {
        eapply reachable_through_reachable;eauto.
      }
      eapply reachable_through_step in H0;eauto.
    }
    assert(H_mid_mid_eq_env_mid:mid_mid_end_state.(chain_state_env) = mid_env).
    {
      simpl.
      eauto.
    }
    assert(Hreachable_mid_mid: reachable mid_mid_end_state).
    {
      eapply reachable_through_reachable;eauto.
    }
    eapply (address_not_contract_not_wc ((user1))) in Hreachable_mid_mid.
    intuition.
    intuition.
    inversion  Hcstate_s_t0.
    rewrite H0 in H_send_or_call_None.
    eapply address_not_contract_negb in user1_eoa.
    rewrite user1_eoa in H_send_or_call_None.
    inversion H_send_or_call_None;subst.
    simpl in H_exec.
    inversion H_exec;subst.
    inversion Htrans.
    subst.
    inversion Hcs_s'.
    unfold contract_state in H0.
    simpl in H0.
    destruct_address_eq;eauto.
    setoid_rewrite deserialize_serialize in H0.
    inversion H0.
    intuition.
    simpl.
    eauto.
    intuition.
    specialize (hashPass_kown_all_state s cstate Hcs_s ).
    propify.
    eapply address_not_contract_negb in user1_eoa.
    rewrite e in *.
    intuition.

    (* caddr = miner *)
    (* eapply address_not_contract_negb in user1_eoa.
    rewrite e in *.
    intuition. *)
    (* 
      n: sender cstate <> miner
      n0: caddr <> sender cstate
      e: caddr = caddr
      n1: caddr <> miner
    *)
    destruct(0 >? env_account_balances s user1)%Z;try congruence.
    rewrite Hec_s in H_send_or_call_GetGift.
    assert(Hcstate_s_t0:contract_state s caddr = Some cstate) by eauto.
    unfold contract_state in Hcstate_s_t0.
    simpl in Hcstate_s_t0.
    destruct (env_contract_states s caddr) eqn : Hcstate_s_t0';try congruence.
    destruct (weak_error_to_error_receive
    (wc_receive contract
        (s <| chain_height := S (chain_height s) |> <|
        current_slot := (current_slot s + 1)%nat |> <|
        finalized_height := finalized_height s |>)
        {|
          ctx_origin := user1;
          ctx_from := user1;
          ctx_contract_address := caddr;
          ctx_contract_balance := 0 + env_account_balances s caddr;
          ctx_amount := 0
        |} s1 (Some (serialize (GetGift correct_pass))))) eqn : H_wc_receive_s1;try congruence.
    unfold weak_error_to_error_receive in H_wc_receive_s1.
    unfold bind_error in H_wc_receive_s1.
    destruct (wc_receive contract
    (s <| chain_height := S (chain_height s) |> <| current_slot :=
      (current_slot s + 1)%nat |> <| finalized_height :=
      finalized_height s |>)
    {|
      ctx_origin := user1;
      ctx_from := user1;
      ctx_contract_address := caddr;
      ctx_contract_balance := 0 + env_account_balances s caddr;
      ctx_amount := 0
    |} s1 (Some (serialize (GetGift correct_pass))))
      eqn : H_wc_receive_s1';try congruence.
    
    set (cchain := s <| chain_height := S (chain_height s) |> <| current_slot :=
    (current_slot s + 1)%nat |> <| finalized_height :=
    finalized_height s |>) in H_wc_receive_s1'.
    set (cctx := {|
    ctx_origin := user1;
    ctx_from := user1;
    ctx_contract_address := caddr;
    ctx_contract_balance := 0 + env_account_balances s caddr;
    ctx_amount := 0
    |}) in H_wc_receive_s1'.
    
    destruct t2 as [new_state new_acts].

    destruct (wc_receive_strong ltac:(try eassumption))
    as (prev_state_strong & msg_strong & resp_state_strong &
      deser_state & deser_msg & <- & receive).

    simpl in deser_msg.
    destruct (msg_strong) eqn : H_msg;try congruence.
    rewrite deserialize_serialize in deser_msg.
    rewrite <- deser_msg in receive.
    rewrite deser_state in Hcstate_s_t0.
    simpl in receive.
    rename receive into receive_some.
    unfold receive in receive_some.
    reduce_getGift.
    (* 111 *)
    inversion receive_some.
    subst.
    inversion H_wc_receive_s1;subst.
    inversion H_send_or_call_GetGift;subst.
    simpl in H_exec.
    destruct (  send_or_call (user1) caddr ((user1))
    (balance prev_state_strong) None
    (set_contract_state caddr
       (serialize
          (prev_state_strong <| balance := 0 |>))
       (transfer_balance (user1) caddr 0
          (add_new_block_to_env (get_valid_header (miner) s) s)))) eqn : H_send_or_call_None;try congruence.
    unfold send_or_call in H_send_or_call_None.
    destruct_match in H_send_or_call_None;try congruence.
    destruct_match in H_send_or_call_None;try congruence.
    destruct (
      env_contracts
      (set_contract_state caddr
         (serialize
            (prev_state_strong <| balance := 0 |>))
         (transfer_balance (user1) caddr 0
            (add_new_block_to_env
               (get_valid_header (miner) s) s)))
      ((user1)) ) 
    eqn : H_none_wc.
    set (
        mid_env:=(set_contract_state caddr
          (serialize (prev_state_strong <| balance := 0 |>))
          (transfer_balance (user1) caddr 0
              (add_new_block_to_env (get_valid_header (miner) s) s)))) 
    in H_none_wc.
    set (
      mid_mid_end_state := {|
      chain_state_env :=
      mid_env;
      chain_state_queue :=
        [{|
            act_origin := user1;
            act_from := caddr;
            act_body :=
              act_transfer ((user1))
                (balance prev_state_strong)
          |}]
      |}
    ).
    assert(Hreachable_through_s'_mid_mid_end_state : reachable_through s mid_mid_end_state).
    {
      assert(step_s'_mid : ChainStep s mid_state).
      {
        eapply (step_block s mid_state  (get_valid_header (miner) s));eauto.
        unfold get_valid_header.
        eapply build_is_valid_next_block;simpl;intuition;eauto.
        unfold miner_reward.
        lia.
        eapply Forall_forall.
        intros.
        simpl in H.
        destruct H.
        rewrite <- H.
        unfold act_is_from_account.
        simpl.
        intuition.
        eapply address_not_contract_negb in user1_eoa.
        eauto.
        eapply Forall_forall;eauto.
        intros.
        eapply Forall_forall;eauto.
        intros.
        simpl in H.
        destruct H;eauto;intuition.
        rewrite <- H.
        unfold act_origin_is_eq_from.
        simpl.
        destruct_address_eq;try congruence.
        eapply build_env_equiv;eauto.
      }
      assert(reachable_through s mid_state).
      {
        assert(tt:ChainTrace s s) by eapply clnil.
        assert(tt' : ChainTrace s mid_state).
        {
          eapply snoc;eauto.
        }
        econstructor;eauto.
        eapply transition_reachable_impl_reachable in Htrc_s;eauto.
      }
      assert(step_mid_end : ChainStep mid_state mid_mid_end_state).
      {
        eapply (step_action mid_state mid_mid_end_state (user_call_GetGift cstate) [] 
        [{|
          act_origin := user1;
          act_from := caddr;
          act_body :=
            act_transfer ((user1))
              (balance prev_state_strong)
        |}] )
        ;eauto.
        eapply (eval_call (user1) (user1) caddr 0 
          (contract:WeakContract) (Some (serialize (GetGift correct_pass)))
          ( s1) (serialize (prev_state_strong <| balance := 0 |>)) 
          [act_transfer ((user1)) (balance prev_state_strong)]);eauto;intuition.
        eapply reachable_through_reachable in H.
        eapply (account_balance_nonnegative mid_state (user1)) in H.
        lia.
        eauto.
        unfold user_call_GetGift.
        unfold build_call.
        intuition.
        eapply build_env_equiv;eauto.
      }
      assert(reachable mid_state).
      {
        eapply reachable_through_reachable;eauto.
      }
      eapply reachable_through_step in H0;eauto.
    }
    assert(H_mid_mid_eq_env_mid:mid_mid_end_state.(chain_state_env) = mid_env).
    {
      simpl.
      eauto.
    }
    assert(Hreachable_mid_mid: reachable mid_mid_end_state).
    {
      eapply reachable_through_reachable;eauto.
    }
    eapply (address_not_contract_not_wc ((user1))) in Hreachable_mid_mid.
    intuition.
    intuition.
    inversion  Hcstate_s_t0.
    rewrite H0 in H_send_or_call_None.
    eapply address_not_contract_negb;eauto.
    eapply address_not_contract_negb in user1_eoa.
    rewrite user1_eoa in H_send_or_call_None.
    inversion H_send_or_call_None;subst.
    simpl in H_exec.
    inversion H_exec;subst.
    inversion Htrans.
    subst.
    inversion Hcs_s'.
    unfold contract_state in H0.
    simpl in H0.
    destruct_address_eq;eauto.
    setoid_rewrite deserialize_serialize in H0.
    inversion H0.
    intuition.
    simpl.
    eauto.
    intuition.
  Qed.

  Lemma honeypot_satisfy_base_liquidity:
    base_liquidity miner contract caddr s0.
  Proof.
    unfold base_liquidity.
    intros.
    clear H.
    pose proof H_state.
    unfold get_contract_state in H_state.
    pose proof H_init as H_init'.
    decompose_is_init_state H_init'.
    rewrite H_env_states in H_state.
    rewrite deserialize_serialize in H_state.
    rename H_state into H_state_eq.
    rename H into H_state.
    pose proof H0 as Htrc_s.
    eapply transition_reachable_queue_is_empty in Htrc_s as Hqueue_s;eauto.
    assert(Hrct_s0_s : reachable_through s0 s).
    {
      eapply transition_reachable_impl_reachable_through in Htrc_s;eauto.
    }
    assert(Hcs_s :exists (cstate:State), contract_state s caddr = Some cstate).
    {
      eapply reachable_through_contract_deployed in Hrct_s0_s;eauto.
      eapply deployed_contract_state_typed in Hrct_s0_s;eauto.
      eapply transition_reachable_impl_reachable in Htrc_s;eauto.
    }
    destruct Hcs_s as [cstate Hcs_s].
    assert(Hdeployed : env_contracts s caddr = Some (contract: WeakContract)).
    {
      eapply reachable_through_contract_deployed;eauto.
    }
    assert( H_caddr_not_EOA : address_is_contract caddr = true).
    {
      eapply contract_addr_format in Hdeployed.
      eauto.
      eapply transition_reachable_impl_reachable in Htrc_s;eauto.
    }
    pose proof Htrc_s.
    eapply user_call_GetGift_is_call_act_transition_correct in H;eauto.
    destruct H as [s' Htrans].
    pose proof Htrans.
    eapply user_call_GetGift_is_call_act_state_correct in H;eauto.
    destruct H as [cstate' [Hcs_s' HPhase]].
    assert (Htrc_s':transition_reachable miner contract caddr s0 s').
    {
      econstructor;eauto.
      decompose_transition_reachable Htrc_s.
      econstructor;eauto.
      assert(is_call_act (user_call_GetGift cstate') = true).
      {
        eapply (user_call_GetGift_is_call_act cstate').
      }
      
      eapply (snoc trace (step_trans miner (user_call_GetGift cstate') H  Htrans)).
    }
    assert (trace_s_s' :inhabited(TransitionTrace miner s s')).
    {
      decompose_transition_reachable Htrc_s.
      assert (TransitionTrace miner s s) by eapply clnil.
      assert(is_call_act (user_call_GetGift cstate) = true).
      {
        eapply (user_call_GetGift_is_call_act cstate).
      }
      econstructor;eauto.
      eapply (snoc X (step_trans miner (user_call_GetGift  cstate) H  Htrans)).
    }
    eapply transition_reachable_impl_reachable in Htrc_s' as H.
    eapply balance_on_chain_forall in H;eauto.
    exists s'.
    split.
    eauto.
    eauto.
    unfold funds.
    intuition.
    eapply transition_reachable_impl_reachable_through in Htrc_s';eauto.
    eapply reachable_through_contract_deployed in Htrc_s';eauto.
    unfold outgoing_acts.
    eapply transition_reachable_queue_is_empty in Htrc_s'.
    rewrite Htrc_s'.
    intuition.
    eauto.
    eauto.
  Qed.

  Lemma honest_call_GetGift_is_call_act_transition_correct_nopass:
  forall (s:ChainState) cstate,
    contract_state s caddr = Some cstate ->
    transition_reachable miner contract caddr s0 s ->
    cstate.(passHasBeenSet) = true ->
    cstate.(hashPass) <> sha3 honest_pass ->
    transition miner s (honest_call_GetGift cstate) = Err StratModel.default_error.
  Proof.
    intros * Hcs_s Htrc_s H_passB H_neq.
    unfold transition.
    unfold queue_isb_empty.
    eapply transition_reachable_queue_is_empty in Htrc_s as Hqueue_s;eauto.
    rewrite Hqueue_s.
    rewrite honest_call_GetGift_is_call_act.
    unfold evaluate_action.
    rewrite get_valid_header_is_valid_header.
    unfold user_call_GetGift .
    simpl.
    destruct_address_eq;try congruence.
    simpl.
    assert (Hec_s:env_contracts s caddr = Some (contract:WeakContract)).
    {
      eapply transition_reachable_impl_reachable_through in Htrc_s.
      eapply reachable_through_contract_deployed in Htrc_s;eauto.
      decompose_is_init_state H_init.
      eauto.
      eauto.
    }
    eapply address_not_contract_negb in honest_eoa.
    rewrite honest_eoa.
    unfold send_or_call.
    simpl.
    assert( H_caddr_not_EOA : address_is_contract caddr = true).
    {
      eapply contract_addr_format in Hec_s;eauto.
      eapply transition_reachable_impl_reachable in Htrc_s;eauto.  
    }
    assert(Hrc_s:reachable s).
    {
      eapply transition_reachable_impl_reachable in Htrc_s;eauto.
    }
    assert(Hbal:env_account_balances s caddr = cstate.(balance)).
    {
      eapply balance_on_chain_forall;eauto.
      unfold outgoing_acts.
      rewrite Hqueue_s.
      simpl.
      eauto.
    }
    destruct_address_eq;try congruence.
    + assert ((0 >? miner_reward + env_account_balances s honest )%Z 
                = false).
      {
        unfold miner_reward.
        eapply (account_balance_nonnegative s honest) in Hrc_s.
        lia.
      }
      rewrite H.
      rewrite Hec_s.
      unfold contract_state in Hcs_s.
      simpl in Hcs_s.
      destruct (env_contract_states s caddr) eqn : Hecs_s;try congruence.
      simpl.
      rewrite Hcs_s.
      simpl.
      setoid_rewrite deserialize_serialize.
      simpl.
      cbn in *.
      unfold receive.
      simpl.
      simpl.
      destruct (hashPass cstate =? sha3 honest_pass)%N eqn : N.
      - propify. intuition.
      - propify. 
        simpl.
        
        eauto.
    + assert ((0 >?  env_account_balances s honest )%Z 
                = false).
      {
        unfold miner_reward.
        eapply (account_balance_nonnegative s honest) in Hrc_s.
        lia.
      }
      rewrite H.
      rewrite Hec_s.
      unfold contract_state in Hcs_s.
      simpl in Hcs_s.
      destruct (env_contract_states s caddr) eqn : Hecs_s;try congruence.
      simpl.
      rewrite Hcs_s.
      simpl.
      setoid_rewrite deserialize_serialize.
      simpl.
      cbn in *.
      unfold receive.
      simpl.
      unfold address_not_contract.
      destruct (hashPass cstate =? sha3 honest_pass)%N eqn : N.
      - propify. intuition.
      - propify. 
        simpl.
        
        eauto.
    + assert ((0 >?  env_account_balances s honest )%Z 
                = false).
      {
        unfold miner_reward.
        eapply (account_balance_nonnegative s honest) in Hrc_s.
        lia.
      }
      rewrite H.
      rewrite Hec_s.
      unfold contract_state in Hcs_s.
      simpl in Hcs_s.
      destruct (env_contract_states s caddr) eqn : Hecs_s;try congruence.
      simpl.
      rewrite Hcs_s.
      simpl.
      setoid_rewrite deserialize_serialize.
      simpl.
      cbn in *.
      unfold receive.
      simpl.
      unfold address_not_contract.
      destruct (hashPass cstate =? sha3 honest_pass)%N eqn : N.
      - propify. intuition.
      - propify. 
        simpl.
        eauto.
  Qed.

  Lemma honest_call_SetPass_is_call_act_transition_correct_nopass:
    forall (s:ChainState) cstate,
      contract_state s caddr = Some cstate ->
      transition_reachable miner contract caddr s0 s ->
      cstate.(passHasBeenSet) = true ->
      cstate.(hashPass) <> sha3 honest_pass ->
      exists s',
      transition miner s (honest_call_SetPass cstate) = Ok s'.
  Proof.
    intros * Hcs_s Htrc_s H_passB H_pass .
    eexists.
    unfold transition.
    unfold queue_isb_empty.
    eapply transition_reachable_queue_is_empty in Htrc_s as Hqueue_s;eauto.
    rewrite Hqueue_s.
    rewrite honest_call_SetPass_is_call_act.
    unfold evaluate_action.
    rewrite get_valid_header_is_valid_header.
    unfold user_call_GetGift .
    simpl.
    destruct_address_eq;try congruence.
    simpl.
    assert (Hec_s:env_contracts s caddr = Some (contract:WeakContract)).
    {
      eapply transition_reachable_impl_reachable_through in Htrc_s.
      eapply reachable_through_contract_deployed in Htrc_s;eauto.
      decompose_is_init_state H_init.
      eauto.
      eauto.
    }
    eapply address_not_contract_negb in honest_eoa.
    rewrite honest_eoa.
    unfold send_or_call.
    simpl.
    assert( H_caddr_not_EOA : address_is_contract caddr = true).
    {
      eapply contract_addr_format in Hec_s;eauto.
      eapply transition_reachable_impl_reachable in Htrc_s;eauto.  
    }
    assert(Hrc_s:reachable s).
    {
      eapply transition_reachable_impl_reachable in Htrc_s;eauto.
    }
    assert(Hbal:env_account_balances s caddr = cstate.(balance)).
    {
      eapply balance_on_chain_forall;eauto.
      unfold outgoing_acts.
      rewrite Hqueue_s.
      simpl.
      eauto.
    }
    destruct_address_eq;try congruence.
    + assert ((1 >? miner_reward + env_account_balances s honest )%Z 
                = false).
      {
        unfold miner_reward.
        eapply (account_balance_nonnegative s honest) in Hrc_s.
        lia.
      }
      rewrite H.
      rewrite Hec_s.
      unfold contract_state in Hcs_s.
      simpl in Hcs_s.
      destruct (env_contract_states s caddr) eqn : Hecs_s;try congruence.
      simpl.
      rewrite Hcs_s.
      simpl.
      setoid_rewrite deserialize_serialize.
      simpl.
      cbn in *.
      unfold receive.
      simpl.
      unfold address_not_contract.
      destruct (hashPass cstate =? sha3 honest_pass)%N eqn : N.
      - propify. intuition.
      - propify. 
        simpl.
        unfold  setPass.
        simpl.
        rewrite H_passB.
        unfold  one_ether.
        simpl.
        eauto.
      
    + eapply address_not_contract_negb in H_miner.
      rewrite e1 in *.
      intuition.
    + assert ((1 >?  env_account_balances s honest )%Z 
                = false).
      {
        unfold miner_reward.
        eapply (account_balance_nonnegative s honest) in Hrc_s.
        specialize (H_honest_bal_ge_1 s).
        unfold funds in *.

        lia.
      }
      rewrite H.
      rewrite Hec_s.
      unfold contract_state in Hcs_s.
      simpl in Hcs_s.
      destruct (env_contract_states s caddr) eqn : Hecs_s;try congruence.
      simpl.
      rewrite Hcs_s.
      simpl.
      setoid_rewrite deserialize_serialize.
      simpl.
      cbn in *.
      unfold receive.
      simpl.
      unfold address_not_contract.
      destruct (hashPass cstate =? sha3 honest_pass)%N eqn : N.
      - propify. intuition.
      - propify. 
        simpl.
        unfold  setPass.
        simpl.
        rewrite H_passB.
        unfold  one_ether.
        simpl.
        eauto.
  Qed.

  Lemma honest_call_SetPass_is_call_act_state_correct:
  forall (s s':ChainState) cstate,
     contract_state s caddr = Some cstate ->
     transition_reachable miner contract caddr s0 s ->
     transition miner s (honest_call_SetPass cstate) = Ok s' ->
     funds s' caddr  >= funds s caddr.
 Proof.
   intros * Hcs_s Htrc_s Htrans.
   eapply transition_reachable_queue_is_empty in Htrc_s as Hqueue_s;eauto.
   assert (Hact_call : is_call_act ((honest_call_SetPass cstate)) = true).
   {
     unfold is_call_act.
     unfold honest_call_SetPass.
     unfold build_call.
     destruct_address_eq;eauto.
   }
   assert(ttrace_s_s : TransitionTrace miner s s) by eapply clnil.
   assert(ttrace_s_s' : TransitionTrace miner s s').
   {
     econstructor;eauto.
     eapply step_trans;eauto.

   }
   assert(Htrct_s_s' : reachable_via miner contract caddr s0 s s').
   {
     econstructor;eauto.
   }
   assert(Hrt : reachable_through s s').
   {
     eapply reachable_via_impl_reachable_through in Htrct_s_s';eauto.
   }
   assert(H_t: reachable s') by eauto.
   destruct H_t as [trace].
   assert (Hec_s : env_contracts s caddr = Some ((contract : WeakContract))).
   {
     pose proof H_init.
     decompose_is_init_state H_init.
     eapply reachable_through_contract_deployed in H_env_contracts.
     eauto.
     eapply transition_reachable_impl_reachable_through in Htrc_s;eauto.
   }
   assert (Hec_s' : env_contracts s' caddr = Some ((contract : WeakContract))).
   {
     pose proof H_init.
     decompose_is_init_state H_init.
     eapply reachable_through_contract_deployed in H_env_contracts.
     eauto.
     eapply transition_reachable_impl_reachable_through in Htrc_s;eauto.
   }
   eapply deployed_contract_state_typed in Hec_s';eauto.
   destruct Hec_s' as [cstate_s' Hcs_s'].

   eauto.
   unfold transition in Htrans.
   unfold queue_isb_empty in Htrans.
   rewrite Hqueue_s in Htrans.
   rewrite Hact_call in Htrans.
   destruct (evaluate_action true s (get_valid_header miner s)
   [honest_call_SetPass cstate ]) eqn : H_exec;try congruence.
   unfold evaluate_action in H_exec.
   rewrite get_valid_header_is_valid_header in H_exec.
   destruct (find_origin_neq_from [honest_call_SetPass cstate]) ; try congruence.
   destruct (find_invalid_root_action [honest_call_SetPass cstate]);try congruence.
   set (mid_state := {|
     chain_state_env := add_new_block_to_env (get_valid_header miner s) s;
     chain_state_queue := [user_call_GetGift cstate]
   |}) in H_exec.
   simpl in *.
   destruct_address_eq;try congruence.
   simpl in *.
   destruct(send_or_call honest honest caddr 1
   (Some (serialize (SetPass (sha3 honest_pass))))
   (add_new_block_to_env (get_valid_header miner s) s)) eqn : H_send_or_call_GetGift;try congruence.
   unfold send_or_call in  H_send_or_call_GetGift.
   simpl in H_send_or_call_GetGift.
   eapply address_not_contract_negb in H_miner.
   assert( H_caddr_not_EOA : address_is_contract caddr = true).
   {
     eapply contract_addr_format in Hec_s;eauto.
     eapply transition_reachable_impl_reachable in Htrc_s;eauto.  
   }
   destruct_address_eq;simpl in *;try congruence.
   
   (* 
     e: sender cstate = miner
     n: caddr <> sender cstate
     e0: caddr = caddr
     n0: caddr <> miner 
   *)
   destruct(1 >? miner_reward + env_account_balances s honest)%Z;try congruence.
   rewrite Hec_s in H_send_or_call_GetGift.
   assert(Hcstate_s_t0:contract_state s caddr = Some cstate) by eauto.
   unfold contract_state in Hcstate_s_t0.
   simpl in Hcstate_s_t0.
   destruct (env_contract_states s caddr) eqn : Hcstate_s_t0';try congruence.
   destruct (weak_error_to_error_receive
   (wc_receive contract
      (s <| chain_height := S (chain_height s) |> <|
       current_slot := (current_slot s + 1)%nat |> <|
       finalized_height := finalized_height s |>)
      {|
        ctx_origin := honest;
        ctx_from := honest;
        ctx_contract_address := caddr;
        ctx_contract_balance :=
          1 + env_account_balances s caddr;
        ctx_amount := 1
      |} s1
      (Some (serialize (SetPass (sha3 honest_pass)))))) eqn : H_wc_receive_s1;try congruence.
   unfold weak_error_to_error_receive in H_wc_receive_s1.
   unfold bind_error in H_wc_receive_s1.
   destruct (wc_receive contract
   (s <| chain_height := S (chain_height s) |> <| current_slot
    := (current_slot s + 1)%nat |> <| finalized_height :=
    finalized_height s |>)
   {|
     ctx_origin := honest;
     ctx_from := honest;
     ctx_contract_address := caddr;
     ctx_contract_balance := 1 + env_account_balances s caddr;
     ctx_amount := 1
   |} s1 (Some (serialize (SetPass (sha3 honest_pass)))))
     eqn : H_wc_receive_s1';try congruence.
   
   set (cchain := s <| chain_height := S (chain_height s) |> <| current_slot :=
   (current_slot s + 1)%nat |> <| finalized_height :=
   finalized_height s |>) in H_wc_receive_s1'.
   set (cctx := {|
   ctx_origin := honest;
   ctx_from := honest;
   ctx_contract_address := caddr;
   ctx_contract_balance := 1 + env_account_balances s caddr;
   ctx_amount := 1
  |}) in H_wc_receive_s1'.
   
   destruct t2 as [new_state new_acts].

   destruct (wc_receive_strong ltac:(try eassumption))
   as (prev_state_strong & msg_strong & resp_state_strong &
     deser_state & deser_msg & <- & receive).

   simpl in deser_msg.
   destruct (msg_strong) eqn : H_msg;try congruence.
   rewrite deserialize_serialize in deser_msg.
   rewrite <- deser_msg in receive.
   rewrite deser_state in Hcstate_s_t0.
   simpl in receive.
   rename receive into receive_some.
   unfold receive in receive_some.
   reduce_setPass.
   propify.
   destruct_and_split.

   (* 111 *)
   inversion receive_some.
   subst.
   inversion H_wc_receive_s1;subst.
   inversion H_send_or_call_GetGift;subst.
   simpl in H_exec.
   inversion H_exec;subst.
   inversion Htrans;subst.
   simpl.
   unfold funds.
   simpl.
   destruct_address_eq;try congruence.
   lia.

   inversion receive_some.
   subst.
   inversion H_wc_receive_s1;subst.
   inversion H_send_or_call_GetGift;subst.
   simpl in H_exec.
   inversion H_exec;subst.
   inversion Htrans;subst.
   simpl.
   unfold funds.
   simpl.
   destruct_address_eq;try congruence.
   lia.
   

   (* caddr = miner *)
   eapply address_not_contract_negb in honest_eoa.
   rewrite e in *.
   intuition.
   (* 
     n: sender cstate <> miner
     n0: caddr <> sender cstate
     e: caddr = caddr
     n1: caddr <> miner
   *)
   destruct(1 >? env_account_balances s honest)%Z;try congruence.
   rewrite Hec_s in H_send_or_call_GetGift.
   assert(Hcstate_s_t0:contract_state s caddr = Some cstate) by eauto.
   unfold contract_state in Hcstate_s_t0.
   simpl in Hcstate_s_t0.
   destruct (env_contract_states s caddr) eqn : Hcstate_s_t0';try congruence.
   destruct (weak_error_to_error_receive
   (wc_receive contract
      (s <| chain_height := S (chain_height s) |> <|
       current_slot := (current_slot s + 1)%nat |> <|
       finalized_height := finalized_height s |>)
      {|
        ctx_origin := honest;
        ctx_from := honest;
        ctx_contract_address := caddr;
        ctx_contract_balance :=
          1 + env_account_balances s caddr;
        ctx_amount := 1
      |} s1
      (Some (serialize (SetPass (sha3 honest_pass)))))) eqn : H_wc_receive_s1;try congruence.
   unfold weak_error_to_error_receive in H_wc_receive_s1.
   unfold bind_error in H_wc_receive_s1.
   destruct (wc_receive contract
   (s <| chain_height := S (chain_height s) |> <| current_slot
    := (current_slot s + 1)%nat |> <| finalized_height :=
    finalized_height s |>)
   {|
     ctx_origin := honest;
     ctx_from := honest;
     ctx_contract_address := caddr;
     ctx_contract_balance := 1 + env_account_balances s caddr;
     ctx_amount := 1
   |} s1 (Some (serialize (SetPass (sha3 honest_pass)))))
     eqn : H_wc_receive_s1';try congruence.
   
   set (cchain := s <| chain_height := S (chain_height s) |> <| current_slot
   := (current_slot s + 1)%nat |> <| finalized_height :=
   finalized_height s |>) in H_wc_receive_s1'.
   set (cctx := {|
   ctx_origin := honest;
   ctx_from := honest;
   ctx_contract_address := caddr;
   ctx_contract_balance := 1 + env_account_balances s caddr;
   ctx_amount := 1
  |}) in H_wc_receive_s1'.
   
   destruct t2 as [new_state new_acts].

   destruct (wc_receive_strong ltac:(try eassumption))
   as (prev_state_strong & msg_strong & resp_state_strong &
     deser_state & deser_msg & <- & receive).

   simpl in deser_msg.
   destruct (msg_strong) eqn : H_msg;try congruence.
   rewrite deserialize_serialize in deser_msg.
   rewrite <- deser_msg in receive.
   rewrite deser_state in Hcstate_s_t0.
   simpl in receive.
   rename receive into receive_some.
   unfold receive in receive_some.
   reduce_setPass.
   (* 111 *)
   inversion receive_some.
   subst.
   inversion H_wc_receive_s1;subst.
   inversion H_send_or_call_GetGift;subst.
   simpl in H_exec.
   inversion H_exec;subst.
   inversion Htrans;subst.
   simpl.
   unfold funds.
   simpl.
   destruct_address_eq;try congruence.
   lia.

   inversion receive_some.
   subst.
   inversion H_wc_receive_s1;subst.
   inversion H_send_or_call_GetGift;subst.
   simpl in H_exec.
   inversion H_exec;subst.
   inversion Htrans;subst.
   simpl.
   unfold funds.
   simpl.
   destruct_address_eq;try congruence.
   lia.
 Qed.

  Lemma honest_call_PassHasBeenSetMsg_is_call_act_transition_correct_nopass:
  forall (s:ChainState) cstate,
      contract_state s caddr = Some cstate ->
      transition_reachable miner contract caddr s0 s ->
      cstate.(passHasBeenSet) = true ->
      cstate.(hashPass) <> (sha3 honest_pass) ->
      transition miner s (honest_call_PassHasBeenSetMsg cstate) = Err StratModel.default_error.
  Proof.
      intros * Hcs_s Htrc_s H_passB H_neq.
      unfold transition.
      unfold queue_isb_empty.
      eapply transition_reachable_queue_is_empty in Htrc_s as Hqueue_s;eauto.
      rewrite Hqueue_s.
      rewrite honest_call_PassHasBeenSetMsg_is_call_act.
      unfold evaluate_action.
      rewrite get_valid_header_is_valid_header.
      unfold honest_call_PassHasBeenSetMsg .
      simpl.
      destruct_address_eq;try congruence.
      simpl.
      assert (Hec_s:env_contracts s caddr = Some (contract:WeakContract)).
      {
        eapply transition_reachable_impl_reachable_through in Htrc_s.
        eapply reachable_through_contract_deployed in Htrc_s;eauto.
        decompose_is_init_state H_init.
        eauto.
        eauto.
      }
      eapply address_not_contract_negb in honest_eoa.
      rewrite honest_eoa.
      unfold send_or_call.
      simpl.
      assert( H_caddr_not_EOA : address_is_contract caddr = true).
      {
        eapply contract_addr_format in Hec_s;eauto.
        eapply transition_reachable_impl_reachable in Htrc_s;eauto.  
      }
      assert(Hrc_s:reachable s).
      {
        eapply transition_reachable_impl_reachable in Htrc_s;eauto.
      }
      assert(Hbal:env_account_balances s caddr = cstate.(balance)).
      {
        eapply balance_on_chain_forall;eauto.
        unfold outgoing_acts.
        rewrite Hqueue_s.
        simpl.
        eauto.
      }
      destruct_address_eq;try congruence.
      + assert ((0 >? miner_reward + env_account_balances s honest )%Z 
                  = false).
        {
          unfold miner_reward.
          eapply (account_balance_nonnegative s honest) in Hrc_s.
          lia.
        }
        rewrite H.
        rewrite Hec_s.
        unfold contract_state in Hcs_s.
        simpl in Hcs_s.
        destruct (env_contract_states s caddr) eqn : Hecs_s;try congruence.
        simpl.
        rewrite Hcs_s.
        simpl.
        setoid_rewrite deserialize_serialize.
        simpl.
        cbn in *.
        unfold receive.
        destruct (hashPass cstate)%N eqn : HH.
        - propify.  intuition.
        - propify. 
          unfold sha3 in H_neq.
          destruct ((countable.encode honest_pass =? p)%positive) eqn :  h';try congruence .
          propify.
          eapply Pos.eqb_eq in h'.
          rewrite <- h' in H_neq.
          intuition.
          setoid_rewrite h'.
          simpl.
          eauto.
      
      + assert ((0 >?  env_account_balances s honest )%Z 
                  = false).
        {
          unfold miner_reward.
          eapply (account_balance_nonnegative s honest) in Hrc_s.
          lia.
        }
        rewrite H.
        rewrite Hec_s.
        unfold contract_state in Hcs_s.
        simpl in Hcs_s.
        destruct (env_contract_states s caddr) eqn : Hecs_s;try congruence.
        simpl.
        rewrite Hcs_s.
        simpl.
        setoid_rewrite deserialize_serialize.
        simpl.
        cbn in *.
        unfold receive.
        simpl.
        unfold address_not_contract.
        destruct (hashPass cstate)%N eqn : HH.
        - propify.  intuition.
        - propify. 
          unfold sha3 in H_neq.
          destruct ((countable.encode honest_pass =? p)%positive) eqn :  h';try congruence .
          propify.
          eapply Pos.eqb_eq in h'.
          rewrite <- h' in H_neq.
          intuition.
          setoid_rewrite h'.
          simpl.
          eauto.
      + assert ((0 >?  env_account_balances s honest )%Z 
                  = false).
        {
          unfold miner_reward.
          eapply (account_balance_nonnegative s honest) in Hrc_s.
          lia.
        }
        rewrite H.
        rewrite Hec_s.
        unfold contract_state in Hcs_s.
        simpl in Hcs_s.
        destruct (env_contract_states s caddr) eqn : Hecs_s;try congruence.
        simpl.
        rewrite Hcs_s.
        simpl.
        setoid_rewrite deserialize_serialize.
        simpl.
        cbn in *.
        unfold receive.
        simpl.
        unfold address_not_contract.
        destruct (hashPass cstate)%N eqn : HH.
        - propify.  intuition.
        - propify. 
          unfold sha3 in H_neq.
          destruct ((countable.encode honest_pass =? p)%positive) eqn :  h';try congruence .
          propify.
          eapply Pos.eqb_eq in h'.
          rewrite <- h' in H_neq.
          intuition.
          setoid_rewrite h'.
          simpl.
          eauto.
  Qed.

  Lemma honest_strat_correct_nopass:
    forall (s s':ChainState) cstate a (tr : TransitionTrace miner s0 s) ,
        contract_state s caddr = Some cstate ->
        transition_reachable miner contract caddr s0 s ->
        cstate.(passHasBeenSet) = true ->
        cstate.(hashPass) <> (sha3 honest_pass) ->
        In a (honest_strat s0 s tr) ->
        transition miner s a = Ok s' ->
        funds s' caddr >= funds s caddr.
  Proof.
    intros.
    unfold honest_strat in *.
    unfold get_contract_state in H3.
    pose proof H as HT.
    unfold contract_state in HT.
    simpl in HT.
    destruct (env_contract_states s caddr) eqn : cs;try congruence.
    rewrite HT in H3.
    destruct H3.
    rewrite <- H3 in H4.
    eapply honest_call_SetPass_is_call_act_state_correct in H4;eauto.
    destruct H3.
    rewrite <- H3 in H4.
    eapply honest_call_GetGift_is_call_act_transition_correct_nopass in H;eauto.
    congruence.
    destruct H3.
    eauto.
    rewrite <- H3 in H4.
    eapply honest_call_PassHasBeenSetMsg_is_call_act_transition_correct_nopass in H;eauto.
    congruence.
    destruct H3.
  Qed.

  Lemma attacker_call_SetPass_is_call_act_transition_correct:
    forall (s:ChainState) cstate,
        contract_state s caddr = Some cstate ->
        transition_reachable miner contract caddr s0 s ->
        cstate.(passHasBeenSet) = false ->
        exists s',
        transition miner s (attacker_call_SetPass cstate) = Ok s'.
  Proof.
    intros * Hcs_s Htrc_s H_passB  .
    eexists.
    unfold transition.
    unfold queue_isb_empty.
    eapply transition_reachable_queue_is_empty in Htrc_s as Hqueue_s;eauto.
    rewrite Hqueue_s.
    rewrite attacker_call_SetPass_is_call_act.
    unfold evaluate_action.
    rewrite get_valid_header_is_valid_header.
    unfold attacker_call_SetPass .
    simpl.
    destruct_address_eq;try congruence.
    simpl.
    assert (Hec_s:env_contracts s caddr = Some (contract:WeakContract)).
    {
      eapply transition_reachable_impl_reachable_through in Htrc_s.
      eapply reachable_through_contract_deployed in Htrc_s;eauto.
      decompose_is_init_state H_init.
      eauto.
      eauto.
    }
    eapply address_not_contract_negb in attacker_eoa.
    rewrite attacker_eoa.
    unfold send_or_call.
    simpl.
    assert( H_caddr_not_EOA : address_is_contract caddr = true).
    {
      eapply contract_addr_format in Hec_s;eauto.
      eapply transition_reachable_impl_reachable in Htrc_s;eauto.  
    }
    assert(Hrc_s:reachable s).
    {
      eapply transition_reachable_impl_reachable in Htrc_s;eauto.
    }
    assert(Hbal:env_account_balances s caddr = cstate.(balance)).
    {
      eapply balance_on_chain_forall;eauto.
      unfold outgoing_acts.
      rewrite Hqueue_s.
      simpl.
      eauto.
    }
    destruct_address_eq;try congruence.
    + assert ((1 >? miner_reward + env_account_balances s attacker )%Z = false).
      {
        unfold miner_reward.
        eapply (account_balance_nonnegative s attacker) in Hrc_s.
        
        lia.
      }
      rewrite H.
      rewrite Hec_s.
      unfold contract_state in Hcs_s.
      simpl in Hcs_s.
      destruct (env_contract_states s caddr) eqn : Hecs_s;try congruence.
      simpl.
      rewrite Hcs_s.
      simpl.
      setoid_rewrite deserialize_serialize.
      simpl.
      unfold setPass.
      rewrite H_passB.
      simpl.
      eauto.
      
    + assert ((1 >? env_account_balances s attacker )%Z = false).
    {
      unfold miner_reward.
      eapply (account_balance_nonnegative s attacker) in Hrc_s.
      specialize (H_attack_bal_ge_1 s).
      unfold funds in *.
      lia.
    }
    rewrite H.
    rewrite Hec_s.
    unfold contract_state in Hcs_s.
    simpl in Hcs_s.
    destruct (env_contract_states s caddr) eqn : Hecs_s;try congruence.
    simpl.
    rewrite Hcs_s.
    simpl.
    setoid_rewrite deserialize_serialize.
    simpl.
    unfold setPass.
    rewrite H_passB.
    simpl.
    eauto.
    + assert ((1 >? env_account_balances s attacker )%Z 
                = false).
      {
        unfold miner_reward.
        eapply (account_balance_nonnegative s attacker) in Hrc_s.
        specialize (H_attack_bal_ge_1 s).
        unfold funds in *.
        lia.
      }
      rewrite H.
    rewrite Hec_s.
    unfold contract_state in Hcs_s.
    simpl in Hcs_s.
    destruct (env_contract_states s caddr) eqn : Hecs_s;try congruence.
    simpl.
    rewrite Hcs_s.
    simpl.
    setoid_rewrite deserialize_serialize.
    simpl.
    unfold setPass.
    rewrite H_passB.
    simpl.
    eauto.
  Qed.

  Lemma attacker_call_PassHasBeenSetMsg_is_call_act_transition_correct:
    forall (s:ChainState) cstate,
      contract_state s caddr = Some cstate ->
      transition_reachable miner contract caddr s0 s ->
      cstate.(passHasBeenSet) = false ->
      cstate.(hashPass) = sha3 attacker_pass ->
      exists s',
      transition miner s (attacker_call_PassHasBeenSetMsg cstate) = Ok s'.
  Proof.
    intros * Hcs_s Htrc_s H_passB H_pass .
    eexists.
    unfold transition.
    unfold queue_isb_empty.
    eapply transition_reachable_queue_is_empty in Htrc_s as Hqueue_s;eauto.
    rewrite Hqueue_s.
    rewrite attacker_call_PassHasBeenSetMsg_is_call_act.
    unfold evaluate_action.
    rewrite get_valid_header_is_valid_header.
    unfold attacker_call_PassHasBeenSetMsg .
    simpl.
    destruct_address_eq;try congruence.
    simpl.
    assert (Hec_s:env_contracts s caddr = Some (contract:WeakContract)).
    {
      eapply transition_reachable_impl_reachable_through in Htrc_s.
      eapply reachable_through_contract_deployed in Htrc_s;eauto.
      decompose_is_init_state H_init.
      eauto.
      eauto.
    }
    eapply address_not_contract_negb in attacker_eoa.
    rewrite attacker_eoa.
    unfold send_or_call.
    simpl.
    assert( H_caddr_not_EOA : address_is_contract caddr = true).
    {
      eapply contract_addr_format in Hec_s;eauto.
      eapply transition_reachable_impl_reachable in Htrc_s;eauto.  
    }
    assert(Hrc_s:reachable s).
    {
      eapply transition_reachable_impl_reachable in Htrc_s;eauto.
    }
    assert(Hbal:env_account_balances s caddr = cstate.(balance)).
    {
      eapply balance_on_chain_forall;eauto.
      unfold outgoing_acts.
      rewrite Hqueue_s.
      simpl.
      eauto.
    }
    destruct_address_eq;try congruence.
    + assert ((0 >? miner_reward + env_account_balances s attacker )%Z 
                = false).
      {
        unfold miner_reward.
        eapply (account_balance_nonnegative s attacker) in Hrc_s.
        lia.
      }
      rewrite H.
      rewrite Hec_s.
      unfold contract_state in Hcs_s.
      simpl in Hcs_s.
      destruct (env_contract_states s caddr) eqn : Hecs_s;try congruence.
      simpl.
      rewrite Hcs_s.
      simpl.
      setoid_rewrite deserialize_serialize.
      simpl.
      cbn in *.
      unfold receive.
      simpl.
      unfold address_not_contract.
      rewrite H_pass.
      destruct (hashPass cstate =? sha3 attacker_pass)%N eqn : N.
      - propify. 
        destruct (sha3 attacker_pass) eqn : h'; try congruence.
        destruct ((countable.encode attacker_pass =? p)%positive) eqn : h''; try congruence.
        ++ propify.
           setoid_rewrite h''.
           simpl.
           eauto.
        ++ eapply Pos.eqb_neq in h''.
            unfold sha3 in h'.
            eapply pos_inj in h'.
            intuition.
      - eapply N.eqb_neq in N.
         rewrite H_pass in N.
          intuition.
      
    + eapply address_not_contract_negb in H_miner.
      rewrite e1 in *.
      intuition.
    + assert ((0 >?  env_account_balances s attacker )%Z 
                = false).
      {
        unfold miner_reward.
        eapply (account_balance_nonnegative s attacker) in Hrc_s.
        specialize (H_honest_bal_ge_1 s).
        unfold funds in *.
        lia.
      }
      rewrite H.
      rewrite Hec_s.
      unfold contract_state in Hcs_s.
      simpl in Hcs_s.
      destruct (env_contract_states s caddr) eqn : Hecs_s;try congruence.
      simpl.
      rewrite Hcs_s.
      simpl.
      setoid_rewrite deserialize_serialize.
      simpl.
      cbn in *.
      unfold receive.
      simpl.
      unfold address_not_contract.
      rewrite H_pass.
      destruct (hashPass cstate =? sha3 attacker_pass)%N eqn : N.
      - propify. 
        destruct (sha3 attacker_pass) eqn : h'; try congruence.
        destruct ((countable.encode attacker_pass =? p)%positive) eqn : h''; try congruence.
        ++ propify.
           setoid_rewrite h''.
           simpl.
           eauto.
        ++ eapply Pos.eqb_neq in h''.
            unfold sha3 in h'.
            eapply pos_inj in h'.
            intuition.
      - eapply N.eqb_neq in N.
         rewrite H_pass in N.
          intuition.
  Qed.

  Lemma attacker_call_SetPass_is_call_act_state_correct:
   forall (s s':ChainState) cstate,
      contract_state s caddr = Some cstate ->
      transition_reachable miner contract caddr s0 s ->
      cstate.(passHasBeenSet) = false ->
      transition miner s (attacker_call_SetPass cstate) = Ok s' ->
      exists cstate',
        contract_state s' caddr = Some cstate' /\
        cstate'.(hashPass) = sha3 attacker_pass /\
        cstate'.(passHasBeenSet ) = false.
  Proof.
    intros * Hcs_s Htrc_s H_passB Htrans.
    eapply transition_reachable_queue_is_empty in Htrc_s as Hqueue_s;eauto.
    assert (Hact_call : is_call_act ((attacker_call_SetPass cstate)) = true).
    {
      unfold is_call_act.
      unfold attacker_call_SetPass.
      unfold build_call.
      destruct_address_eq;eauto.
    }
    assert(ttrace_s_s : TransitionTrace miner s s) by eapply clnil.
    assert(ttrace_s_s' : TransitionTrace miner s s').
    {
      econstructor;eauto.
      eapply step_trans;eauto.

    }
    assert(Htrct_s_s' : reachable_via miner contract caddr s0 s s').
    {
      econstructor;eauto.
    }
    assert(Hrt : reachable_through s s').
    {
      eapply reachable_via_impl_reachable_through in Htrct_s_s';eauto.
    }
    assert(H_t: reachable s') by eauto.
    destruct H_t as [trace].
    assert (Hec_s : env_contracts s caddr = Some ((contract : WeakContract))).
    {
      pose proof H_init.
      decompose_is_init_state H_init.
      eapply reachable_through_contract_deployed in H_env_contracts.
      eauto.
      eapply transition_reachable_impl_reachable_through in Htrc_s;eauto.
    }
    assert (Hec_s' : env_contracts s' caddr = Some ((contract : WeakContract))).
    {
      pose proof H_init.
      decompose_is_init_state H_init.
      eapply reachable_through_contract_deployed in H_env_contracts.
      eauto.
      eapply transition_reachable_impl_reachable_through in Htrc_s;eauto.
    }
    eapply deployed_contract_state_typed in Hec_s';eauto.
    destruct Hec_s' as [cstate_s' Hcs_s'].
    exists cstate_s'.
    split.
    eauto.
    unfold transition in Htrans.
    unfold queue_isb_empty in Htrans.
    rewrite Hqueue_s in Htrans.
    rewrite Hact_call in Htrans.
    destruct (evaluate_action true s (get_valid_header miner s)
    [attacker_call_SetPass cstate ]) eqn : H_exec;try congruence.
    unfold evaluate_action in H_exec.
    rewrite get_valid_header_is_valid_header in H_exec.
    destruct (find_origin_neq_from [attacker_call_SetPass cstate]) ; try congruence.
    destruct (find_invalid_root_action [attacker_call_SetPass cstate]);try congruence.
    set (mid_state := {|
      chain_state_env := add_new_block_to_env (get_valid_header miner s) s;
      chain_state_queue := [attacker_call_SetPass cstate]
    |}) in H_exec.
    simpl in *.
    destruct(
    send_or_call attacker attacker caddr 1
      (Some (serialize (SetPass (sha3 attacker_pass))))
      (add_new_block_to_env (get_valid_header miner s) s)) eqn : H_send_or_call_GetGift;try congruence.
    unfold send_or_call in  H_send_or_call_GetGift.
    simpl in H_send_or_call_GetGift.
    eapply address_not_contract_negb in H_miner.
    assert( H_caddr_not_EOA : address_is_contract caddr = true).
    {
      eapply contract_addr_format in Hec_s;eauto.
      eapply transition_reachable_impl_reachable in Htrc_s;eauto.  
    }
    destruct_address_eq;simpl in *;try congruence.
    
    (* 
      e: sender cstate = miner
      n: caddr <> sender cstate
      e0: caddr = caddr
      n0: caddr <> miner 
    *)

    destruct(1 >? miner_reward + env_account_balances s attacker)%Z;try congruence.
    rewrite Hec_s in H_send_or_call_GetGift.
    assert(Hcstate_s_t0:contract_state s caddr = Some cstate) by eauto.
    unfold contract_state in Hcstate_s_t0.
    simpl in Hcstate_s_t0.
    destruct (env_contract_states s caddr) eqn : Hcstate_s_t0';try congruence.
    destruct (weak_error_to_error_receive
    (wc_receive contract
       (s <| chain_height := S (chain_height s) |> <|
        current_slot := (current_slot s + 1)%nat |> <|
        finalized_height := finalized_height s |>)
       {|
         ctx_origin := attacker;
         ctx_from := attacker;
         ctx_contract_address := caddr;
         ctx_contract_balance :=
           1 + env_account_balances s caddr;
         ctx_amount := 1
       |} s1
       (Some (serialize (SetPass (sha3 attacker_pass)))))) eqn : H_wc_receive_s1;try congruence.
    unfold weak_error_to_error_receive in H_wc_receive_s1.
    unfold bind_error in H_wc_receive_s1.
    destruct (wc_receive contract
    (s <| chain_height := S (chain_height s) |> <| current_slot
     := (current_slot s + 1)%nat |> <| finalized_height :=
     finalized_height s |>)
    {|
      ctx_origin := attacker;
      ctx_from := attacker;
      ctx_contract_address := caddr;
      ctx_contract_balance := 1 + env_account_balances s caddr;
      ctx_amount := 1
    |} s1 (Some (serialize (SetPass (sha3 attacker_pass)))))
      eqn : H_wc_receive_s1';try congruence.
    
    set (cchain := s <| chain_height := S (chain_height s) |> <| current_slot :=
    (current_slot s + 1)%nat |> <| finalized_height :=
    finalized_height s |>) in H_wc_receive_s1'.
    set (cctx := {|
    ctx_origin := user1;
    ctx_from := user1;
    ctx_contract_address := caddr;
    ctx_contract_balance := 0 + env_account_balances s caddr;
    ctx_amount := 0
    |}) in H_wc_receive_s1'.
    
    destruct t2 as [new_state new_acts].

    destruct (wc_receive_strong ltac:(try eassumption))
    as (prev_state_strong & msg_strong & resp_state_strong &
      deser_state & deser_msg & <- & receive).

    simpl in deser_msg.
    destruct (msg_strong) eqn : H_msg;try congruence.
    rewrite deserialize_serialize in deser_msg.
    rewrite <- deser_msg in receive.
    rewrite deser_state in Hcstate_s_t0.
    simpl in receive.
    rename receive into receive_some.
    unfold receive in receive_some.
    reduce_setPass.
    (* 111 *)
    inversion receive_some.
    subst.
    inversion H_wc_receive_s1;subst.
    inversion H_send_or_call_GetGift;subst.
    simpl in H_exec.
    inversion H_exec;subst.
    inversion Htrans;subst.
    inversion H_send_or_call_GetGift;subst.
    inversion Hcs_s';subst.
    unfold contract_state in H0.
    simpl in H0.
    destruct_address_eq;eauto.
    setoid_rewrite deserialize_serialize in H0.
    inversion H0.
    inversion Hcstate_s_t0 ;    subst.
    intuition.
    destruct_address_eq;try congruence.

    simpl in *.
    inversion Hcstate_s_t0.
    rewrite H0 in EsetPass.
    rewrite H_passB in EsetPass.
    simpl in EsetPass.
    unfold one_ether in EsetPass.
    intuition.

    (* n: attacker <> miner
      e: caddr = attacker
      e0: caddr = caddr
      n0: caddr <> miner *)

    eapply address_not_contract_negb in attacker_eoa.
    rewrite e in *.
    intuition.

    (* 
      n: attacker <> miner
    n0: caddr <> attacker
    e: caddr = caddr
    n1: caddr <> miner
    
    *)
    destruct(1 >?  env_account_balances s attacker)%Z;try congruence.
    rewrite Hec_s in H_send_or_call_GetGift.
    assert(Hcstate_s_t0:contract_state s caddr = Some cstate) by eauto.
    unfold contract_state in Hcstate_s_t0.
    simpl in Hcstate_s_t0.
    destruct (env_contract_states s caddr) eqn : Hcstate_s_t0';try congruence.
    destruct (weak_error_to_error_receive
    (wc_receive contract
       (s <| chain_height := S (chain_height s) |> <|
        current_slot := (current_slot s + 1)%nat |> <|
        finalized_height := finalized_height s |>)
       {|
         ctx_origin := attacker;
         ctx_from := attacker;
         ctx_contract_address := caddr;
         ctx_contract_balance :=
           1 + env_account_balances s caddr;
         ctx_amount := 1
       |} s1
       (Some (serialize (SetPass (sha3 attacker_pass)))))) eqn : H_wc_receive_s1;try congruence.
    unfold weak_error_to_error_receive in H_wc_receive_s1.
    unfold bind_error in H_wc_receive_s1.
    destruct (wc_receive contract
    (s <| chain_height := S (chain_height s) |> <| current_slot
     := (current_slot s + 1)%nat |> <| finalized_height :=
     finalized_height s |>)
    {|
      ctx_origin := attacker;
      ctx_from := attacker;
      ctx_contract_address := caddr;
      ctx_contract_balance := 1 + env_account_balances s caddr;
      ctx_amount := 1
    |} s1 (Some (serialize (SetPass (sha3 attacker_pass)))))
      eqn : H_wc_receive_s1';try congruence.
    
    set (cchain := s <| chain_height := S (chain_height s) |> <| current_slot :=
    (current_slot s + 1)%nat |> <| finalized_height :=
    finalized_height s |>) in H_wc_receive_s1'.
    set (cctx := {|
    ctx_origin := user1;
    ctx_from := user1;
    ctx_contract_address := caddr;
    ctx_contract_balance := 0 + env_account_balances s caddr;
    ctx_amount := 0
    |}) in H_wc_receive_s1'.
    
    destruct t2 as [new_state new_acts].

    destruct (wc_receive_strong ltac:(try eassumption))
    as (prev_state_strong & msg_strong & resp_state_strong &
      deser_state & deser_msg & <- & receive).

    simpl in deser_msg.
    destruct (msg_strong) eqn : H_msg;try congruence.
    rewrite deserialize_serialize in deser_msg.
    rewrite <- deser_msg in receive.
    rewrite deser_state in Hcstate_s_t0.
    simpl in receive.
    rename receive into receive_some.
    unfold receive in receive_some.
    reduce_setPass.
    (* 111 *)
    inversion receive_some.
    subst.
    inversion H_wc_receive_s1;subst.
    inversion H_send_or_call_GetGift;subst.
    simpl in H_exec.
    inversion H_exec;subst.
    inversion Htrans;subst.
    inversion H_send_or_call_GetGift;subst.
    inversion Hcs_s';subst.
    unfold contract_state in H0.
    simpl in H0.
    destruct_address_eq;eauto.
    setoid_rewrite deserialize_serialize in H0.
    inversion H0.
    inversion Hcstate_s_t0 ;    subst.
    intuition.
    destruct_address_eq;try congruence.
    simpl in *.
    inversion Hcstate_s_t0.
    rewrite H0 in EsetPass.
    rewrite H_passB in EsetPass.
    simpl in EsetPass.
    unfold one_ether in EsetPass.
    intuition.
  Qed.

  Lemma attacker_call_SetPass_is_call_act_state_correct_funds:
    forall (s s':ChainState) cstate,
     contract_state s caddr = Some cstate ->
     transition_reachable miner contract caddr s0 s ->
     cstate.(passHasBeenSet) = false ->
     transition miner s (attacker_call_SetPass cstate) = Ok s' ->
     funds s' caddr > 0.
  Proof.
    intros * Hcs_s Htrc_s H_passB Htrans.
    eapply transition_reachable_queue_is_empty in Htrc_s as Hqueue_s;eauto.
    assert (Hact_call : is_call_act ((attacker_call_SetPass cstate)) = true).
    {
      unfold is_call_act.
      unfold attacker_call_SetPass.
      unfold build_call.
      destruct_address_eq;eauto.
    }
    assert(ttrace_s_s : TransitionTrace miner s s) by eapply clnil.
    assert(ttrace_s_s' : TransitionTrace miner s s').
    {
      econstructor;eauto.
      eapply step_trans;eauto.

    }
    assert(Htrct_s_s' : reachable_via miner contract caddr s0 s s').
    {
      econstructor;eauto.
    }
    assert(Hrt : reachable_through s s').
    {
      eapply reachable_via_impl_reachable_through in Htrct_s_s';eauto.
    }
    assert(H_t: reachable s') by eauto.
    destruct H_t as [trace].
    assert (Hec_s : env_contracts s caddr = Some ((contract : WeakContract))).
    {
      pose proof H_init.
      decompose_is_init_state H_init.
      eapply reachable_through_contract_deployed in H_env_contracts.
      eauto.
      eapply transition_reachable_impl_reachable_through in Htrc_s;eauto.
    }
    assert (Hec_s' : env_contracts s' caddr = Some ((contract : WeakContract))).
    {
      pose proof H_init.
      decompose_is_init_state H_init.
      eapply reachable_through_contract_deployed in H_env_contracts.
      eauto.
      eapply transition_reachable_impl_reachable_through in Htrc_s;eauto.
    }
    eapply deployed_contract_state_typed in Hec_s';eauto.
    
    unfold transition in Htrans.
    unfold queue_isb_empty in Htrans.
    rewrite Hqueue_s in Htrans.
    rewrite Hact_call in Htrans.
    destruct (evaluate_action true s (get_valid_header miner s)
    [attacker_call_SetPass cstate ]) eqn : H_exec;try congruence.
    unfold evaluate_action in H_exec.
    rewrite get_valid_header_is_valid_header in H_exec.
    destruct (find_origin_neq_from [attacker_call_SetPass cstate]) ; try congruence.
    destruct (find_invalid_root_action [attacker_call_SetPass cstate]);try congruence.
    set (mid_state := {|
      chain_state_env := add_new_block_to_env (get_valid_header miner s) s;
      chain_state_queue := [attacker_call_SetPass cstate]
    |}) in H_exec.
    simpl in *.
    destruct(
    send_or_call attacker attacker caddr 1
      (Some (serialize (SetPass (sha3 attacker_pass))))
      (add_new_block_to_env (get_valid_header miner s) s)) eqn : H_send_or_call_GetGift;try congruence.
    unfold send_or_call in  H_send_or_call_GetGift.
    simpl in H_send_or_call_GetGift.
    eapply address_not_contract_negb in H_miner.
    assert( H_caddr_not_EOA : address_is_contract caddr = true).
    {
      eapply contract_addr_format in Hec_s;eauto.
      eapply transition_reachable_impl_reachable in Htrc_s;eauto.  
    }
    destruct_address_eq;simpl in *;try congruence.
    
    (* 
      e: sender cstate = miner
      n: caddr <> sender cstate
      e0: caddr = caddr
      n0: caddr <> miner 
    *)

    destruct(1 >? miner_reward + env_account_balances s attacker)%Z;try congruence.
    rewrite Hec_s in H_send_or_call_GetGift.
    assert(Hcstate_s_t0:contract_state s caddr = Some cstate) by eauto.
    unfold contract_state in Hcstate_s_t0.
    simpl in Hcstate_s_t0.
    destruct (env_contract_states s caddr) eqn : Hcstate_s_t0';try congruence.
    destruct (weak_error_to_error_receive
    (wc_receive contract
       (s <| chain_height := S (chain_height s) |> <|
        current_slot := (current_slot s + 1)%nat |> <|
        finalized_height := finalized_height s |>)
       {|
         ctx_origin := attacker;
         ctx_from := attacker;
         ctx_contract_address := caddr;
         ctx_contract_balance :=
           1 + env_account_balances s caddr;
         ctx_amount := 1
       |} s1
       (Some (serialize (SetPass (sha3 attacker_pass)))))) eqn : H_wc_receive_s1;try congruence.
    unfold weak_error_to_error_receive in H_wc_receive_s1.
    unfold bind_error in H_wc_receive_s1.
    destruct (wc_receive contract
    (s <| chain_height := S (chain_height s) |> <| current_slot
     := (current_slot s + 1)%nat |> <| finalized_height :=
     finalized_height s |>)
    {|
      ctx_origin := attacker;
      ctx_from := attacker;
      ctx_contract_address := caddr;
      ctx_contract_balance := 1 + env_account_balances s caddr;
      ctx_amount := 1
    |} s1 (Some (serialize (SetPass (sha3 attacker_pass)))))
      eqn : H_wc_receive_s1';try congruence.
    
    set (cchain := s <| chain_height := S (chain_height s) |> <| current_slot :=
    (current_slot s + 1)%nat |> <| finalized_height :=
    finalized_height s |>) in H_wc_receive_s1'.
    set (cctx := {|
    ctx_origin := user1;
    ctx_from := user1;
    ctx_contract_address := caddr;
    ctx_contract_balance := 0 + env_account_balances s caddr;
    ctx_amount := 0
    |}) in H_wc_receive_s1'.
    
    destruct t2 as [new_state new_acts].

    destruct (wc_receive_strong ltac:(try eassumption))
    as (prev_state_strong & msg_strong & resp_state_strong &
      deser_state & deser_msg & <- & receive).

    simpl in deser_msg.
    destruct (msg_strong) eqn : H_msg;try congruence.
    rewrite deserialize_serialize in deser_msg.
    rewrite <- deser_msg in receive.
    rewrite deser_state in Hcstate_s_t0.
    simpl in receive.
    rename receive into receive_some.
    unfold receive in receive_some.
    reduce_setPass.
    (* 111 *)
    inversion receive_some.
    subst.
    inversion H_wc_receive_s1;subst.
    inversion H_send_or_call_GetGift;subst.
    simpl in H_exec.
    inversion H_exec;subst.
    inversion Htrans;subst.
    inversion H_send_or_call_GetGift;subst.
    eapply transition_reachable_impl_reachable in Htrc_s as Hreac.
    eapply (reachable_funds_nonnegative s caddr) in Hreac.
    unfold funds in *.
    simpl.
    destruct_address_eq;try congruence.
    lia.
    eauto.


    simpl in *.
    inversion Hcstate_s_t0.
    rewrite H0 in EsetPass.
    rewrite H_passB in EsetPass.
    simpl in EsetPass.
    unfold one_ether in EsetPass.
    intuition.

    (* n: attacker <> miner
      e: caddr = attacker
      e0: caddr = caddr
      n0: caddr <> miner *)

    eapply address_not_contract_negb in attacker_eoa.
    rewrite e in *.
    intuition.

    (* 
      n: attacker <> miner
    n0: caddr <> attacker
    e: caddr = caddr
    n1: caddr <> miner
    
    *)
    destruct(1 >?  env_account_balances s attacker)%Z;try congruence.
    rewrite Hec_s in H_send_or_call_GetGift.
    assert(Hcstate_s_t0:contract_state s caddr = Some cstate) by eauto.
    unfold contract_state in Hcstate_s_t0.
    simpl in Hcstate_s_t0.
    destruct (env_contract_states s caddr) eqn : Hcstate_s_t0';try congruence.
    destruct (weak_error_to_error_receive
    (wc_receive contract
       (s <| chain_height := S (chain_height s) |> <|
        current_slot := (current_slot s + 1)%nat |> <|
        finalized_height := finalized_height s |>)
       {|
         ctx_origin := attacker;
         ctx_from := attacker;
         ctx_contract_address := caddr;
         ctx_contract_balance :=
           1 + env_account_balances s caddr;
         ctx_amount := 1
       |} s1
       (Some (serialize (SetPass (sha3 attacker_pass)))))) eqn : H_wc_receive_s1;try congruence.
    unfold weak_error_to_error_receive in H_wc_receive_s1.
    unfold bind_error in H_wc_receive_s1.
    destruct (wc_receive contract
    (s <| chain_height := S (chain_height s) |> <| current_slot
     := (current_slot s + 1)%nat |> <| finalized_height :=
     finalized_height s |>)
    {|
      ctx_origin := attacker;
      ctx_from := attacker;
      ctx_contract_address := caddr;
      ctx_contract_balance := 1 + env_account_balances s caddr;
      ctx_amount := 1
    |} s1 (Some (serialize (SetPass (sha3 attacker_pass)))))
      eqn : H_wc_receive_s1';try congruence.
    
    set (cchain := s <| chain_height := S (chain_height s) |> <| current_slot :=
    (current_slot s + 1)%nat |> <| finalized_height :=
    finalized_height s |>) in H_wc_receive_s1'.
    set (cctx := {|
    ctx_origin := user1;
    ctx_from := user1;
    ctx_contract_address := caddr;
    ctx_contract_balance := 0 + env_account_balances s caddr;
    ctx_amount := 0
    |}) in H_wc_receive_s1'.
    
    destruct t2 as [new_state new_acts].

    destruct (wc_receive_strong ltac:(try eassumption))
    as (prev_state_strong & msg_strong & resp_state_strong &
      deser_state & deser_msg & <- & receive).

    simpl in deser_msg.
    destruct (msg_strong) eqn : H_msg;try congruence.
    rewrite deserialize_serialize in deser_msg.
    rewrite <- deser_msg in receive.
    rewrite deser_state in Hcstate_s_t0.
    simpl in receive.
    rename receive into receive_some.
    unfold receive in receive_some.
    reduce_setPass.
    (* 111 *)
    inversion receive_some.
    subst.
    inversion H_wc_receive_s1;subst.
    inversion H_send_or_call_GetGift;subst.
    simpl in H_exec.
    inversion H_exec;subst.
    inversion Htrans;subst.
    inversion H_send_or_call_GetGift;subst.
    eapply transition_reachable_impl_reachable in Htrc_s as Hreac.
    eapply (reachable_funds_nonnegative s caddr) in Hreac.
    unfold funds in *.
    simpl.
    destruct_address_eq;try congruence.
    lia.
    eauto.
    simpl in *.
    inversion Hcstate_s_t0.
    rewrite H0 in EsetPass.
    rewrite H_passB in EsetPass.
    simpl in EsetPass.
    unfold one_ether in EsetPass.
    intuition.
  Qed.

  Lemma attacker_call_PassHasBeenSetMsg_is_call_act_state_correct_funds:
  forall (s s':ChainState) cstate,
      contract_state s caddr = Some cstate ->
      transition_reachable miner contract caddr s0 s ->
      cstate.(passHasBeenSet) = false ->
      cstate.(hashPass) = sha3 attacker_pass ->
      transition miner s (attacker_call_PassHasBeenSetMsg cstate) = Ok s' ->
      funds s' caddr = funds s caddr.
  Proof.
    intros * Hcs_s Htrc_s H_passB H_pass Htrans.
    eapply transition_reachable_queue_is_empty in Htrc_s as Hqueue_s;eauto.
    assert (Hact_call : is_call_act ((attacker_call_PassHasBeenSetMsg cstate)) = true).
    {
      unfold is_call_act.
      unfold attacker_call_PassHasBeenSetMsg.
      unfold build_call.
      destruct_address_eq;eauto.
    }
    assert(ttrace_s_s : TransitionTrace miner s s) by eapply clnil.
    assert(ttrace_s_s' : TransitionTrace miner s s').
    {
      econstructor;eauto.
      eapply step_trans;eauto.
    }
    assert(Htrct_s_s' : reachable_via miner contract caddr s0 s s').
    {
      econstructor;eauto.
    }
    assert(Hrt : reachable_through s s').
    {
      eapply reachable_via_impl_reachable_through in Htrct_s_s';eauto.
    }
    assert(H_t: reachable s') by eauto.
    destruct H_t as [trace].
    assert (Hec_s : env_contracts s caddr = Some ((contract : WeakContract))).
    {
      pose proof H_init.
      decompose_is_init_state H_init.
      eapply reachable_through_contract_deployed in H_env_contracts.
      eauto.
      eapply transition_reachable_impl_reachable_through in Htrc_s;eauto.
    }
    assert (Hec_s' : env_contracts s' caddr = Some ((contract : WeakContract))).
    {
      pose proof H_init.
      decompose_is_init_state H_init.
      eapply reachable_through_contract_deployed in H_env_contracts.
      eauto.
      eapply transition_reachable_impl_reachable_through in Htrc_s;eauto.
    }
    eapply deployed_contract_state_typed in Hec_s';eauto.
    destruct Hec_s' as [cstate_s' Hcs_s'].
    
    eauto.
    unfold transition in Htrans.
    unfold queue_isb_empty in Htrans.
    rewrite Hqueue_s in Htrans.
    rewrite Hact_call in Htrans.
    destruct (evaluate_action true s (get_valid_header miner s)
    [attacker_call_PassHasBeenSetMsg cstate ]) eqn : H_exec;try congruence.
    unfold evaluate_action in H_exec.
    rewrite get_valid_header_is_valid_header in H_exec.
    destruct (find_origin_neq_from [attacker_call_PassHasBeenSetMsg cstate]) ; try congruence.
    destruct (find_invalid_root_action [attacker_call_PassHasBeenSetMsg cstate]);try congruence.
    set (mid_state := {|
      chain_state_env := add_new_block_to_env (get_valid_header miner s) s;
      chain_state_queue := [attacker_call_PassHasBeenSetMsg cstate]
    |}) in H_exec.
    simpl in *.
    destruct(
      send_or_call attacker attacker caddr 0
      (Some (serialize (PassHasBeenSetMsg (sha3 attacker_pass))))
      (add_new_block_to_env (get_valid_header miner s) s)) eqn : H_send_or_call_GetGift;try congruence.
    unfold send_or_call in  H_send_or_call_GetGift.
    simpl in H_send_or_call_GetGift.
    eapply address_not_contract_negb in H_miner.
    assert( H_caddr_not_EOA : address_is_contract caddr = true).
    {
      eapply contract_addr_format in Hec_s;eauto.
      eapply transition_reachable_impl_reachable in Htrc_s;eauto.  
    }
    destruct_address_eq;simpl in *;try congruence.
    
    (* 
      e: sender cstate = miner
      n: caddr <> sender cstate
      e0: caddr = caddr
      n0: caddr <> miner 
    *)

    destruct(0 >? miner_reward + env_account_balances s attacker)%Z;try congruence.
    rewrite Hec_s in H_send_or_call_GetGift.
    assert(Hcstate_s_t0:contract_state s caddr = Some cstate) by eauto.
    unfold contract_state in Hcstate_s_t0.
    simpl in Hcstate_s_t0.
    destruct (env_contract_states s caddr) eqn : Hcstate_s_t0';try congruence.
    destruct (weak_error_to_error_receive
    (wc_receive contract
       (s <| chain_height := S (chain_height s) |> <|
        current_slot := (current_slot s + 1)%nat |> <|
        finalized_height := finalized_height s |>)
       {|
         ctx_origin := attacker;
         ctx_from := attacker;
         ctx_contract_address := caddr;
         ctx_contract_balance :=
           0 + env_account_balances s caddr;
         ctx_amount := 0
       |} s1
       (Some
          (serialize
             (PassHasBeenSetMsg (sha3 attacker_pass)))))) eqn : H_wc_receive_s1;try congruence.
    unfold weak_error_to_error_receive in H_wc_receive_s1.
    unfold bind_error in H_wc_receive_s1.
    destruct (wc_receive contract
    (s <| chain_height := S (chain_height s) |> <| current_slot
     := (current_slot s + 1)%nat |> <| finalized_height :=
     finalized_height s |>)
    {|
      ctx_origin := attacker;
      ctx_from := attacker;
      ctx_contract_address := caddr;
      ctx_contract_balance := 0 + env_account_balances s caddr;
      ctx_amount := 0
    |} s1
    (Some (serialize (PassHasBeenSetMsg (sha3 attacker_pass)))))
      eqn : H_wc_receive_s1';try congruence.
    
    set (cchain := s <| chain_height := S (chain_height s) |> <| current_slot :=
    (current_slot s + 1)%nat |> <| finalized_height :=
    finalized_height s |>) in H_wc_receive_s1'.
    set (cctx := {|
    ctx_origin := user1;
    ctx_from := user1;
    ctx_contract_address := caddr;
    ctx_contract_balance := 0 + env_account_balances s caddr;
    ctx_amount := 0
    |}) in H_wc_receive_s1'.
    
    destruct t2 as [new_state new_acts].

    destruct (wc_receive_strong ltac:(try eassumption))
    as (prev_state_strong & msg_strong & resp_state_strong &
      deser_state & deser_msg & <- & receive).

    simpl in deser_msg.
    destruct (msg_strong) eqn : H_msg;try congruence.
    rewrite deserialize_serialize in deser_msg.
    rewrite <- deser_msg in receive.
    rewrite deser_state in Hcstate_s_t0.
    simpl in receive.
    rename receive into receive_some.
    unfold receive in receive_some.
    reduce_passHasBeenSet_fn.
    (* 111 *)
    inversion receive_some.
    subst.
    inversion H_wc_receive_s1;subst.
    inversion H_send_or_call_GetGift;subst.
    simpl in H_exec.
    inversion H_exec;subst.
    inversion Htrans;subst.
    inversion H_send_or_call_GetGift;subst.
    inversion Hcs_s';subst.
    unfold contract_state in H0.
    simpl in H0.
    destruct_address_eq;eauto.
    setoid_rewrite deserialize_serialize in H0.
    inversion H0.
    simpl.
    inversion Hcstate_s_t0.
    unfold funds.
    simpl.
    destruct_address_eq;try congruence.
    eauto.
    unfold funds.
    simpl.
    destruct_address_eq;try congruence.
    eauto.
    (* n: attacker <> miner
      e: caddr = attacker
      e0: caddr = caddr
      n0: caddr <> miner *)
    eapply address_not_contract_negb in attacker_eoa.
    rewrite e in *.
    intuition.
    (* 
      n: attacker <> miner
    n0: caddr <> attacker
    e: caddr = caddr
    n1: caddr <> miner
    
    *)
    destruct(0 >?  env_account_balances s attacker)%Z;try congruence.
    rewrite Hec_s in H_send_or_call_GetGift.
    assert(Hcstate_s_t0:contract_state s caddr = Some cstate) by eauto.
    unfold contract_state in Hcstate_s_t0.
    simpl in Hcstate_s_t0.
    destruct (env_contract_states s caddr) eqn : Hcstate_s_t0';try congruence.
    destruct (weak_error_to_error_receive
    (wc_receive contract
       (s <| chain_height := S (chain_height s) |> <|
        current_slot := (current_slot s + 1)%nat |> <|
        finalized_height := finalized_height s |>)
       {|
         ctx_origin := attacker;
         ctx_from := attacker;
         ctx_contract_address := caddr;
         ctx_contract_balance :=
           0 + env_account_balances s caddr;
         ctx_amount := 0
       |} s1
       (Some
          (serialize
             (PassHasBeenSetMsg (sha3 attacker_pass)))))) eqn : H_wc_receive_s1;try congruence.
    unfold weak_error_to_error_receive in H_wc_receive_s1.
    unfold bind_error in H_wc_receive_s1.
    destruct (wc_receive contract
    (s <| chain_height := S (chain_height s) |> <| current_slot
     := (current_slot s + 1)%nat |> <| finalized_height :=
     finalized_height s |>)
    {|
      ctx_origin := attacker;
      ctx_from := attacker;
      ctx_contract_address := caddr;
      ctx_contract_balance := 0 + env_account_balances s caddr;
      ctx_amount := 0
    |} s1
    (Some (serialize (PassHasBeenSetMsg (sha3 attacker_pass)))))
      eqn : H_wc_receive_s1';try congruence.
    
    set (cchain := s <| chain_height := S (chain_height s) |> <| current_slot :=
    (current_slot s + 1)%nat |> <| finalized_height :=
    finalized_height s |>) in H_wc_receive_s1'.
    set (cctx := {|
    ctx_origin := user1;
    ctx_from := user1;
    ctx_contract_address := caddr;
    ctx_contract_balance := 0 + env_account_balances s caddr;
    ctx_amount := 0
    |}) in H_wc_receive_s1'.
    
    destruct t2 as [new_state new_acts].

    destruct (wc_receive_strong ltac:(try eassumption))
    as (prev_state_strong & msg_strong & resp_state_strong &
      deser_state & deser_msg & <- & receive).

    simpl in deser_msg.
    destruct (msg_strong) eqn : H_msg;try congruence.
    rewrite deserialize_serialize in deser_msg.
    rewrite <- deser_msg in receive.
    rewrite deser_state in Hcstate_s_t0.
    simpl in receive.
    rename receive into receive_some.
    unfold receive in receive_some.
    reduce_passHasBeenSet_fn.
    (* 111 *)
    inversion receive_some.
    subst.
    inversion H_wc_receive_s1;subst.
    inversion H_send_or_call_GetGift;subst.
    simpl in H_exec.
    inversion H_exec;subst.
    inversion Htrans;subst.
    inversion H_send_or_call_GetGift;subst.
    inversion Hcs_s';subst.
    unfold contract_state in H0.
    simpl in H0.
    destruct_address_eq;eauto.
    setoid_rewrite deserialize_serialize in H0.
    inversion H0.
    simpl.
    inversion Hcstate_s_t0.
    unfold funds.
    simpl.
    destruct_address_eq;try congruence.
    eauto.
    unfold funds.
    simpl.
    destruct_address_eq;try congruence.
  Qed.

  Lemma attacker_call_PassHasBeenSetMsg_is_call_act_state_correct:
  forall (s s':ChainState) cstate,
      contract_state s caddr = Some cstate ->
      transition_reachable miner contract caddr s0 s ->
      cstate.(passHasBeenSet) = false ->
      cstate.(hashPass) = sha3 attacker_pass ->
      transition miner s (attacker_call_PassHasBeenSetMsg cstate) = Ok s' ->
      exists cstate',
        contract_state s' caddr = Some cstate' /\
        cstate'.(hashPass) = sha3 attacker_pass /\
        cstate'.(passHasBeenSet) = true.
  Proof.
    intros * Hcs_s Htrc_s H_passB H_pass Htrans.
    eapply transition_reachable_queue_is_empty in Htrc_s as Hqueue_s;eauto.
    assert (Hact_call : is_call_act ((attacker_call_PassHasBeenSetMsg cstate)) = true).
    {
      unfold is_call_act.
      unfold attacker_call_PassHasBeenSetMsg.
      unfold build_call.
      destruct_address_eq;eauto.
    }
    assert(ttrace_s_s : TransitionTrace miner s s) by eapply clnil.
    assert(ttrace_s_s' : TransitionTrace miner s s').
    {
      econstructor;eauto.
      eapply step_trans;eauto.
    }
    assert(Htrct_s_s' : reachable_via miner contract caddr s0 s s').
    {
      econstructor;eauto.
    }
    assert(Hrt : reachable_through s s').
    {
      eapply reachable_via_impl_reachable_through in Htrct_s_s';eauto.
    }
    assert(H_t: reachable s') by eauto.
    destruct H_t as [trace].
    assert (Hec_s : env_contracts s caddr = Some ((contract : WeakContract))).
    {
      pose proof H_init.
      decompose_is_init_state H_init.
      eapply reachable_through_contract_deployed in H_env_contracts.
      eauto.
      eapply transition_reachable_impl_reachable_through in Htrc_s;eauto.
    }
    assert (Hec_s' : env_contracts s' caddr = Some ((contract : WeakContract))).
    {
      pose proof H_init.
      decompose_is_init_state H_init.
      eapply reachable_through_contract_deployed in H_env_contracts.
      eauto.
      eapply transition_reachable_impl_reachable_through in Htrc_s;eauto.
    }
    eapply deployed_contract_state_typed in Hec_s';eauto.
    destruct Hec_s' as [cstate_s' Hcs_s'].
    exists cstate_s'.
    split.
    eauto.
    unfold transition in Htrans.
    unfold queue_isb_empty in Htrans.
    rewrite Hqueue_s in Htrans.
    rewrite Hact_call in Htrans.
    destruct (evaluate_action true s (get_valid_header miner s)
    [attacker_call_PassHasBeenSetMsg cstate ]) eqn : H_exec;try congruence.
    unfold evaluate_action in H_exec.
    rewrite get_valid_header_is_valid_header in H_exec.
    destruct (find_origin_neq_from [attacker_call_PassHasBeenSetMsg cstate]) ; try congruence.
    destruct (find_invalid_root_action [attacker_call_PassHasBeenSetMsg cstate]);try congruence.
    set (mid_state := {|
      chain_state_env := add_new_block_to_env (get_valid_header miner s) s;
      chain_state_queue := [attacker_call_PassHasBeenSetMsg cstate]
    |}) in H_exec.
    simpl in *.
    destruct(
      send_or_call attacker attacker caddr 0
      (Some (serialize (PassHasBeenSetMsg (sha3 attacker_pass))))
      (add_new_block_to_env (get_valid_header miner s) s)) eqn : H_send_or_call_GetGift;try congruence.
    unfold send_or_call in  H_send_or_call_GetGift.
    simpl in H_send_or_call_GetGift.
    eapply address_not_contract_negb in H_miner.
    assert( H_caddr_not_EOA : address_is_contract caddr = true).
    {
      eapply contract_addr_format in Hec_s;eauto.
      eapply transition_reachable_impl_reachable in Htrc_s;eauto.  
    }
    destruct_address_eq;simpl in *;try congruence.
    
    (* 
      e: sender cstate = miner
      n: caddr <> sender cstate
      e0: caddr = caddr
      n0: caddr <> miner 
    *)

    destruct(0 >? miner_reward + env_account_balances s attacker)%Z;try congruence.
    rewrite Hec_s in H_send_or_call_GetGift.
    assert(Hcstate_s_t0:contract_state s caddr = Some cstate) by eauto.
    unfold contract_state in Hcstate_s_t0.
    simpl in Hcstate_s_t0.
    destruct (env_contract_states s caddr) eqn : Hcstate_s_t0';try congruence.
    destruct (weak_error_to_error_receive
    (wc_receive contract
       (s <| chain_height := S (chain_height s) |> <|
        current_slot := (current_slot s + 1)%nat |> <|
        finalized_height := finalized_height s |>)
       {|
         ctx_origin := attacker;
         ctx_from := attacker;
         ctx_contract_address := caddr;
         ctx_contract_balance :=
           0 + env_account_balances s caddr;
         ctx_amount := 0
       |} s1
       (Some
          (serialize
             (PassHasBeenSetMsg (sha3 attacker_pass)))))) eqn : H_wc_receive_s1;try congruence.
    unfold weak_error_to_error_receive in H_wc_receive_s1.
    unfold bind_error in H_wc_receive_s1.
    destruct (wc_receive contract
    (s <| chain_height := S (chain_height s) |> <| current_slot
     := (current_slot s + 1)%nat |> <| finalized_height :=
     finalized_height s |>)
    {|
      ctx_origin := attacker;
      ctx_from := attacker;
      ctx_contract_address := caddr;
      ctx_contract_balance := 0 + env_account_balances s caddr;
      ctx_amount := 0
    |} s1
    (Some (serialize (PassHasBeenSetMsg (sha3 attacker_pass)))))
      eqn : H_wc_receive_s1';try congruence.
    
    set (cchain := s <| chain_height := S (chain_height s) |> <| current_slot :=
    (current_slot s + 1)%nat |> <| finalized_height :=
    finalized_height s |>) in H_wc_receive_s1'.
    set (cctx := {|
    ctx_origin := user1;
    ctx_from := user1;
    ctx_contract_address := caddr;
    ctx_contract_balance := 0 + env_account_balances s caddr;
    ctx_amount := 0
    |}) in H_wc_receive_s1'.
    
    destruct t2 as [new_state new_acts].

    destruct (wc_receive_strong ltac:(try eassumption))
    as (prev_state_strong & msg_strong & resp_state_strong &
      deser_state & deser_msg & <- & receive).

    simpl in deser_msg.
    destruct (msg_strong) eqn : H_msg;try congruence.
    rewrite deserialize_serialize in deser_msg.
    rewrite <- deser_msg in receive.
    rewrite deser_state in Hcstate_s_t0.
    simpl in receive.
    rename receive into receive_some.
    unfold receive in receive_some.
    reduce_passHasBeenSet_fn.
    (* 111 *)
    inversion receive_some.
    subst.
    inversion H_wc_receive_s1;subst.
    inversion H_send_or_call_GetGift;subst.
    simpl in H_exec.
    inversion H_exec;subst.
    inversion Htrans;subst.
    inversion H_send_or_call_GetGift;subst.
    inversion Hcs_s';subst.
    unfold contract_state in H0.
    simpl in H0.
    destruct_address_eq;eauto.
    setoid_rewrite deserialize_serialize in H0.
    inversion H0.
    simpl.
    inversion Hcstate_s_t0.
    rewrite <- H_pass.
    intuition.
    destruct_address_eq;try congruence.



    (* n: attacker <> miner
      e: caddr = attacker
      e0: caddr = caddr
      n0: caddr <> miner *)

    eapply address_not_contract_negb in attacker_eoa.
    rewrite e in *.
    intuition.

    (* 
      n: attacker <> miner
    n0: caddr <> attacker
    e: caddr = caddr
    n1: caddr <> miner
    
    *)
    destruct(0 >?  env_account_balances s attacker)%Z;try congruence.
    rewrite Hec_s in H_send_or_call_GetGift.
    assert(Hcstate_s_t0:contract_state s caddr = Some cstate) by eauto.
    unfold contract_state in Hcstate_s_t0.
    simpl in Hcstate_s_t0.
    destruct (env_contract_states s caddr) eqn : Hcstate_s_t0';try congruence.
    destruct (weak_error_to_error_receive
    (wc_receive contract
       (s <| chain_height := S (chain_height s) |> <|
        current_slot := (current_slot s + 1)%nat |> <|
        finalized_height := finalized_height s |>)
       {|
         ctx_origin := attacker;
         ctx_from := attacker;
         ctx_contract_address := caddr;
         ctx_contract_balance :=
           0 + env_account_balances s caddr;
         ctx_amount := 0
       |} s1
       (Some
          (serialize
             (PassHasBeenSetMsg (sha3 attacker_pass)))))) eqn : H_wc_receive_s1;try congruence.
    unfold weak_error_to_error_receive in H_wc_receive_s1.
    unfold bind_error in H_wc_receive_s1.
    destruct (wc_receive contract
    (s <| chain_height := S (chain_height s) |> <| current_slot
     := (current_slot s + 1)%nat |> <| finalized_height :=
     finalized_height s |>)
    {|
      ctx_origin := attacker;
      ctx_from := attacker;
      ctx_contract_address := caddr;
      ctx_contract_balance := 0 + env_account_balances s caddr;
      ctx_amount := 0
    |} s1
    (Some (serialize (PassHasBeenSetMsg (sha3 attacker_pass)))))
      eqn : H_wc_receive_s1';try congruence.
    
    set (cchain := s <| chain_height := S (chain_height s) |> <| current_slot :=
    (current_slot s + 1)%nat |> <| finalized_height :=
    finalized_height s |>) in H_wc_receive_s1'.
    set (cctx := {|
    ctx_origin := user1;
    ctx_from := user1;
    ctx_contract_address := caddr;
    ctx_contract_balance := 0 + env_account_balances s caddr;
    ctx_amount := 0
    |}) in H_wc_receive_s1'.
    
    destruct t2 as [new_state new_acts].

    destruct (wc_receive_strong ltac:(try eassumption))
    as (prev_state_strong & msg_strong & resp_state_strong &
      deser_state & deser_msg & <- & receive).

    simpl in deser_msg.
    destruct (msg_strong) eqn : H_msg;try congruence.
    rewrite deserialize_serialize in deser_msg.
    rewrite <- deser_msg in receive.
    rewrite deser_state in Hcstate_s_t0.
    simpl in receive.
    rename receive into receive_some.
    unfold receive in receive_some.
    reduce_passHasBeenSet_fn.
    (* 111 *)
    inversion receive_some.
    subst.
    inversion H_wc_receive_s1;subst.
    inversion H_send_or_call_GetGift;subst.
    simpl in H_exec.
    inversion H_exec;subst.
    inversion Htrans;subst.
    inversion H_send_or_call_GetGift;subst.
    inversion Hcs_s';subst.
    unfold contract_state in H0.
    simpl in H0.
    destruct_address_eq;eauto.
    setoid_rewrite deserialize_serialize in H0.
    inversion H0.
    simpl.
    inversion Hcstate_s_t0.
    rewrite <- H_pass.
    intuition.
    destruct_address_eq;try congruence.
  Qed.

  Require stdpp.countable.

  Lemma tmp:
    exists tr s (tr' : TransitionTrace miner s0 s)  cstate,
    interleavedExecution miner [honest] honest_strat [attacker] attacker_strat s0 s0 tr Tusr s tr' /\
    contract_state s caddr = Some cstate /\
    cstate.(passHasBeenSet) = true /\
    cstate.(hashPass) <> sha3 honest_pass /\
    funds s caddr > 0.
  Proof.
    assert (tr0 : TransitionTrace miner s0 s0) by eapply clnil.
    decompose_is_init_state H_init.
    simpl in *.
    reduce_init.
    unfold negb in Einit.
    destruct (setup_passHasBeenSet setup) eqn : H_passBset;try congruence.
    assert (exists s' , transition miner s0 (attacker_call_SetPass state) = Ok s').
    {
      eapply attacker_call_SetPass_is_call_act_transition_correct.
      unfold contract_state.
      rewrite H_env_states.
      simpl.
      setoid_rewrite deserialize_serialize.
      eauto.
      unfold transition_reachable.
      split.
      eauto.
      econstructor;eauto.
      inversion H_init0.
      simpl.
      eauto.
    }
    destruct H as [s' Htrans].
    eapply attacker_call_SetPass_is_call_act_state_correct in Htrans as Ht.
    destruct Ht as [Hcs_s' [Hhash Hset]].
    assert (Hcall : is_call_act (attacker_call_SetPass state) = true).
    {
      eapply attacker_call_SetPass_is_call_act.
    }

    set (tr_s' := snoc tr0 (step_trans miner (attacker_call_SetPass state) Hcall Htrans) ).

    assert (exists s'' , transition miner s' (attacker_call_PassHasBeenSetMsg Hcs_s') = Ok s'').
    {
      eapply attacker_call_PassHasBeenSetMsg_is_call_act_transition_correct.
      eauto.
      unfold contract_state.
      unfold transition_reachable.
      split.
      eauto.
      econstructor;eauto.
      eauto.
      inversion H_init0.
      simpl.
      destruct Hset.
      eauto.
      destruct Hset.
      eauto.
    }
    destruct H as [s'' Htrans''].
    eapply attacker_call_PassHasBeenSetMsg_is_call_act_state_correct in Htrans'' as Ht'.
    destruct Ht' as [Hcs_s'' [Hhash' Hset']].
    assert (Hcall' : is_call_act (attacker_call_PassHasBeenSetMsg Hcs_s') = true).
    {
      eapply attacker_call_PassHasBeenSetMsg_is_call_act.
    }
    set (tr_s'' := snoc tr_s' (step_trans miner (attacker_call_PassHasBeenSetMsg Hcs_s') Hcall' Htrans'') ).
    exists tr0.
    exists s''.
    exists tr_s''.
    exists Hcs_s''.
    split.
    assert (interleavedExecution miner [honest] honest_strat [attacker] attacker_strat s0
    s0 tr0 Tenv s0 tr0).
    {
      eapply IS_Refl.
    }
    (* stratDrive  addrs_usr delta_usr s0  s' tr' s'' tr'' *)
    assert (stratDrive miner [attacker] attacker_strat s0 s0 tr0 s' tr_s').
    {
      unfold stratDrive.
      exists (attacker_call_SetPass state).
      exists Hcall.
      exists Htrans.
      split;eauto.
      unfold attacker_strat.
      simpl.
      unfold get_contract_state.
      rewrite H_env_states.
      setoid_rewrite deserialize_serialize.
      destruct ((hashPass state =? sha3 attacker_pass)%N) eqn : Ht.
      + inversion H_init0;subst.
        simpl in *.
        congruence.
      + destruct (passHasBeenSet state) eqn : Ht'.
        - inversion H_init0;subst.
          simpl in *.
          congruence.
        - simpl.
          eauto.
    }
    assert (stratDrive miner [attacker] attacker_strat s0 s' tr_s' s'' tr_s'').
    {
      unfold stratDrive.
      exists (attacker_call_PassHasBeenSetMsg Hcs_s').
      exists Hcall'.
      exists Htrans''.
      split;eauto.
      unfold attacker_strat.
      simpl.
      unfold get_contract_state.
      unfold contract_state in Hhash.
      destruct (env_contract_states s' caddr) eqn : Hcstate_s';try congruence.
      simpl in *.
      rewrite Hhash.
      destruct Hset.
      rewrite H1.
      destruct ((sha3 attacker_pass =? sha3 attacker_pass)%N) eqn : Ht;try congruence.
      +  eauto.
        simpl.
        eauto.
      + eapply Pos.eqb_neq in Ht.
        unfold not in Ht.
        assert (countable.encode attacker_pass = countable.encode attacker_pass).
        {
        eapply stdpp.countable.encode_inj.
        eauto.
        }
        intuition.
      + simpl in  Hhash.
        congruence.
    }
    assert(multiStratDrive miner [attacker] attacker_strat s0 s0 tr0  s0 tr0 0) by eapply MS_Refl.
    assert(multiStratDrive miner [attacker] attacker_strat s0 s0 tr0  s' tr_s' 1).
    {
      eapply MS_Step in H2;eauto.
    }
    assert(multiStratDrive miner [attacker] attacker_strat s0 s0 tr0  s'' tr_s'' 2).
    {
      eapply MS_Step in H3;eauto.
    }

    eapply ISE_Step in H4;eauto.
    split.
    eauto.
    split.
    destruct Hset'.
    eauto.
    split.
    destruct Hset'.
    rewrite H.
    eauto.
    unfold sha3.
    unfold not.
    intros.
    inversion H1.
    eapply stdpp.countable.encode_inj in H3.
    congruence.
    eapply attacker_call_PassHasBeenSetMsg_is_call_act_state_correct_funds in Htrans'' as Ht.
    eapply attacker_call_SetPass_is_call_act_state_correct_funds in Htrans as Ht'.
    lia.
    unfold contract_state.
    rewrite H_env_states.
    simpl.
    setoid_rewrite deserialize_serialize.
    eauto.
    unfold transition_reachable.
    split.
    eauto.
    econstructor;eauto.
    inversion H_init0.
    simpl.
    eauto.
    eauto.
    unfold transition_reachable.
    split.
    eauto.
    econstructor;eauto.
    destruct Hset.
    eauto.
    destruct Hset.
    eauto.
    eauto.
    unfold transition_reachable.
    split.
    eauto.
    econstructor;eauto.
    destruct Hset.
    eauto.
    destruct Hset.
    eauto.
    eauto.
    unfold transition_reachable.
    unfold contract_state.
    rewrite H_env_states.
    simpl.
    setoid_rewrite deserialize_serialize.
    eauto.
    unfold transition_reachable.
    split.
    eauto.
    econstructor;eauto.
    inversion H_init0.
    simpl.
    eauto.
  Qed.
  
End Liqiuidity.

