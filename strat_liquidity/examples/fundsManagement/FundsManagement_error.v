
Require Import Blockchain.
Require Import Serializable.
Require Import Extras.
Require Import BuildUtils.
Require Import RecordUpdate.
Require Import Automation.
Require Import Containers.
Require Import ContractCommon.
Require Import ResultMonad.
Require Import ChainedList.
Require Import ModelBase.
Require Import StratModel.
Require Import ProofLib.

From Coq Require Import List.
From Coq Require Import Bool.
From Coq Require Import ZArith.
From Coq Require Import Arith.
From Coq Require Import String.
Import ListNotations.
Require Import Lia.
Import RecordSetNotations.

Require Import LibTactics. 

(* Context {BaseTypes : ChainBase}. *)

Variable zero_addr : Address.

Variable h_usr : Address.
Variable d_usr : Address.
Variable adm : Address.

Section FundsManagement.
  
  Set Primitive Projections.
  Set Nonrecursive Elimination Schemes.
  Context {AddrSize : N}.

  Local Open Scope Z.

  Definition Error : Type := nat.
  Definition default_error : Error := 1%nat.

  Definition bytes := N. 

  Definition bytes32 := N.

  Inductive Msg :=
  | ReqWithdrawal 
  | ProcessReq (a: Address) (b : bool) 
  | Withdraw
  | ReInit.  

  Global Instance Msg_serializable : Serializable Msg :=
    Derive Serializable Msg_rect<ReqWithdrawal, ProcessReq, Withdraw, ReInit>. 

  
  (* 0 -- None
       1 -- Requested
       2 -- Approved *)
  
  Record State :=
    build_state {
        status : (FMap Address nat);
        admin : Address 
      }.

  Definition status_requested := 1%nat.
  Definition status_approved := 2%nat. 

  Record Setup :=
    build_setup {
        setup_status : nat; 
        setup_admin : Address
      }.

  Instance state_settable : Settable State :=
    settable! build_state
    <status; admin>. 

  Instance setup_settable : Settable Setup :=
    settable! build_setup
    <setup_status; setup_admin>.


  Section Serialization.
    Global Instance State_serializable : Serializable State :=
      Derive Serializable State_rect<build_state>.

    Global Instance Setup_serializable : Serializable Setup :=
      Derive Serializable Setup_rect<build_setup>.
  End Serialization.

  Definition init 
    (chain : Chain)
    (ctx : ContractCallContext)
    (setup : Setup)
    : result State Error :=
    Ok (build_state FMap.empty adm).

  Definition reqWithdrawal 
    (ctx: ContractCallContext)
    (st : State) 
    : result (State * list ActionBody) Error :=
    match FMap.find ctx.(ctx_origin) st.(status) with
      Some _ => Err default_error
    | None => Ok (st <| status := FMap.update ctx.(ctx_origin) (Some status_requested) st.(status) |>, []) 
    end.

  Definition processReq
    (ctx : ContractCallContext)
    (st : State)
    (a: Address)
    (b : bool)
    : result (State * list ActionBody) Error :=
    match FMap.find a st.(status) with
      Some n => 
        if address_eqb ctx.(ctx_origin) st.(admin)
           && beq_nat n status_requested then 
          if b then
            Ok (st <| status := FMap.update a (Some status_approved) st.(status) |>, []) 
          else
            Ok (st <| status := FMap.update a None st.(status) |>, [])  
        else
          Err default_error
    | None => Err default_error
    end.  

  Definition withdraw
    (ctx : ContractCallContext)
    (st : State)
    : result (State * list ActionBody) Error :=
    match FMap.find ctx.(ctx_origin) st.(status) with
      Some n => 
        if beq_nat n status_approved then 
          Ok (st <| status := FMap.update ctx.(ctx_origin) None st.(status) |>, 
                  [ act_transfer ctx.(ctx_origin) ctx.(ctx_contract_balance) ])
        else
          Err default_error
    | None => Err default_error
    end.
  
  Definition reinit
    (ctx : ContractCallContext)
    (st : State)
    : result (State * list ActionBody) Error :=    
    Ok (st<| status := FMap.empty |><| admin := ctx.(ctx_origin) |>, []).  

  Definition receive
    (chain : Chain)
    (ctx : ContractCallContext)
    (st : State)
    (msg : option Msg)
    : result (State * list ActionBody) Error :=
    match msg with
    | Some ReqWithdrawal =>
        reqWithdrawal ctx st 
    | Some (ProcessReq a b) => 
        processReq ctx st a b 
    | Some Withdraw => 
        withdraw ctx st
    | Some ReInit =>
        reinit ctx st 
    | None => Ok (st, []) 
    end.
  
  Definition contract : Contract Setup Msg State Error :=
    build_contract init receive.

End FundsManagement. 


Section Liquidity.
  
  Set Primitive Projections.
  Set Nonrecursive Elimination Schemes.
  Context {AddrSize : N}.

  Definition get_contract_state (state : ChainState) (addr : Address) : option State :=
    match env_contract_states state addr with
    | Some serialized_state =>
        deserialize serialized_state
    | None => None
    end.

  Context `{caddr : Address} `{miner : Address}.

  Variable s0 : ChainState.
  Hypothesis H_init: is_init_state contract caddr s0.

  Variable init_cstate : State.
  Hypothesis H_state : get_contract_state s0 caddr = Some init_cstate.

  Require Coq.NArith.NArith. 
  Require stdpp.countable.
  Local Open Scope Z_scope.

  Tactic Notation "contract_simpl" := contract_simpl @receive @init.
  Ltac destruct_message :=
    repeat match goal with
      | H : Blockchain.receive _ _ _ _ _ = Ok _ |- _ => unfold Blockchain.receive in H; cbn in H
      | msg : option Msg |- _ => destruct msg
      | msg : Msg |- _ => destruct msg
      | H : Blockchain.receive _ _ _ _ None = Ok _ |- _ => now contract_simpl
      | H : receive _ _ _ None = Ok _ |- _ => now contract_simpl
      end.

  Ltac simpl_eval :=
    match goal with
    (* | H: context[FMap.find ?a ?m] |- _ => destruct (FMap.find a m) eqn: E_; simpl_eval *)
    | H: (if ?e then _ else _) = _ |- _ => destruct e; tryfalse; inverts H; simpl_eval
    | H: Ok _ = Ok _ |- _ => idtac
    | H: _ = Ok _ |- _ => unfolds in H; simpl_eval
    | _ => idtac
    end. 

  Hypothesis H_miner : address_not_contract miner= true.

  Hypothesis h_usr_eoa : address_not_contract h_usr = true.
  Hypothesis d_usr_eoa : address_not_contract d_usr = true.
  Hypothesis adm_eoa : address_not_contract adm = true.

  Hypothesis addr_neq : adm <> h_usr /\ adm <> d_usr /\ h_usr <> d_usr.   
  Hypothesis pos_bal: env_account_balances s0 caddr > 0.
  
  Definition attacker_call_reinit: Action :=
    build_call d_usr caddr 0 ReInit. 
  
  Definition usr_deposit: Action :=
    build_transfer h_usr caddr 1.
    
  Definition usr_call_reqWithdrawal: Action :=
    build_call h_usr caddr 0 ReqWithdrawal.

  Definition usr_call_withdraw: Action :=
    build_call h_usr caddr 0 Withdraw.

  Definition adm_call_processReq (a: Address): Action :=
    build_call adm caddr 0 (ProcessReq a true).

  Lemma trans_rc_env_contracts:
    forall s, 
      transition_reachable miner contract caddr s0 s ->
      env_contracts s caddr = Some (contract:WeakContract). 
  Proof.
    introv Htrc_s.
    eapply transition_reachable_impl_reachable_through in Htrc_s.
    eapply reachable_through_contract_deployed in Htrc_s;eauto.
    decompose_is_init_state H_init.
    eauto.
    eauto.
  Qed. 

  Lemma get_valid_header_is_valid_header s:
    validate_header (get_valid_header miner s) s = true. 
  Proof.
    intros.
    unfold get_valid_header.
    unfold validate_header.
    propify.
    repeat split;cbn ;try lia;eauto.
    unfold miner_reward.
    lia.
  Qed.

  Lemma reachable_ex_cstate :
    forall bstate,
      reachable bstate ->
      env_contracts bstate caddr = Some (contract : WeakContract) -> 
      exists cstate,
        contract_state bstate caddr = Some cstate /\ 
          exists ad, cstate.(admin) = ad. 
  Proof.
    intros.
    contract_induction; intros; auto; cbn in *;try congruence;try lia;eauto.
    solve_facts. 
  Qed. 
      
  Lemma att_reinit_transition_correct:
    forall (s:ChainState) (cstate: State) usr,
      contract_state s caddr = Some cstate ->
      transition_reachable miner contract caddr s0 s ->
      usr = adm \/ usr = d_usr -> 
      exists s',
        transition miner 5 s (build_call usr caddr 0 ReInit) = Ok s' /\
          funds s' caddr = funds s caddr /\  
          exists cs,
            contract_state s' caddr = Some cs /\
              cs.(status) = FMap.empty /\
              cs.(admin) = usr.   
  Proof.
    introv Hcs Htrc_s Hor.
    eexists. 
    unfold transition.
    unfold queue_isb_empty.
    eapply transition_reachable_queue_is_empty in Htrc_s as Hqueue_s;eauto.
    rewrite Hqueue_s.
    unfold evaluate_action.
    rewrite get_valid_header_is_valid_header; auto.
    unfold attacker_call_reinit.
    simpl.
    destruct_address_eq;try congruence.
    simpl.
    assert (Hec_s: env_contracts s caddr = Some (contract:WeakContract)).
    {
      eapply trans_rc_env_contracts; eauto.
    }
    assert (Hd_nc: address_is_contract usr = false).
    {
      inverts Hor; 
      eapply address_not_contract_negb; eauto.
    }
    assert(H_caddr_not_EOA : address_is_contract caddr = true).
    {
      eapply contract_addr_format in Hec_s;eauto.
      eapply transition_reachable_impl_reachable in Htrc_s;eauto.  
    }
    assert (Hrc: reachable s).
    {
      eapply transition_reachable_impl_reachable in H_init; eauto.
    }
    assert (Hb: env_account_balances s usr >= 0).
    {
      eapply account_balance_nonnegative; eauto.
    }
    rewrite Hd_nc.
    unfold send_or_call.
    simpl.

    destruct_address_eq;try congruence. 
    -      
      assert (Hzgt: 0 >? miner_reward + env_account_balances s usr = false). 
      {
        unfold miner_reward; lia.
      }
      rewrite Hzgt.
      rewrite Hec_s.
      unfold contract_state in Hcs.
      simpl in Hcs.
      destruct (env_contract_states s caddr) eqn: Ecs; try congruence.
      simpl.
      rewrite Hcs.
      simpl.
      setoid_rewrite deserialize_serialize.
      simpl.
      splits; eauto.
      unfold funds. unfold env_account_balances.
      simpl.
      destruct_address_eq; try congruence.
      destruct (chain_state_env s).
      simpl.
      lia.
      simpl.
      unfold set_contract_state.
      unfold contract_state.
      simpl.
      destruct_address_eq; try congruence.
      rewrite deserialize_serialize.
      eexists.
      splits; eauto.
    -
      assert (caddr <> miner).
      {
        eapply addr_ctr_neq; eauto.
      }
      false.
    -
      assert (Hg: 0 >? env_account_balances s usr = false).
      {
        lia. 
      }
      rewrite Hg.
      rewrite Hec_s.
      unfold contract_state in Hcs.
      simpl in Hcs.
      destruct (env_contract_states s caddr) eqn: Ecs; try congruence.
      simpl.
      rewrite Hcs.
      simpl.
      setoid_rewrite deserialize_serialize.
      simpl.
      splits; eauto.
      unfold funds. unfold env_account_balances.
      simpl.
      destruct_address_eq; try congruence.
      destruct (chain_state_env s).
      simpl.
      lia.
      unfold set_contract_state.
      unfold contract_state.
      simpl.
      destruct_address_eq; try congruence.
      rewrite deserialize_serialize.
      eexists.
      splits; eauto.
  Qed.      

  Lemma usr_req_transition_correct: 
    forall (s:ChainState) (cstate: State),
      contract_state s caddr = Some cstate ->
      FMap.find h_usr cstate.(status) = None -> 
      transition_reachable miner contract caddr s0 s ->
      exists s',
        transition miner 5 s usr_call_reqWithdrawal = Ok s' /\ 
          funds s' caddr = funds s caddr /\  
          exists cs,
            contract_state s' caddr = Some cs /\
              FMap.find h_usr cs.(status) = Some status_requested /\ 
              cs.(admin) = cstate.(admin).
  Proof.
    introv Hcs Hst Htrc_s.
    eexists. 
    unfold transition.
    unfold queue_isb_empty.
    eapply transition_reachable_queue_is_empty in Htrc_s as Hqueue_s;eauto.
    rewrite Hqueue_s.
    unfold evaluate_action.
    rewrite get_valid_header_is_valid_header; auto.
    unfold usr_call_reqWithdrawal.
    simpl.
    destruct_address_eq;try congruence.
    simpl.
    assert (Hec_s: env_contracts s caddr = Some (contract:WeakContract)).
    {
      eapply trans_rc_env_contracts; eauto.
    }
    assert (Hd_nc: address_is_contract h_usr = false).
    {
      eapply address_not_contract_negb; eauto.
    }
    assert(H_caddr_not_EOA : address_is_contract caddr = true).
    {
      eapply contract_addr_format in Hec_s;eauto.
      eapply transition_reachable_impl_reachable in Htrc_s;eauto.  
    }
    assert (Hrc: reachable s).
    {
      eapply transition_reachable_impl_reachable in H_init; eauto.
    }
    assert (Hb: env_account_balances s h_usr >= 0).
    {
      eapply account_balance_nonnegative; eauto.
    }
    rewrite Hd_nc.
    unfold send_or_call.
    simpl.

    destruct_address_eq;try congruence.
    -
      assert (Hzgt: 0 >? miner_reward + env_account_balances s h_usr = false). 
      {
        unfold miner_reward; lia. 
      }
      rewrite Hzgt.
      rewrite Hec_s.
      unfold contract_state in Hcs.
      simpl in Hcs.
      destruct (env_contract_states s caddr) eqn: Ecs; try congruence.
      simpl.
      rewrite Hcs.
      simpl.
      setoid_rewrite deserialize_serialize.
      simpl.
      unfold reqWithdrawal.
      simpl.
      rewrite Hst.
      simpl.
      split; eauto.
      split.
      {
        unfolds.
        simpl.
        destruct_address_eq;try congruence.
        lia.
      }
      {
        eexists. simpl.
        split.
        unfolds. simpl.
        rewrite address_eq_refl.
        rewrite deserialize_serialize.
        eauto.
        split.
        simpl; auto.
        simpl; auto.
      }
    -
      assert (caddr <> miner).
      {
        eapply addr_ctr_neq; eauto.
      }
      false.      
    -
      assert (Hzgt: 0 >? env_account_balances s h_usr = false) by lia.
      rewrite Hzgt.
      rewrite Hec_s.
      unfold contract_state in Hcs.
      simpl in Hcs.
      destruct (env_contract_states s caddr) eqn: Ecs; try congruence.
      simpl.
      rewrite Hcs.
      simpl.
      setoid_rewrite deserialize_serialize.
      simpl.
      unfold reqWithdrawal.
      simpl.
      rewrite Hst.
      simpl.
      split; eauto.
      split.
      {
        unfolds.
        simpl.
        destruct_address_eq;try congruence.
        lia.
      }
      {
        eexists. simpl.
        split.
        unfolds. simpl.
        rewrite address_eq_refl.
        rewrite deserialize_serialize.
        eauto.
        split.
        simpl; auto.
        simpl; auto.
      }
  Qed.
  
  Lemma adm_apr_transition_correct: 
    forall (s:ChainState) (cstate: State),
      contract_state s caddr = Some cstate ->
      FMap.find h_usr cstate.(status) = Some status_requested -> 
      cstate.(admin) = adm -> 
      transition_reachable miner contract caddr s0 s ->
      exists s',
        transition miner 5 s (adm_call_processReq h_usr) = Ok s' /\  
          funds s' caddr = funds s caddr /\  
          exists cs,
            contract_state s' caddr = Some cs /\
              FMap.find h_usr cs.(status) = Some status_approved /\ 
              cs.(admin) = cstate.(admin).
  Proof.
    introv Hcs Hst Hadm Htrc_s.
    eexists. 
    unfold transition.
    unfold queue_isb_empty.
    eapply transition_reachable_queue_is_empty in Htrc_s as Hqueue_s;eauto.
    rewrite Hqueue_s.
    unfold evaluate_action.
    rewrite get_valid_header_is_valid_header; auto.
    unfold adm_call_processReq. 
    simpl.
    destruct_address_eq;try congruence.
    simpl.
    assert (Hec_s: env_contracts s caddr = Some (contract:WeakContract)).
    {
      eapply trans_rc_env_contracts; eauto.
    }
    assert (Hd_nc: address_is_contract adm = false).
    {
      eapply address_not_contract_negb; eauto.
    }
    assert(H_caddr_not_EOA : address_is_contract caddr = true).
    {
      eapply contract_addr_format in Hec_s;eauto.
      eapply transition_reachable_impl_reachable in Htrc_s;eauto.  
    }
    assert (Hrc: reachable s).
    {
      eapply transition_reachable_impl_reachable in H_init; eauto.
    }
    assert (Hb: env_account_balances s adm >= 0).
    {
      eapply account_balance_nonnegative; eauto.
    }
    rewrite Hd_nc.
    unfold send_or_call.
    simpl.

    destruct_address_eq;try congruence.
    -
      asserts_rewrite (0 >? miner_reward + env_account_balances s adm = false). 
      {
        unfold miner_reward; lia. 
      }
      rewrite Hec_s.
      unfold contract_state in Hcs.
      simpl in Hcs.
      destruct (env_contract_states s caddr) eqn: Ecs; try congruence.
      simpl.
      rewrite Hcs.
      simpl.
      setoid_rewrite deserialize_serialize.
      simpl.
      unfold processReq. 
      simpl.
      asserts_rewrite (((adm =? admin cstate)%address) = true).
      {
        lets H__: address_eqb_spec adm (admin cstate).
        inverts H__; tryfalse; auto.
      }
      rewrite Hst.
      simpl.
      split; eauto.
      split.
      {
        unfolds.
        simpl.
        destruct_address_eq;try congruence.
        lia.
      }
      {
        eexists. simpl. 
        split.
        unfolds. simpl.
        rewrite address_eq_refl.
        rewrite deserialize_serialize.
        eauto.
        split.
        simpl; auto.
        simpl; auto.
      }
    -
      assert (caddr <> miner).
      {
        eapply addr_ctr_neq; eauto.
      }
      false.      
    -
      assert (Hzgt: 0 >? env_account_balances s adm = false) by lia.
      rewrite Hzgt.
      rewrite Hec_s.
      unfold contract_state in Hcs.
      simpl in Hcs.
      destruct (env_contract_states s caddr) eqn: Ecs; try congruence.
      simpl.
      rewrite Hcs.
      simpl.
      setoid_rewrite deserialize_serialize.
      simpl.
      unfold processReq. 
      simpl.
      asserts_rewrite (((adm =? admin cstate)%address) = true).
      {
        lets H__: address_eqb_spec adm (admin cstate).
        inverts H__; tryfalse; auto.
      }
      rewrite Hst.
      simpl.
      split; eauto.
      split.
      {
        unfolds.
        simpl.
        destruct_address_eq;try congruence.
        lia.
      }
      {
        eexists. simpl. 
        split.
        unfolds. simpl.
        rewrite address_eq_refl.
        rewrite deserialize_serialize.
        eauto.
        split.
        simpl; auto.
        simpl; auto.
      }
  Qed.       

  Lemma addr_not_ctr_none: 
    forall a s,
      reachable s -> 
      address_not_contract a = true -> 
      env_contracts s a = None.
  Proof.
    introv Hrc Hanc.
    destruct (env_contracts s a) eqn: E.
    - specialize (contract_addr_format a w Hrc E).
      introv Hf.
      unfold address_not_contract in Hanc.
      rewrite Hf in Hanc.
      false.
    - auto.
  Qed.
  
  Lemma usr_wth_transition_correct: 
    forall (s:ChainState) (cstate: State),
      contract_state s caddr = Some cstate ->
      FMap.find h_usr cstate.(status) = Some status_approved ->  
      transition_reachable miner contract caddr s0 s ->
      exists s',
        transition miner 5 s (usr_call_withdraw) = Ok s' /\   
          funds s' caddr = 0 /\  
          exists cs,
            contract_state s' caddr = Some cs /\
              FMap.find h_usr cs.(status) = None.
  Proof.
    introv Hcs Hst Htrc_s.
    eexists. 
    unfold transition.
    unfold queue_isb_empty.
    eapply transition_reachable_queue_is_empty in Htrc_s as Hqueue_s;eauto.
    rewrite Hqueue_s.
    unfold evaluate_action.
    rewrite get_valid_header_is_valid_header; auto.
    unfold usr_call_withdraw.  
    simpl.
    destruct_address_eq;try congruence.
    simpl.
    assert (Hec_s: env_contracts s caddr = Some (contract:WeakContract)).
    {
      eapply trans_rc_env_contracts; eauto.
    }
    assert (Hd_nc: address_is_contract h_usr = false).
    {
      eapply address_not_contract_negb; eauto.
    }
    assert(H_caddr_not_EOA : address_is_contract caddr = true).
    {
      eapply contract_addr_format in Hec_s;eauto.
      eapply transition_reachable_impl_reachable in Htrc_s;eauto.  
    }
    assert (Hrc: reachable s).
    {
      eapply transition_reachable_impl_reachable in H_init; eauto.
    }
    assert (Hb: env_account_balances s h_usr >= 0).
    {
      eapply account_balance_nonnegative; eauto.
    }
    assert (Hc: env_account_balances s caddr >= 0).
    {
      eapply account_balance_nonnegative; eauto.
    }
    rewrite Hd_nc.
    unfold send_or_call.
    simpl.

    destruct_address_eq;try congruence.
    -
      assert (Hzgt: 0 >? miner_reward + env_account_balances s h_usr = false). 
      {
        unfold miner_reward; lia. 
      }
      rewrite Hzgt.
      rewrite Hec_s.
      unfold contract_state in Hcs.
      simpl in Hcs.
      destruct (env_contract_states s caddr) eqn: Ecs; try congruence.
      simpl.
      rewrite Hcs.
      simpl.
      setoid_rewrite deserialize_serialize.
      simpl.
      unfold withdraw. 
      simpl.
      rewrite Hst.
      simpl.
      unfold send_or_call.
      asserts_rewrite (0 + env_account_balances s caddr <? 0 = false).
      {
        lets H__: Z.ltb_spec0 (0 + env_account_balances s caddr) 0.
        inverts H__; try (false; lia); auto.
      }
      match goal with
        H: _ |- context [?t1 >? ?t2] => asserts_rewrite (t1 >? t2 = false)
      end.
      {
        simpl.
        destruct_address_eq;try congruence.
        lia.
      }
      simpl.
      lets Hn: addr_not_ctr_none Hrc h_usr_eoa.
      rewrite Hn.
      asserts_rewrite (address_is_contract h_usr = false).
      {
        unfolds in h_usr_eoa.
        destruct (address_is_contract h_usr); tryfalse; auto.
      }
      simpl.
      split.
      eauto.
      split.
      {
        unfolds.
        simpl.
        destruct_address_eq;try congruence.
        lia.
      }
      {
        eexists. simpl. 
        split.
        unfolds. simpl.
        rewrite address_eq_refl.
        rewrite deserialize_serialize.
        eauto.
        simpl. apply FMap.find_remove. 
      }
    -
      assert (caddr <> miner).
      {
        eapply addr_ctr_neq; eauto.
      }
      false.      
    -
      asserts_rewrite (0 >? env_account_balances s h_usr = false).
      { lia. }
      rewrite Hec_s.
      unfold contract_state in Hcs.
      simpl in Hcs.
      destruct (env_contract_states s caddr) eqn: Ecs; try congruence.
      simpl.
      rewrite Hcs.
      simpl.
      setoid_rewrite deserialize_serialize.
      simpl.
      unfold withdraw. 
      simpl.
      rewrite Hst.
      simpl.
      unfold send_or_call.
      asserts_rewrite (0 + env_account_balances s caddr <? 0 = false).
      {
        lets H__: Z.ltb_spec0 (0 + env_account_balances s caddr) 0.
        inverts H__; try (false; lia); auto.
      }
      match goal with
        H: _ |- context [?t1 >? ?t2] => asserts_rewrite (t1 >? t2 = false)
      end.
      {
        simpl.
        destruct_address_eq;try congruence.
        lia.
      }
      simpl.
      lets Hn: addr_not_ctr_none Hrc h_usr_eoa.
      rewrite Hn.
      asserts_rewrite (address_is_contract h_usr = false).
      {
        unfolds in h_usr_eoa.
        destruct (address_is_contract h_usr); tryfalse; auto.
      }
      simpl.
      split.
      eauto.
      split.
      {
        unfolds.
        simpl.
        destruct_address_eq;try congruence.
        lia.
      }
      {
        eexists. simpl. 
        split.
        unfolds. simpl.
        rewrite address_eq_refl.
        rewrite deserialize_serialize.
        eauto.
        simpl. apply FMap.find_remove.
      }
  Qed.
  
  (* basic liquidity is satisfied *) 
  Theorem fm_sat_base_liquidity:
    base_liquidity miner contract caddr s0.
  Proof.
    unfold base_liquidity.
    introv Hini Htrc.
    assert (Hrcs: reachable s).
    {
      specialize (transition_reachable_impl_reachable miner contract caddr s0 s).
      introv H_. apply H_ in Hini; auto.
    }
    assert (Hec_s:env_contracts s caddr = Some (contract:WeakContract)).
    {
      eapply transition_reachable_impl_reachable_through in Htrc.
      eapply reachable_through_contract_deployed in Htrc;eauto.
      decompose_is_init_state H_init.
      eauto.
      eauto.
    }
    lets H_: reachable_ex_cstate Hrcs Hec_s.
    destruct H_ as (cs & Hcs & _).
    
    lets H__: att_reinit_transition_correct adm Hcs Htrc.
    specializes H__; eauto.
    destruct H__ as (s' & Htr' & fd' & Hex).
    destruct Hex as (cs' & Hcs' & Hst' & Had').
    specialize (transition_reachable_transition_transition_reachable
                  miner 5 s0 s s' (build_call adm caddr 0 ReInit) contract caddr).
    introv Htrc'.
    specializes Htrc'; eauto.
    assert (Hfd': FMap.find h_usr (status cs') = None).
    { simpl. rewrite Hst'. auto. }
    
    lets H__: usr_req_transition_correct Hcs' Hfd' Htrc'.
    destruct H__ as (s'0 & Hs'0 & Hfd'0 & Hex).
    destruct Hex as (cs'0 & Hcs'0 & Hfm'0 & Had'0). 
    specialize (transition_reachable_transition_transition_reachable
                  miner 5 s0 s' s'0 usr_call_reqWithdrawal contract caddr).
    introv Htrc'0.
    specializes Htrc'0; eauto.
    assert (Hadm'0: admin cs'0 = adm).
    { congruence. }

    lets H__: adm_apr_transition_correct Hcs'0 Hfm'0 Hadm'0 Htrc'0.
    destruct H__ as (s'1 & Hs'1 & Hfd'1 & Hex).
    destruct Hex as (cs'1 & Hcs'1 & Hfm'1 & Had'1).
    specialize (transition_reachable_transition_transition_reachable
                  miner 5 s0 s'0 s'1 (adm_call_processReq h_usr) contract caddr).
    introv Htrc'1.
    specializes Htrc'1; eauto.
    assert (Hadm'1: admin cs'1 = adm).
    { congruence. }

    lets H__: usr_wth_transition_correct Hcs'1 Hfm'1 Htrc'1.
    destruct H__ as (s'2 & Htr'2 & Hfd'2 & Hex).

    exists s'2.
    split; auto.
    constructors.
    eapply snoc; eauto.
    instantiate (1:=s'1).
    2: constructors; eauto.
    eapply snoc; eauto.
    instantiate (1:=s'0).
    2: constructors; eauto.
    eapply snoc; eauto.
    instantiate (1:=s').
    2: constructors; eauto.
    eapply snoc; eauto.
    instantiate (1:=s).
    2: constructors; eauto.
    constructors. 
  Qed.


  (* definitions and lemmas for refutation of strategy-aware liquidity *) 

  Definition attacker_strat : (strat miner [d_usr]) :=
    fun s0 s tr =>
      match get_contract_state s caddr with
      | Some state =>
          match FMap.find h_usr state.(status) with
          | Some n => 
              if ((n =? status_requested)%nat) then 
                [attacker_call_reinit]
              else 
                []
          | None => []
          end
      | None => []
      end.

  Definition honest_strat : (strat miner [h_usr; adm]) :=
    fun s0 s tr =>
      match get_contract_state s caddr with
      | Some state =>
          [usr_deposit; 
           usr_call_reqWithdrawal;
           usr_call_withdraw;
           adm_call_processReq h_usr;
           adm_call_processReq d_usr]  
      | None => []
      end.

  Lemma md_none:
    forall s (cstate: State) (tr: TransitionTrace miner s0 s),
      funds s caddr > 0 -> 
      contract_state s caddr = Some cstate ->
      FMap.find h_usr (status cstate) = Some status_requested -> 
      transition_reachable miner contract caddr s0 s ->
      exists s' tr' n,
        multiStratDrive miner [d_usr] attacker_strat s0 s tr s' tr' n /\
          transition_reachable miner contract caddr s0 s' /\
          funds s' caddr > 0 /\
          exists cst, 
            contract_state s' caddr = Some cst /\
              status cst = FMap.empty.
  Proof.
    introv Hfd Hcs Hreq Hrc.
    lets H_: att_reinit_transition_correct d_usr Hcs Hrc.
    specializes H_; eauto.
    protect addr_neq.
    destruct_and_split.
    exists x.
    do 2 eexists.
    splits.
    constructors. 
    2: {
      exists attacker_call_reinit.
      eexists.
      exists H.
      split.
      unfold attacker_strat. 
      unfold get_contract_state.
      unfold contract_state in Hcs.
      simpl in Hcs.
      rewrite Hcs.
      rewrite Hreq.
      rewrite Nat.eqb_refl.
      simpl; auto.
      eauto.
    }
    constructors.
    eapply transition_reachable_transition_transition_reachable; eauto.
    lia.
    eexists; splits; eauto.
  Qed. 
      
  Lemma exe_pos_funds:  
    exists tr s tr' cstate,
      interleavedExecution miner [h_usr; adm] honest_strat [d_usr] attacker_strat s0 s0 tr Tusr s tr' /\
        contract_state s caddr = Some cstate /\
        cstate.(status) = FMap.empty /\ 
        funds s caddr > 0.
  Proof.
    assert (tr0 : TransitionTrace miner s0 s0) by eapply clnil.
    do 4 eexists.
    split.
    eapply IS_Refl. 
    splits; eauto.
    unfold is_init_state in H_init.
    destruct H_init as (Hrc & Hcsq & Hec & Hex).
    destruct Hex as (ctx & setup & st & Hec_ & Hini).
    unfold Blockchain.init in Hini.
    unfold contract in Hini.
    unfold get_contract_state in H_state.
    rewrite Hec_ in H_state.
    rewrite deserialize_serialize in H_state.
    inverts H_state. 
    unfold init in Hini.
    destruct (address_neqb (setup_admin setup) zero_addr) eqn: E; tryfalse. 
    inverts Hini.
    simpl; auto.

    inverts Hini. simpl. auto.
    
    Unshelve.
    auto.
  Qed. 

  Lemma user_deposit_post:
    forall s (cst: State) n s', 
      funds s caddr > 0 -> 
      contract_state s caddr = Some cst -> 
      FMap.find h_usr (status cst) = None -> 
      transition_reachable miner contract caddr s0 s ->
      transition miner n s (usr_deposit) = Ok s' -> 
      funds s' caddr > 0 /\
        exists cst',
          contract_state s' caddr = Some cst' /\
            FMap.find h_usr (status cst') = None.
  Proof.
    introv Hfd Hcs_s Hcst Htrc_s Htrans.
    unfold transition in Htrans.
    unfold queue_isb_empty in Htrans.
    eapply transition_reachable_queue_is_empty in Htrc_s as Hqueue_s;eauto.
    rewrite Hqueue_s in Htrans.
    unfold evaluate_action in Htrans.
    rewrite get_valid_header_is_valid_header in Htrans.
    unfold usr_deposit in Htrans.
    simpl in Htrans.
    destruct_address_eq;try congruence.
    simpl in Htrans.
    assert (Hec_s:env_contracts s caddr = Some (contract:WeakContract)).
    {
      eapply transition_reachable_impl_reachable_through in Htrc_s.
      eapply reachable_through_contract_deployed in Htrc_s;eauto.
      decompose_is_init_state H_init.
      eauto.
      eauto.
    }
    eapply address_not_contract_negb in h_usr_eoa.
    rewrite h_usr_eoa in Htrans.
    destruct n. 
    simpl in Htrans; false.
    simpl in Htrans.
    assert(H_caddr_not_EOA : address_is_contract caddr = true).
    {
      eapply contract_addr_format in Hec_s;eauto.
      eapply transition_reachable_impl_reachable in Htrc_s;eauto.  
    }
    assert(Hrc_s:reachable s).
    {
      eapply transition_reachable_impl_reachable in Htrc_s;eauto.
    }
    unfold send_or_call in Htrans.
    simpl in Htrans.
    destruct_address_eq;try congruence.
    
    -
      assert (Hgtn: (1 >? miner_reward + env_account_balances s h_usr)%Z 
              = false).
      {
        unfold miner_reward.
        eapply (account_balance_nonnegative s h_usr) in Hrc_s.
        lia.        
      }
      rewrite Hgtn in Htrans.
      rewrite Hec_s in Htrans.
      unfold contract_state in Hcs_s.
      simpl in Hcs_s.
      destruct (env_contract_states s caddr) eqn: Ecs; try congruence.
      unfold weak_error_to_error_receive in Htrans.
      simpl in Htrans.
      rewrite Hcs_s in Htrans.
      simpl in Htrans.

      destruct n.
      {
        simpl in Htrans.
        inverts Htrans.
        split.
        unfold funds.
        simpl.
        destruct_address_eq;try congruence.
        unfold funds in Hfd.
        lia.
        eexists.
        split; eauto.
        simpl.
        unfold contract_state.
        simpl.
        lets H_: address_eqb_spec caddr caddr.
        inverts H_; tryfalse; auto.
        rewrite deserialize_serialize; eauto.
      }
      {
        simpl in Htrans.
        inverts Htrans.
        split.
        unfold funds.
        simpl.
        destruct_address_eq;try congruence.
        unfold funds in Hfd.
        lia.
        eexists.
        split; eauto.
        simpl.
        unfold contract_state.
        simpl.
        lets H_: address_eqb_spec caddr caddr.
        inverts H_; tryfalse; auto.
        rewrite deserialize_serialize; eauto.
      }
    -
      assert (caddr <> miner).
      {
        eapply addr_ctr_neq; eauto.
      }
      false. 
    -
      destruct (1 >? env_account_balances s h_usr) eqn: Egt; tryfalse. 
      rewrite Hec_s in Htrans.
      simpl in Htrans.
      unfold contract_state in Hcs_s.
      simpl in Hcs_s.
      destruct (env_contract_states s caddr) eqn: Ecs; try congruence.
      unfold weak_error_to_error_receive in Htrans.
      simpl in Htrans.
      rewrite Hcs_s in Htrans.
      simpl in Htrans.
      destruct n.
      {
        simpl in Htrans.
        inverts Htrans.
        split.
        unfold funds.
        simpl.
        destruct_address_eq;try congruence.
        unfold funds in Hfd.
        lia.
        eexists.
        split; eauto.
        simpl.
        unfold contract_state.
        simpl.
        lets H_: address_eqb_spec caddr caddr.
        inverts H_; tryfalse; auto.
        rewrite deserialize_serialize; eauto.
      }
      {
        simpl in Htrans.
        inverts Htrans.
        split.
        unfold funds.
        simpl.
        destruct_address_eq;try congruence.
        unfold funds in Hfd.
        lia.
        eexists.
        split; eauto.
        simpl.
        unfold contract_state.
        simpl.
        lets H_: address_eqb_spec caddr caddr.
        inverts H_; tryfalse; auto.
        rewrite deserialize_serialize; eauto.        
      }
  Qed. 
  
  Lemma user_req_withdrawal_post:
    forall s (cst: State) n s', 
      funds s caddr > 0 -> 
      contract_state s caddr = Some cst -> 
      FMap.find h_usr (status cst) = None -> 
      transition_reachable miner contract caddr s0 s ->
      transition miner n s (usr_call_reqWithdrawal) = Ok s' -> 
      funds s' caddr > 0 /\
        exists cst',
          contract_state s' caddr = Some cst' /\
            FMap.find h_usr (status cst') = Some status_requested.
  Proof.
    introv Hfd Hcs_s Hcst Htrc_s Htrans.
    unfold transition in Htrans.
    unfold queue_isb_empty in Htrans.
    eapply transition_reachable_queue_is_empty in Htrc_s as Hqueue_s;eauto.
    rewrite Hqueue_s in Htrans.
    unfold evaluate_action in Htrans.
    rewrite get_valid_header_is_valid_header in Htrans.
    unfold usr_call_reqWithdrawal in Htrans. 
    simpl in Htrans.
    destruct_address_eq;try congruence.
    simpl in Htrans.
    assert (Hec_s:env_contracts s caddr = Some (contract:WeakContract)).
    {
      eapply transition_reachable_impl_reachable_through in Htrc_s.
      eapply reachable_through_contract_deployed in Htrc_s;eauto.
      decompose_is_init_state H_init.
      eauto.
      eauto.
    }
    assert(H_caddr_not_EOA : address_is_contract caddr = true).
    {
      eapply contract_addr_format in Hec_s;eauto.
      eapply transition_reachable_impl_reachable in Htrc_s;eauto.  
    }
    assert(Hrc_s:reachable s).
    {
      eapply transition_reachable_impl_reachable in Htrc_s;eauto.
    }
    eapply address_not_contract_negb in h_usr_eoa.
    rewrite h_usr_eoa in Htrans.
    
    destruct n. 
    simpl in Htrans; false.
    simpl in Htrans.
    unfold send_or_call in Htrans.
    simpl in Htrans.
    destruct_address_eq;try congruence.
    -
      assert (Hgtn: (0 >? miner_reward + env_account_balances s h_usr)%Z 
              = false).
      {
        unfold miner_reward.
        eapply (account_balance_nonnegative s h_usr) in Hrc_s.
        lia.        
      }
      rewrite Hgtn in Htrans.
      rewrite Hec_s in Htrans.
      unfold contract_state in Hcs_s.
      simpl in Hcs_s.
      destruct (env_contract_states s caddr) eqn: Ecs; try congruence.
      unfold weak_error_to_error_receive in Htrans.
      simpl in Htrans.
      rewrite Hcs_s in Htrans.
      rewrite deserialize_serialize in Htrans.
      unfold error_to_weak_error in Htrans.
      unfold reqWithdrawal in Htrans.
      simpl in Htrans.
      rewrite Hcst in Htrans.
      simpl in Htrans.
      destruct n.
      {
        simpl in Htrans.
        inverts Htrans.
        split.
        unfold funds.
        simpl.
        destruct_address_eq;try congruence.
        unfold funds in Hfd.
        lia.
        eexists.
        split; eauto.
        simpl.
        unfold contract_state.
        simpl.
        lets H_: address_eqb_spec caddr caddr.
        inverts H_; tryfalse; auto.
        rewrite deserialize_serialize; eauto.
        simpl; auto.
      }
      {
        simpl in Htrans.
        inverts Htrans.
        split.
        unfold funds.
        simpl.
        destruct_address_eq;try congruence.
        unfold funds in Hfd.
        lia.
        eexists.
        split; eauto.
        simpl.
        unfold contract_state.
        simpl.
        lets H_: address_eqb_spec caddr caddr.
        inverts H_; tryfalse; auto.
        rewrite deserialize_serialize; eauto.
        simpl; auto.        
      }
    -
      assert (caddr <> miner).
      {
        eapply addr_ctr_neq; eauto.
      }
      false. 
    -
      assert (Hgtn: (0 >? env_account_balances s h_usr)%Z = false).
      {
        eapply (account_balance_nonnegative s h_usr) in Hrc_s.
        lia.        
      }
      rewrite Hgtn in Htrans.
      rewrite Hec_s in Htrans.
      unfold contract_state in Hcs_s.
      simpl in Hcs_s.
      destruct (env_contract_states s caddr) eqn: Ecs; try congruence.
      unfold weak_error_to_error_receive in Htrans.
      simpl in Htrans.
      rewrite Hcs_s in Htrans.
      rewrite deserialize_serialize in Htrans.
      unfold error_to_weak_error in Htrans.
      unfold reqWithdrawal in Htrans.
      simpl in Htrans.
      rewrite Hcst in Htrans.
      simpl in Htrans.
      destruct n.
      {
        simpl in Htrans.
        inverts Htrans.
        split.
        unfold funds.
        simpl.
        destruct_address_eq;try congruence.
        unfold funds in Hfd.
        lia.
        eexists.
        split; eauto.
        simpl.
        unfold contract_state.
        simpl.
        lets H_: address_eqb_spec caddr caddr.
        inverts H_; tryfalse; auto.
        rewrite deserialize_serialize; eauto.
        simpl; auto.
      }
      {
        simpl in Htrans.
        inverts Htrans.
        split.
        unfold funds.
        simpl.
        destruct_address_eq;try congruence.
        unfold funds in Hfd.
        lia.
        eexists.
        split; eauto.
        simpl.
        unfold contract_state.
        simpl.
        lets H_: address_eqb_spec caddr caddr.
        inverts H_; tryfalse; auto.
        rewrite deserialize_serialize; eauto.
        simpl; auto.        
      }
  Qed.       
      
  Lemma user_withdraw_post:
    forall s (cst: State) n s', 
      funds s caddr > 0 -> 
      contract_state s caddr = Some cst -> 
      FMap.find h_usr (status cst) = None -> 
      transition_reachable miner contract caddr s0 s ->
      transition miner n s (usr_call_withdraw) = Ok s' -> 
      False.
  Proof.
    introv Hfd Hcs_s Hcst Htrc_s Htrans.
    unfold transition in Htrans.
    unfold queue_isb_empty in Htrans.
    eapply transition_reachable_queue_is_empty in Htrc_s as Hqueue_s;eauto.
    rewrite Hqueue_s in Htrans.
    unfold evaluate_action in Htrans.
    rewrite get_valid_header_is_valid_header in Htrans.
    unfold usr_call_withdraw in Htrans. 
    simpl in Htrans.
    destruct_address_eq;try congruence.
    simpl in Htrans.
    assert (Hec_s:env_contracts s caddr = Some (contract:WeakContract)).
    {
      eapply transition_reachable_impl_reachable_through in Htrc_s.
      eapply reachable_through_contract_deployed in Htrc_s;eauto.
      decompose_is_init_state H_init.
      eauto.
      eauto.
    }
    assert(H_caddr_not_EOA : address_is_contract caddr = true).
    {
      eapply contract_addr_format in Hec_s;eauto.
      eapply transition_reachable_impl_reachable in Htrc_s;eauto.  
    }
    assert(Hrc_s:reachable s).
    {
      eapply transition_reachable_impl_reachable in Htrc_s;eauto.
    }
    (* assert (Hcseq: (status cst =? status_approved)%nat = false). *)
    (* { *)
    (*   lets H_: Nat.eqb_spec (status cst) status_approved. *)
    (*   inverts H_; eauto. *)
    (* } *)

    eapply address_not_contract_negb in h_usr_eoa.
    rewrite h_usr_eoa in Htrans.
    
    destruct n. 
    simpl in Htrans; false.
    simpl in Htrans.
    unfold send_or_call in Htrans.
    simpl in Htrans.
    destruct_address_eq;try congruence.
    -
      assert (Hgtn: (0 >? miner_reward + env_account_balances s h_usr)%Z 
              = false).
      {
        unfold miner_reward.
        eapply (account_balance_nonnegative s h_usr) in Hrc_s.
        lia.        
      }
      rewrite Hgtn in Htrans.
      rewrite Hec_s in Htrans.
      unfold contract_state in Hcs_s.
      simpl in Hcs_s.
      destruct (env_contract_states s caddr) eqn: Ecs; try congruence.
      unfold weak_error_to_error_receive in Htrans.
      simpl in Htrans.
      rewrite Hcs_s in Htrans.
      rewrite deserialize_serialize in Htrans.
      unfold error_to_weak_error in Htrans.
      simpl in Htrans.
      unfold withdraw in Htrans.
      simpl in Htrans.      
      rewrite Hcst in Htrans.
      simpl in Htrans.
      false.
    -
      assert (caddr <> miner).
      {
        eapply addr_ctr_neq; eauto.
      }
      false. 
    -
      assert (Hgtn: (0 >? env_account_balances s h_usr) = false).
      {
        eapply (account_balance_nonnegative s h_usr) in Hrc_s.
        lia.        
      }
      rewrite Hgtn in Htrans.
      rewrite Hec_s in Htrans.
      unfold contract_state in Hcs_s.
      simpl in Hcs_s.
      destruct (env_contract_states s caddr) eqn: Ecs; try congruence.
      unfold weak_error_to_error_receive in Htrans.
      simpl in Htrans.
      rewrite Hcs_s in Htrans.
      rewrite deserialize_serialize in Htrans.
      unfold error_to_weak_error in Htrans.
      simpl in Htrans.
      unfold withdraw in Htrans.
      simpl in Htrans.
      rewrite Hcst in Htrans.
      simpl in Htrans.
      false.
  Qed.      

  Lemma adm_process_req_post:
    forall s (cst: State) n s' usr, 
      funds s caddr > 0 -> 
      contract_state s caddr = Some cst -> 
      FMap.find usr (status cst) = None ->  
      transition_reachable miner contract caddr s0 s ->
      transition miner n s (adm_call_processReq usr) = Ok s' -> 
      False.
  Proof.
    introv Hfd Hcs_s Hcst Htrc_s Htrans.
    unfold transition in Htrans.
    unfold queue_isb_empty in Htrans.
    eapply transition_reachable_queue_is_empty in Htrc_s as Hqueue_s;eauto.
    rewrite Hqueue_s in Htrans.
    unfold evaluate_action in Htrans.
    rewrite get_valid_header_is_valid_header in Htrans.
    unfold adm_call_processReq in Htrans. 
    simpl in Htrans.
    destruct_address_eq;try congruence.
    simpl in Htrans.
    assert (Hec_s:env_contracts s caddr = Some (contract:WeakContract)).
    {
      eapply transition_reachable_impl_reachable_through in Htrc_s.
      eapply reachable_through_contract_deployed in Htrc_s;eauto.
      decompose_is_init_state H_init.
      eauto.
      eauto.
    }
    assert(H_caddr_not_EOA : address_is_contract caddr = true).
    {
      eapply contract_addr_format in Hec_s;eauto.
      eapply transition_reachable_impl_reachable in Htrc_s;eauto.  
    }
    assert(Hrc_s:reachable s).
    {
      eapply transition_reachable_impl_reachable in Htrc_s;eauto.
    }
    (* assert (Hcseq: (status cst =? status_requested)%nat = false). *)
    (* { *)
    (*   lets H_: Nat.eqb_spec (status cst) status_approved. *)
    (*   inverts H_; eauto. *)
    (* } *)

    eapply address_not_contract_negb in adm_eoa.
    rewrite adm_eoa in Htrans.
    
    destruct n. 
    simpl in Htrans; false.
    simpl in Htrans.
    unfold send_or_call in Htrans.
    simpl in Htrans.
    destruct_address_eq;try congruence.
    -
      assert (Hgtn: (0 >? miner_reward + env_account_balances s adm)%Z 
              = false).
      {
        unfold miner_reward.
        eapply (account_balance_nonnegative s adm) in Hrc_s.
        lia.        
      }
      rewrite Hgtn in Htrans.
      rewrite Hec_s in Htrans.
      unfold contract_state in Hcs_s.
      simpl in Hcs_s.
      destruct (env_contract_states s caddr) eqn: Ecs; try congruence.
      unfold weak_error_to_error_receive in Htrans.
      simpl in Htrans.
      rewrite Hcs_s in Htrans.
      rewrite deserialize_serialize in Htrans.
      unfold error_to_weak_error in Htrans.
      simpl in Htrans.
      unfold processReq in Htrans.
      simpl in Htrans.
      rewrite Hcst in Htrans.
      simpl in Htrans.
      destruct_address_eq;try congruence; 
      simpl in Htrans; 
      false.
    -
      assert (caddr <> miner).
      {
        eapply addr_ctr_neq; eauto.
      }
      false. 
    -
      assert (Hgtn: (0 >? env_account_balances s adm) = false).
      {
        eapply (account_balance_nonnegative s adm) in Hrc_s.
        lia.        
      }
      rewrite Hgtn in Htrans.
      rewrite Hec_s in Htrans.
      unfold contract_state in Hcs_s.
      simpl in Hcs_s.
      destruct (env_contract_states s caddr) eqn: Ecs; try congruence.
      unfold weak_error_to_error_receive in Htrans.
      simpl in Htrans.
      rewrite Hcs_s in Htrans.
      rewrite deserialize_serialize in Htrans.
      unfold error_to_weak_error in Htrans.
      simpl in Htrans.
      unfold processReq in Htrans.
      simpl in Htrans.
      rewrite Hcst in Htrans.
      destruct_address_eq;try congruence; 
      simpl in Htrans; 
      false.
  Qed.      
  
  Lemma usr_deposit_preserves_d_usr_st:
    forall s (cst cst': State) n s', 
      transition_reachable miner contract caddr s0 s ->
      contract_state s caddr = Some cst ->       
      transition miner n s usr_deposit = Ok s' ->
      contract_state s' caddr = Some cst' -> 
      FMap.find d_usr (status cst) = FMap.find d_usr (status cst').
  Proof. 
    introv Htrc_s Hcst Htrans Hcst'.
    unfold transition in Htrans.
    unfold queue_isb_empty in Htrans.
    eapply transition_reachable_queue_is_empty in Htrc_s as Hqueue_s;eauto.
    rewrite Hqueue_s in Htrans.
    unfold evaluate_action in Htrans.
    rewrite get_valid_header_is_valid_header in Htrans.
    unfold usr_deposit in Htrans.
    simpl in Htrans.
    destruct_address_eq;try congruence.
    simpl in Htrans.
    assert (Hec_s:env_contracts s caddr = Some (contract:WeakContract)).
    {
      eapply transition_reachable_impl_reachable_through in Htrc_s.
      eapply reachable_through_contract_deployed in Htrc_s;eauto.
      decompose_is_init_state H_init.
      eauto.
      eauto.
    }
    eapply address_not_contract_negb in h_usr_eoa.
    rewrite h_usr_eoa in Htrans.
    destruct n. 
    simpl in Htrans; false.
    simpl in Htrans.
    assert(H_caddr_not_EOA : address_is_contract caddr = true).
    {
      eapply contract_addr_format in Hec_s;eauto.
      eapply transition_reachable_impl_reachable in Htrc_s;eauto.  
    }
    assert(Hrc_s:reachable s).
    {
      eapply transition_reachable_impl_reachable in Htrc_s;eauto.
    }
    unfold send_or_call in Htrans.
    simpl in Htrans.
    destruct_address_eq;try congruence.
    
    -
      assert (Hgtn: (1 >? miner_reward + env_account_balances s h_usr)%Z 
                    = false).
      {
        unfold miner_reward.
        eapply (account_balance_nonnegative s h_usr) in Hrc_s.
        lia.        
      }
      rewrite Hgtn in Htrans.
      rewrite Hec_s in Htrans.
      unfold contract_state in Hcst.
      simpl in Hcst.
      destruct (env_contract_states s caddr) eqn: Ecs; try congruence.
      unfold weak_error_to_error_receive in Htrans.
      simpl in Htrans.
      rewrite Hcst in Htrans.
      simpl in Htrans.

      destruct n.
      {
        simpl in Htrans.
        inverts Htrans.
        simpl in Hcst'.
        unfold contract_state in Hcst'.
        simpl in Hcst'.
        rewrite address_eq_refl in Hcst'.
        rewrite deserialize_serialize in Hcst'.
        inverts Hcst'.
        auto.
      }
      {
        simpl in Htrans.
        inverts Htrans.
        simpl in Hcst'.
        unfold contract_state in Hcst'.
        simpl in Hcst'.
        rewrite address_eq_refl in Hcst'.
        rewrite deserialize_serialize in Hcst'.
        inverts Hcst'.
        auto.
      }
    -
      assert (caddr <> miner).
      {
        eapply addr_ctr_neq; eauto.
      }
      false. 
    -
      destruct (1 >? env_account_balances s h_usr) eqn: Egt; tryfalse.
      rewrite Hec_s in Htrans.
      unfold contract_state in Hcst.
      simpl in Hcst.
      destruct (env_contract_states s caddr) eqn: Ecs; try congruence.
      unfold weak_error_to_error_receive in Htrans.
      simpl in Htrans.
      rewrite Hcst in Htrans.
      simpl in Htrans.

      destruct n.
      {
        simpl in Htrans.
        inverts Htrans.
        simpl in Hcst'.
        unfold contract_state in Hcst'.
        simpl in Hcst'.
        rewrite address_eq_refl in Hcst'.
        rewrite deserialize_serialize in Hcst'.
        inverts Hcst'.
        auto.
      }
      {
        simpl in Htrans.
        inverts Htrans.
        simpl in Hcst'.
        unfold contract_state in Hcst'.
        simpl in Hcst'.
        rewrite address_eq_refl in Hcst'.
        rewrite deserialize_serialize in Hcst'.
        inverts Hcst'.
        auto.
      }
  Qed.
  
  Lemma usr_call_req_withdrawal_preserves_d_usr_st:
    forall s (cst cst': State) n s', 
      transition_reachable miner contract caddr s0 s ->
      contract_state s caddr = Some cst ->       
      transition miner n s usr_call_reqWithdrawal = Ok s' -> 
      contract_state s' caddr = Some cst' -> 
      FMap.find d_usr (status cst) = FMap.find d_usr (status cst').
  Proof. 
    introv Htrc_s Hcst Htrans Hcst'.
    unfold transition in Htrans.
    unfold queue_isb_empty in Htrans.
    eapply transition_reachable_queue_is_empty in Htrc_s as Hqueue_s;eauto.
    rewrite Hqueue_s in Htrans.
    unfold evaluate_action in Htrans.
    rewrite get_valid_header_is_valid_header in Htrans.
    unfold usr_call_reqWithdrawal in Htrans. 
    simpl in Htrans.
    destruct_address_eq;try congruence.
    simpl in Htrans.
    assert (Hec_s:env_contracts s caddr = Some (contract:WeakContract)).
    {
      eapply transition_reachable_impl_reachable_through in Htrc_s.
      eapply reachable_through_contract_deployed in Htrc_s;eauto.
      decompose_is_init_state H_init.
      eauto.
      eauto.
    }
    eapply address_not_contract_negb in h_usr_eoa.
    rewrite h_usr_eoa in Htrans.
    destruct n. 
    simpl in Htrans; false.
    simpl in Htrans.
    assert(H_caddr_not_EOA : address_is_contract caddr = true).
    {
      eapply contract_addr_format in Hec_s;eauto.
      eapply transition_reachable_impl_reachable in Htrc_s;eauto.  
    }
    assert(Hrc_s:reachable s).
    {
      eapply transition_reachable_impl_reachable in Htrc_s;eauto.
    }
    unfold send_or_call in Htrans.
    simpl in Htrans.
    destruct_address_eq;try congruence.
    
    -
      assert (Hgtn: (0 >? miner_reward + env_account_balances s h_usr)%Z 
                    = false).
      {
        unfold miner_reward.
        eapply (account_balance_nonnegative s h_usr) in Hrc_s.
        lia.        
      }
      rewrite Hgtn in Htrans.
      rewrite Hec_s in Htrans.
      unfold contract_state in Hcst.
      simpl in Hcst.
      destruct (env_contract_states s caddr) eqn: Ecs; try congruence.
      unfold weak_error_to_error_receive in Htrans.
      simpl in Htrans.
      rewrite Hcst in Htrans.
      simpl in Htrans.
      rewrite deserialize_serialize in Htrans.
      simpl in Htrans.
      unfold reqWithdrawal in Htrans.
      simpl in Htrans.
      destruct (FMap.find h_usr (status cst)) eqn: Efd; tryfalse.
      simpl in Htrans.

      destruct n.
      {
        simpl in Htrans.
        inverts Htrans.
        simpl in Hcst'.
        unfold contract_state in Hcst'.
        simpl in Hcst'.
        rewrite address_eq_refl in Hcst'.
        rewrite deserialize_serialize in Hcst'.
        inverts Hcst'.
        simpl.
        destructs addr_neq.
        rewrite FMap.find_add_ne; eauto.
      }
      {
        simpl in Htrans.
        inverts Htrans.
        simpl in Hcst'.
        unfold contract_state in Hcst'.
        simpl in Hcst'.
        rewrite address_eq_refl in Hcst'.
        rewrite deserialize_serialize in Hcst'.
        inverts Hcst'.
        simpl.
        destructs addr_neq.
        rewrite FMap.find_add_ne; eauto.
      }
    -
      assert (caddr <> miner).
      {
        eapply addr_ctr_neq; eauto.
      }
      false. 
    -
      destruct (0 >? env_account_balances s h_usr) eqn: Egt; tryfalse.
      rewrite Hec_s in Htrans.
      unfold contract_state in Hcst.
      simpl in Hcst.
      destruct (env_contract_states s caddr) eqn: Ecs; try congruence.
      unfold weak_error_to_error_receive in Htrans.
      simpl in Htrans.
      rewrite Hcst in Htrans.
      simpl in Htrans.
      rewrite deserialize_serialize in Htrans.
      simpl in Htrans.
      unfold reqWithdrawal in Htrans.
      simpl in Htrans.
      destruct (FMap.find h_usr (status cst)) eqn: Efd; tryfalse.
      simpl in Htrans.

      destruct n.
      {
        simpl in Htrans.
        inverts Htrans.
        simpl in Hcst'.
        unfold contract_state in Hcst'.
        simpl in Hcst'.
        rewrite address_eq_refl in Hcst'.
        rewrite deserialize_serialize in Hcst'.
        inverts Hcst'.
        simpl.
        destructs addr_neq.
        rewrite FMap.find_add_ne; eauto.
      }
      {
        simpl in Htrans.
        inverts Htrans.
        simpl in Hcst'.
        unfold contract_state in Hcst'.
        simpl in Hcst'.
        rewrite address_eq_refl in Hcst'.
        rewrite deserialize_serialize in Hcst'.
        inverts Hcst'.
        simpl.
        destructs addr_neq.
        rewrite FMap.find_add_ne; eauto.
      }      
  Qed.
          
  Lemma fm_not_liquidable:
    forall s tr',
      UserLiquidatesNSteps miner [h_usr; adm] honest_strat [d_usr] attacker_strat caddr s0 s tr' ->
      transition_reachable miner contract caddr s0 s ->
      forall cst,
        funds s caddr > 0 ->
        contract_state s caddr = Some cst ->
        FMap.find h_usr cst.(status) = None ->
        FMap.find d_usr cst.(status) = None ->
        False. 
  Proof.
    lets H__: env_mut miner [h_usr; adm] honest_strat.
    lets H_: H__ [d_usr] attacker_strat caddr s0. clear H__.
    lets H__: H_
                (fun s tr (_: envProgress_Mutual miner [h_usr; adm] honest_strat [d_usr] attacker_strat
                                caddr s0 s tr) => 
                   transition_reachable miner contract caddr s0 s ->
                   forall cst,
                     funds s caddr > 0 ->
                     contract_state s caddr = Some cst ->
                     (FMap.find h_usr cst.(status) = None \/ FMap.find h_usr cst.(status) = Some status_requested) ->
                     FMap.find d_usr cst.(status) = None -> 
                     False).
    clear H_.
    lets H_: H__
               (fun s tr (_: UserLiquidatesNSteps miner [h_usr; adm] honest_strat [d_usr] attacker_strat
                               caddr s0 s tr) =>
                  transition_reachable miner contract caddr s0 s ->
                  forall cst,
                    funds s caddr > 0 ->
                    contract_state s caddr = Some cst ->
                    FMap.find h_usr cst.(status) = None ->
                    FMap.find d_usr cst.(status) = None -> 
                    False).
    clear H__.
    eapply H_; eauto; clear H_.
    - intros. lia.
    - introv Hfpos Hliq Hf Htc.
      introv Hpos Hcst Hor Hd.
      destruct Hor as [Hnone | Hreq].
      + assert (multiStratDrive miner [d_usr] attacker_strat s0 s tr s tr 0) by constructors.
        lets H__: Hf H Htc.
        eapply H__; eauto.
      + lets H_: md_none Hpos Hcst Hreq Htc.
        protect addr_neq.
        destruct_and_split.
        eapply Hf; eauto.
        rewrite H3. auto.
        rewrite H3. auto.
    - intros. lia.
    - introv Hsd Hep Hf Htr.
      introv Hpos Hcst Hnone Hd.
      protect addr_neq.
      assert (Hcst_ := Hcst).
      inverts Hsd.
      destruct H as (n & Htrans & Hin & Htr').
      unfold honest_strat in Hin.
      unfold get_contract_state in Hin.
      unfold contract_state in Hcst.
      destruct (env_contract_states s caddr) eqn: E.
      simpl in Hcst.
      rewrite Hcst in Hin.
      inverts Hin.
      {
        lets H__: user_deposit_post Hpos Hcst_ Hnone Htr Htrans.
        destruct_and_split.
        eapply Hf; eauto.
        eapply transition_reachable_transition_transition_reachable; eauto.       
        lets H__: usr_deposit_preserves_d_usr_st Htr Hcst_ Htrans H0.
        congruence.
      }
      {
        inverts H.
        {
          lets H__: user_req_withdrawal_post Hpos Hcst_ Hnone Htr Htrans.
          destruct_and_split.
          eapply Hf; eauto.
          eapply transition_reachable_transition_transition_reachable; eauto.
          lets H_: usr_call_req_withdrawal_preserves_d_usr_st Htr Hcst_ Htrans H0.
          congruence.
        }        
        {
          inverts H0.
          {
            eapply user_withdraw_post; eauto.
          }
          {
            inverts H.
            eapply adm_process_req_post with (usr:=h_usr); eauto.
            inverts H0.
            eapply adm_process_req_post with (usr:=d_usr); eauto.
            inverts H.
          }
        }
      }
      inverts Hin.
  Qed. 
  
  Require Import Coq.Logic.Classical_Prop.
  Require Import Coq.Logic.Classical_Pred_Type.

  (* strategy-aware liquidity is not satisfied *)  
  Theorem fm_unsat_strat_liquidity:
    ~strat_liquidity miner [h_usr; adm] honest_strat [d_usr] attacker_strat contract caddr s0.
  Proof.
    unfold strat_liquidity.
    apply impl_lem; auto.
    split; auto.    
    pose proof exe_pos_funds.
    protect addr_neq.
    destruct_and_split.
    repeat (apply ex_not_not_all; eexists).
    eauto.
    introv Hliqd.
    eapply fm_not_liquidable; eauto.
    eapply transition_reachable_interleavedExecution_transition_reachable; eauto.
    eapply transition_reachable_init_state; eauto.
    rewrite H1; auto.
    rewrite H1; auto.
  Qed. 
    
End Liquidity.
