
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
  | Withdraw. 

  Global Instance Msg_serializable : Serializable Msg :=
    Derive Serializable Msg_rect<ReqWithdrawal, ProcessReq, Withdraw>. 
  
  Record State :=
    build_state {
        status : (FMap Address nat);
        admin : Address 
      }.

  Definition status_requested := 1%nat.
  Definition status_approved := 2%nat. 

  Record Setup :=
    build_setup {
        setup_status : FMap Address nat; 
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
  
  (* lemmas for basic and strategy-aware liquidity *)
  
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

  Lemma reachable_ex_cstate :
    forall bstate,
      reachable bstate ->
      env_contracts bstate caddr = Some (contract : WeakContract) -> 
      exists cstate,
        contract_state bstate caddr = Some cstate /\ 
          (FMap.find h_usr cstate.(status) = None \/
             FMap.find h_usr cstate.(status) = Some status_requested \/
             FMap.find h_usr cstate.(status) = Some status_approved) /\
          cstate.(admin) = adm. 
  Proof.
    intros.
    contract_induction; intros; auto; cbn in *;try congruence;try lia;eauto.
    - unfolds in init_some.
      inverts init_some.
      split.
      + left. simpl. auto.
      + simpl; auto. 
    - unfolds in receive_some.
      destruct_message.
      + simpl_eval; eauto.
        destruct_and_split; simpl; auto.
        lets H_: address_eqb_spec (ctx_origin ctx) h_usr.
        inverts H_.
        rewrite H2. auto.
        rewrite FMap.find_add_ne; eauto.
      + simpl_eval; eauto.
        destruct (FMap.find a (status prev_state)) eqn: E; tryfalse. 
        simpl_eval; eauto.
        {
          simpl.
          lets H_: address_eqb_spec a h_usr.
          inverts H_.
          rewrite FMap.find_add; eauto.
          destruct IH. split; auto.
          rewrite FMap.find_add_ne; eauto.
        }
        {
          simpl.
          lets H_: address_eqb_spec a h_usr.
          inverts H_.
          rewrite FMap.find_remove.
          destruct IH.
          split; auto.
          rewrite FMap.find_remove_ne; eauto.
        }
      + simpl_eval; eauto.
        destruct (FMap.find (ctx_origin ctx) (status prev_state)) eqn: E; tryfalse.
        simpl_eval; eauto.
        simpl.
        lets H_: address_eqb_spec (ctx_origin ctx) h_usr.
        inverts H_.
        {
          rewrite H0.
          rewrite FMap.find_remove.
          destruct IH.
          split; eauto.
        }
        {
          rewrite FMap.find_remove_ne; eauto.
        }
      + inverts receive_some. eauto.
    - unfolds in receive_some.
      destruct_message.
      + simpl_eval; eauto.
        destruct_and_split; simpl; auto.
        lets H_: address_eqb_spec (ctx_origin ctx) h_usr.
        inverts H_.
        rewrite H2. auto.
        rewrite FMap.find_add_ne; eauto.
      + simpl_eval; eauto.
        destruct (FMap.find a (status prev_state)) eqn: E; tryfalse. 
        simpl_eval; eauto.
        {
          simpl.
          lets H_: address_eqb_spec a h_usr.
          inverts H_.
          rewrite FMap.find_add; eauto.
          destruct IH. split; auto.
          rewrite FMap.find_add_ne; eauto.
        }
        {
          simpl.
          lets H_: address_eqb_spec a h_usr.
          inverts H_.
          rewrite FMap.find_remove.
          destruct IH.
          split; auto.
          rewrite FMap.find_remove_ne; eauto.
        }
      + simpl_eval; eauto.
        destruct (FMap.find (ctx_origin ctx) (status prev_state)) eqn: E; tryfalse.
        simpl_eval; eauto.
        simpl.
        lets H_: address_eqb_spec (ctx_origin ctx) h_usr.
        inverts H_.
        {
          rewrite H0.
          rewrite FMap.find_remove.
          destruct IH.
          split; eauto.
        }
        {
          rewrite FMap.find_remove_ne; eauto.
        }
      + inverts receive_some. eauto.
    -
      solve_facts.
  Qed.    

  Hypothesis h_usr_eoa : address_not_contract h_usr = true.
  Hypothesis d_usr_eoa : address_not_contract d_usr = true.
  Hypothesis adm_eoa : address_not_contract adm = true.

  Definition usr_deposit: Action :=
    build_transfer h_usr caddr 1.
    
  Definition usr_call_reqWithdrawal: Action :=
    build_call h_usr caddr 0 ReqWithdrawal.

  Definition usr_call_withdraw: Action :=
    build_call h_usr caddr 0 Withdraw.

  Definition adm_call_processReq (a: Address): Action :=
    build_call adm caddr 0 (ProcessReq a true).

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
    lets H__: reachable_ex_cstate Hrcs.
    specializes H__; eauto.
    eapply trans_rc_env_contracts; eauto.
    destruct H__ as (cs & Hcs & Hst & Hadm).
    destruct Hst as [Hnone | [Hreq | Hapr]].
    - lets H__: usr_req_transition_correct Hcs Hnone Htrc.
      destruct H__ as (s' & Htrs' & Hfds' & Hex).
      destruct Hex as (cs' & Hcs' & Hfm' & Had').
      assert (Hadm': admin cs' = adm) by congruence.
      assert (Htrc': transition_reachable miner contract caddr s0 s').
      {
        specialize (transition_reachable_transition_transition_reachable
                      miner 5 s0 s s' usr_call_reqWithdrawal contract caddr).
        introv Htrc'.
        specializes Htrc'; eauto.
      }
      lets H__: adm_apr_transition_correct Hcs' Hfm' Hadm' Htrc'.
      destruct H__ as (s'0 & Hs'0 & Hfd'0 & Hex).
      destruct Hex as (cs'0 & Hcs'0 & Hfm'0 & Had'0).
      assert (Hadm'0: admin cs'0 = adm) by congruence.
      assert (Htrc'0: transition_reachable miner contract caddr s0 s'0).
      {
        specialize (transition_reachable_transition_transition_reachable
                      miner 5 s0 s' s'0 (adm_call_processReq h_usr) contract caddr).
        introv Htrc'0.
        specializes Htrc'0; eauto.
      }
      lets H__: usr_wth_transition_correct Hcs'0 Hfm'0 Htrc'0.
      destruct H__ as (s'_ & Hs'_ & Hfd'_ & Hex).
      destruct Hex as (cs_ & Hcs_ & Hfm_).
      exists s'_.
      split; eauto.
      constructors.
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
    - lets H__: adm_apr_transition_correct Hcs Hreq Hadm Htrc.
      destruct H__ as (s' & Hs' & Hfd' & Hex).
      destruct Hex as (cs' & Hcs' & Hfm' & Had').
      assert (Hadm'0: admin cs' = adm) by congruence.
      assert (Htrc'0: transition_reachable miner contract caddr s0 s').
      {
        specialize (transition_reachable_transition_transition_reachable
                      miner 5 s0 s s' (adm_call_processReq h_usr) contract caddr).
        introv Htrc'.
        specializes Htrc'; eauto.
      }
      lets H__: usr_wth_transition_correct Hcs' Hfm' Htrc'0.
      destruct H__ as (s'_ & Hs'_ & Hfd'_ & Hex).
      destruct Hex as (cs_ & Hcs_ & Hfm_).
      exists s'_.
      split; auto.
      constructors.
      eapply snoc; eauto.
      instantiate (1:=s').
      2: constructors; eauto.
      eapply snoc; eauto.
      instantiate (1:=s).
      2: constructors; eauto.
      constructors. 
    - lets H__: usr_wth_transition_correct Hcs Hapr Htrc.
      destruct H__ as (s'_ & Hs'_ & Hfd'_ & Hex).
      destruct Hex as (cs_ & Hcs_ & Hfm_).
      exists s'_.
      split; auto.
      constructors.
      eapply snoc; eauto.
      instantiate (1:=s).
      2: constructors; eauto.
      constructors. 
  Qed.

  (* lemmas for strategy-aware liquidity *)
  
  Lemma exe_act_preserves_status:
    forall (s s':ChainState) cstate (a: Action) 
    (Hec_s: env_contracts s caddr = Some (contract:WeakContract)),
      contract_state s caddr = Some cstate ->
      (* transition_reachable miner  contract caddr s0 s -> *)
      execute_action a s.(chain_state_env) = Ok s' ->
      a.(act_origin) <> cstate.(admin) ->
      a.(act_origin) <> h_usr ->
      a.(act_from) <> h_usr ->
      env_contracts s' caddr = env_contracts s caddr /\
        env_contracts s' h_usr = env_contracts s h_usr /\ 
      exists cs',
        contract_state s' caddr = Some cs' /\
          FMap.find h_usr cs'.(status) = FMap.find h_usr cstate.(status) /\
          cs'.(admin) = cstate.(admin).
  Proof.
    do 5 intro.
    introv Hcs (* Htrc *) Hexe Hnoa Hno Hne.
    (* assert (Hec_s: env_contracts s caddr = Some (contract:WeakContract)). *)
    (* { *)
    (*   eapply trans_rc_env_contracts; eauto. *)
    (* } *)
    unfolds in Hexe.
    destruct a eqn: Ea.
    destruct act_body eqn: Eb.
    simpl in Hne.
    - unfolds in Hexe.
      destruct (amount <? 0) eqn: Eamt; tryfalse.
      destruct (amount >? env_account_balances s act_from) eqn: Eamt'; tryfalse.
      destruct (env_contracts s to) eqn: Eec; tryfalse.
      +
        destruct (env_contract_states s to) eqn: Ees; tryfalse.
        simpl in Hexe.
        destruct_address_eq;try congruence.
        destruct (wc_receive w s
                {|
                  ctx_origin := act_origin;
                  ctx_from := act_from;
                  ctx_contract_address := to;
                  ctx_contract_balance := - amount + (amount + env_account_balances s to);
                  ctx_amount := amount
                |} s1 None) eqn: Ewc; tryfalse. 
        simpl in Hexe.
        subst act_from.
        destruct t.
        inverts Hexe.
        simpl.
        unfold contract_state.
        simpl. 
        destruct_address_eq;try congruence.
        *
          unfolds in Ewc.
          destruct w.
          subst to.
          rewrite Hec_s in Eec.
          inverts Eec.
          destruct (result_of_option (deserialize s1) deser_error) eqn: Ero; tryfalse.
          inverts Ewc.
          rewrite deserialize_serialize.
          split; auto.
          split; auto.
          eexists.
          unfolds in Hcs.
          simpl in Hcs.
          destruct (env_contract_states s caddr) eqn: Eec; tryfalse.
          inverts Ees.
          rewrite Hcs in Ero.
          simpl in Ero.
          inverts Ero.
          split; auto.
        *
          unfolds in Hcs.
          simpl in Hcs.
          destruct (env_contract_states s caddr) eqn: Eecs; tryfalse.
          split; auto.
          split; auto.
          eexists.
          split; eauto.
        *
          destruct (wc_receive w s
                {|
                  ctx_origin := act_origin;
                  ctx_from := act_from;
                  ctx_contract_address := to;
                  ctx_contract_balance := amount + env_account_balances s to;
                  ctx_amount := amount
                |} s1 None) eqn: Ewc; tryfalse.
          simpl in Hexe.
          destruct t.
          inverts Hexe.
          simpl.
          unfold contract_state.
          simpl.
          destruct_address_eq;try congruence.
          **
            unfold wc_receive in Ewc.
            destruct w.
            subst to. 
            rewrite Hec_s in Eec.
            inverts Eec.
            destruct (result_of_option (deserialize s1) deser_error) eqn: Ero; tryfalse.
            inverts Ewc.
            rewrite deserialize_serialize.
            split; auto.
            split; auto.
            eexists.
            split; eauto.
            unfolds in Hcs.
            simpl in Hcs.
            destruct (env_contract_states s caddr) eqn: Eec; tryfalse.
            inverts Ees.
            rewrite Hcs in Ero.
            simpl in Ero.
            inverts Ero.
            split; auto.
          **
            unfolds in Hcs.
            simpl in Hcs.
            destruct (env_contract_states s caddr) eqn: Eecs; tryfalse.
            rewrite Hcs.
            split; auto.
            split; auto.
            eexists.
            split; eauto.
      +
        destruct (address_is_contract to) eqn: Eic; tryfalse.
        inverts Hexe.
        simpl.
        unfold contract_state.
        simpl.
        unfolds in Hcs.
        simpl in Hcs.
        destruct (env_contract_states s caddr) eqn: Ee; tryfalse.
        rewrite Hcs.
        split; auto.
        split; auto.
        eexists.
        splits; eauto.
    -
      simpl in Hne.
      simpl in Hno.
      simpl in Hnoa.
      unfolds in Hexe.
      destruct (amount <? 0) eqn: Eamt; tryfalse.
      destruct (amount >? env_account_balances s act_from) eqn: Eamt'; tryfalse.
      destruct (env_contracts s to) eqn: Eec; tryfalse.
      +
        destruct (env_contract_states s to) eqn: Eecs; tryfalse.
        destruct (wc_receive w (transfer_balance act_from to amount s)
                {|
                  ctx_origin := act_origin;
                  ctx_from := act_from;
                  ctx_contract_address := to;
                  ctx_contract_balance :=
                    env_account_balances (transfer_balance act_from to amount s) to;
                  ctx_amount := amount
                |} s1 (Some msg)) eqn: Erc; tryfalse.
        simpl in Hexe.
        destruct t.
        inverts Hexe.
        simpl in Erc.
        unfold wc_receive in Erc.
        destruct w.
        unfold contract_state.
        simpl.
        destruct (caddr =? to)%address eqn: Ecte.
        *
          assert (caddr = to).
          { lets H_: address_eqb_spec caddr to. inverts H_; tryfalse; auto. }
          subst to.
          rewrite Hec_s in Eec.
          inverts Eec.
          simpl in Erc.
          destruct (result_of_option (deserialize s1) deser_error) eqn: Eds1; tryfalse.
          destruct (result_of_option (deserialize msg) deser_error) eqn: Em; tryfalse.
          destruct t0; tryfalse.
          **
            unfold reqWithdrawal in Erc.
            simpl in Erc.
            destruct (FMap.find act_origin (status t)) eqn: Efm; tryfalse.
            simpl in Erc.
            inverts Erc.
            rewrite deserialize_serialize.
            split; auto.
            split; auto.
            eexists.
            split; eauto.
            simpl.
            unfolds in Hcs.
            simpl in Hcs.
            destruct (env_contract_states s caddr) eqn: E_; tryfalse. 
            inverts Eecs.
            rewrite Hcs in Eds1.
            simpl in Eds1.
            inverts Eds1.
            rewrite FMap.find_add_ne; eauto.
          **
            unfold processReq in Erc.
            simpl in Erc.
            destruct (FMap.find a0 (status t)) eqn: Efm; tryfalse.
            destruct ((act_origin =? admin t)%address) eqn: Eadm.
            2: {
              rewrite andb_false_l in Erc.
              simpl in Erc.
              false.
            }
            unfolds in Hcs.
            simpl in Hcs.
            destruct (env_contract_states s caddr) eqn: E_; tryfalse. 
            inverts Eecs.
            rewrite Hcs in Eds1.
            simpl in Eds1.
            inverts Eds1.
            apply address_eq_ne in Hnoa.
            false. 
          **
            unfold withdraw in Erc.
            simpl in Erc.
            unfolds in Hcs.
            simpl in Hcs.
            destruct (env_contract_states s caddr) eqn: E_; tryfalse.
            inverts Eecs.
            rewrite Hcs in Eds1.
            simpl in Eds1.
            inverts Eds1.
            destruct (FMap.find act_origin (status t)) eqn: Efd; tryfalse. 
            destruct ((n =? status_approved)%nat) eqn: Eeq; tryfalse. 
            simpl in Erc.
            inverts Erc.
            rewrite deserialize_serialize.
            split; auto.
            split; auto.
            eexists.
            split; eauto.
            simpl.
            rewrite FMap.find_remove_ne; eauto.
        *
          unfolds in Hcs.
          simpl in Hcs.
          destruct (env_contract_states s caddr) eqn: Ee; tryfalse. 
          rewrite Hcs.
          split; auto.
          split; auto.
          eexists.
          splits; eauto.
      +
        destruct (address_is_contract to); tryfalse.
    -
      simpl in Hnoa, Hno, Hne.
      unfolds in Hexe.
      destruct (amount <? 0) eqn: Eamt; tryfalse.
      destruct (amount >? env_account_balances s act_from) eqn: Eamt'; tryfalse.
      destruct (get_new_contract_addr s) eqn: En; tryfalse. 
      destruct (correct_contract_addr s a0) eqn: Ecca; tryfalse.       
      destruct (wc_init c (transfer_balance act_from a0 amount s)
             {|
               ctx_origin := act_origin;
               ctx_from := act_from;
               ctx_contract_address := a0;
               ctx_contract_balance := amount;
               ctx_amount := amount
             |} setup) eqn: Ewi; tryfalse. 
      inverts Hexe.
      simpl.
      unfold contract_state.
      simpl.
      lets H__: address_eqb_spec caddr a0.
      inverts H__.
      + 
        unfolds in Ecca.
        destruct (isNone (env_contracts s a0)) eqn: Enn.
        unfolds in Enn.
        destruct (env_contracts s a0) eqn: Eea; tryfalse.
        rewrite andb_false_r in Ecca.
        false. 
      +
        unfolds in Hcs.
        simpl in Hcs.
        destruct (env_contract_states s caddr) eqn: E; tryfalse. 
        rewrite Hcs.
        split; auto.
        unfolds in Ecca.
        destruct (address_is_contract a0) eqn: Ea0.
        2: { simpl in Ecca. false. }
        assert (Hneq: a0 <> h_usr).
        {
          eapply addr_ctr_neq; eauto.
        }
        apply address_eq_ne in Hneq.
        rewrite address_eq_sym in Hneq.
        rewrite Hneq.
        split; auto.
        eexists.
        split; eauto.
  Qed.         

  Lemma in_act_org_frm:
    forall l (a: Action) orig fr,  
      In a (map (build_act orig fr) l) ->
      a.(act_origin) = orig /\ a.(act_from) = fr.
  Proof.
    induction l.
    -
      intros.
      simpl in H.
      false. 
    -
      introv Hin.
      simpl in Hin.
      destruct Hin as [Hhd | Htl].
      + subst a0.
        simpl.
        auto.
      + eapply IHl; eauto.
  Qed.

  Lemma exe_acts_preserves_status_d_usr:
    forall n (s s_ s': ChainState) cs cs_, 
      contract_state s caddr = Some cs ->    
      transition_reachable miner contract caddr s0 s ->
      env_contracts s_ caddr = env_contracts s caddr ->
      env_contracts s_ h_usr = env_contracts s h_usr -> 
      contract_state s_ caddr = Some cs_ ->
      FMap.find h_usr cs_.(status) = FMap.find h_usr cs.(status) -> 
      cs_.(admin) = cs.(admin) ->
      execute_actions n s_ true = Ok s' -> 
      (forall a, List.In a s_.(chain_state_queue) ->
                 a.(act_origin) <> cs.(admin) /\ a.(act_origin) <> h_usr /\ a.(act_from) <> h_usr) -> 
      exists cs',
        contract_state s' caddr = Some cs' /\
          FMap.find h_usr cs'.(status) = FMap.find h_usr cs.(status) /\ 
          cs'.(admin) = cs.(admin). 
  Proof.
    induction n.
    -
      intros. simpl in H6.
      destruct (chain_state_queue s_) eqn: E; tryfalse.
      inverts H6.
      simpl.
      eexists.
      splits; eauto.
    -
      introv Hcs Htrc Hec Hech Hcs_ Hfmeq Hadeq Hexe Hane.
      assert (Hane_ := Hane).
      assert (Hrcs: reachable s).
      {
        specialize (transition_reachable_impl_reachable miner contract caddr s0 s H_init Htrc).
        auto.
      }
      simpl in Hexe.
      destruct (chain_state_queue s_) eqn: E.
      + 
        inverts Hexe.
        simpl.
        eexists.
        splits; eauto.
      +
        assert (Hec_s: env_contracts s caddr = Some (contract:WeakContract)).
        {
          eapply trans_rc_env_contracts; eauto.
        }
        destruct (execute_action a s_) eqn: Ee; tryfalse.
        assert (Hec_: env_contracts s_ caddr = Some (contract:WeakContract)).
        {
          congruence.
        }
        lets H__: exe_act_preserves_status Hec_ Hcs_ Ee.
        specialize (Hane a).
        specializes Hane.
        simpl. eauto.
        destruct Hane as (Hoa_ne & Hoh_ne & Hfh_ne).
        rewrite <- Hadeq in Hoa_ne.
        specializes H__; eauto.
        destruct H__ as (Hecc & Hech_ & Hex).
        destruct Hex as (cs' & Hcs' & Hfeq' & Hadeq').
        remember {| chain_state_env := t; chain_state_queue := chain_state_queue t ++ l |} as ss.
        assert (Heceq: env_contracts ss caddr = env_contracts s caddr).
        {
          rewrite Heqss. simpl. congruence.
        }
        assert (Hecheq: env_contracts ss h_usr = env_contracts s h_usr).
        {
          rewrite Heqss. simpl. congruence.
        }
        assert (Hcsca: contract_state ss caddr = Some cs').
        {
          rewrite Heqss. simpl. auto.
        }
        assert (Hfeq_: FMap.find h_usr (status cs') = FMap.find h_usr (status cs)).
        {
          congruence.
        }
        assert (Hadeq_: admin cs' = admin cs).
        {
          congruence.
        }
        lets IH_: IHn Hcs Htrc Heceq Hecheq Hcsca.
        lets IH__: IH_ Hfeq_ Hadeq_ Hexe.
        clear IH_.
        assert (Ha: forall a : Action,
                   In a (chain_state_queue ss) ->
                   act_origin a <> admin cs /\ act_origin a <> h_usr /\ act_from a <> h_usr).
        {
          introv Hin.
          rewrite Heqss in Hin.
          simpl in Hin.
          apply in_app_or in Hin.
          destruct Hin as [Hinqt | Hinl].
          - unfolds in Ee.
            destruct a eqn: Ea.
            destruct act_body eqn: Eb; simpl in *.
            + unfolds in Ee.
              destruct (amount <? 0); tryfalse.
              destruct (amount >? env_account_balances s_ act_from); tryfalse.
              destruct (env_contracts s_ to) eqn: Eto; tryfalse.
              *
                destruct (env_contract_states s_ to); tryfalse.
                match goal with 
                  H: match ?x with _ => _ end = _ |- _ => destruct x; tryfalse
                end.
                destruct t0.
                inverts Ee.
                simpl in Hinqt.
                lets H_: in_act_org_frm Hinqt.
                destruct H_ as (Ho_ & Hf_).
                rewrite Ho_.
                rewrite Hf_.
                splits; try congruence; eauto.
                assert (Hnone: env_contracts s_ h_usr = None).
                {
                  rewrite Hech.
                  eapply addr_not_ctr_none; eauto.
                }
                revert Eto.
                introv Heto.
                introv Heq.
                congruence.
              *
                destruct (address_is_contract to); tryfalse.
                inverts Ee.
                simpl in Hinqt.
                false.
            +
              unfolds in Ee.
              destruct (amount <? 0); tryfalse.
              destruct (amount >? env_account_balances s_ act_from); tryfalse.
              destruct (env_contracts s_ to) eqn: Eto; tryfalse.
              *
                destruct (env_contract_states s_ to); tryfalse.
                match goal with 
                  H: match ?x with _ => _ end = _ |- _ => destruct x; tryfalse
                end.
                destruct t0.
                inverts Ee.
                simpl in Hinqt.
                lets H_: in_act_org_frm Hinqt.
                destruct H_ as (Ho_ & Hf_).
                rewrite Ho_.
                rewrite Hf_.
                splits; try congruence; eauto.
                assert (Hnone: env_contracts s_ h_usr = None).
                {
                  rewrite Hech.
                  eapply addr_not_ctr_none; eauto.
                }
                revert Eto.
                introv Heto.
                introv Heq.
                congruence.
              *
                destruct (address_is_contract to); tryfalse.
            +
              unfolds in Ee.
              destruct (amount <? 0); tryfalse.
              destruct (amount >? env_account_balances s_ act_from); tryfalse.
              destruct (get_new_contract_addr s_) eqn: Enc; tryfalse.
              destruct (correct_contract_addr s_ a1) eqn: Ecca; tryfalse.
              match goal with 
                H: match ?x with _ => _ end = _ |- _ => destruct x; tryfalse
              end.
              inverts Ee.
              simpl in Hinqt.
              false. 
          - assert (Hin': List.In a0 (a :: l)).
            {
              simpl. right; auto.
            }
            specialize (Hane_ _ Hin').
            auto.
        }
        specialize (IH__ Ha).
        destruct IH__ as (cs__ & Hcs__ & Hfdeq__ & Hadeq__).
        eexists.
        split; eauto.
  Qed.
  
  Hypothesis addr_neq : adm <> h_usr /\ adm <> d_usr /\ h_usr <> d_usr.
  
  Lemma transition_preserves_status_d_usr:
    forall (s s':ChainState) cstate (a: Action) n, 
      contract_state s caddr = Some cstate ->
      transition_reachable miner  contract caddr s0 s ->
      transition miner n s a = Ok s' ->
      a.(act_origin) = d_usr -> 
      exists cs',
        contract_state s' caddr = Some cs' /\
          FMap.find h_usr cs'.(status) = FMap.find h_usr cstate.(status) /\ 
          cs'.(admin) = cstate.(admin). 
  Proof.
    introv Hcs Htrc Htrans Horig.
    unfolds in Htrans.
    destruct (queue_isb_empty s) eqn: Eq; tryfalse.
    destruct (evaluate_action n s (get_valid_header miner s) [a]) eqn: Ee; tryfalse.
    unfolds in Ee.
    destruct (validate_header (get_valid_header miner s) s) eqn: Evh; tryfalse. 
    destruct (find_origin_neq_from [a]) eqn: Efo; tryfalse.
    destruct (find_invalid_root_action [a]) eqn: Eivr; tryfalse.
    inverts Htrans.

    lets H__: exe_acts_preserves_status_d_usr Ee; eauto.
    eapply H__; eauto.
    introv Hin.
    simpl in Hin.
    inverts Hin; subst; tryfalse.
    rewrite Horig.
    assert (Hrc: reachable s).
    {
      specialize (transition_reachable_impl_reachable miner contract caddr s0 s H_init Htrc).
      auto.
    }
    lets Hctr: trans_rc_env_contracts Htrc.
    lets H_: reachable_ex_cstate Hrc Hctr.
    destructs addr_neq.
    protect addr_neq.
    destruct_and_split.
    introv Hf; false.
    introv Hf; false.
    unfolds in Efo.
    simpl in Efo.
    destruct (address_neqb (act_origin a0) (act_from a0)) eqn: E; tryfalse. 
    unfolds in E.
    lets H_: address_eqb_spec (act_origin a0) (act_from a0).    
    inverts H_; tryfalse; eauto.
    introv Hf; congruence.
    rewrite <- H5 in E.
    simpl in E.
    false. 
  Qed. 

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

  Lemma usr_req_strat_drive:  
    forall (s:ChainState) (cstate: State) (tr: TransitionTrace miner s0 s),
      contract_state s caddr = Some cstate ->
      FMap.find h_usr cstate.(status) = None -> 
      transition_reachable miner contract caddr s0 s ->
      exists s' tr', 
        stratDrive miner [h_usr; adm] honest_strat s0 s tr s' tr' /\ 
          (* transition miner 5 s usr_call_reqWithdrawal = Ok s' /\  *)
          funds s' caddr = funds s caddr /\  
          exists cs,
            contract_state s' caddr = Some cs /\
              FMap.find h_usr cs.(status) = Some status_requested /\
              cs.(admin) = cstate.(admin).
  Proof.
    introv Hcs Hnone Htrc.
    lets H__: usr_req_transition_correct Hcs Hnone Htrc.
    protect addr_neq.
    destruct_and_split.
    exists x. 
    eexists.
    split.
    exists usr_call_reqWithdrawal. eexists. exists H.
    split.
    unfold honest_strat.
    unfolds in Hcs. simpl in Hcs.
    unfold get_contract_state.
    destruct (env_contract_states s caddr); tryfalse.
    rewrite Hcs.
    simpl; auto.
    eauto.
    split; auto.
    eexists. splits; eauto.
  Qed.

  Lemma adm_apr_strat_drive:  
    forall (s:ChainState) (cstate: State) (tr: TransitionTrace miner s0 s),
      contract_state s caddr = Some cstate ->
      FMap.find h_usr cstate.(status) = Some status_requested ->
      cstate.(admin) = adm -> 
      transition_reachable miner contract caddr s0 s ->
      exists s' tr', 
        stratDrive miner [h_usr; adm] honest_strat s0 s tr s' tr' /\ 
          funds s' caddr = funds s caddr /\  
          exists cs,
            contract_state s' caddr = Some cs /\
              FMap.find h_usr cs.(status) = Some status_approved /\  
              cs.(admin) = cstate.(admin).
  Proof.
    introv Hcs Hreq Hadm Htrc.
    lets H__: adm_apr_transition_correct Hcs Hreq Hadm Htrc.
    protect addr_neq.
    destruct_and_split.
    exists x. 
    eexists.
    split.
    exists (adm_call_processReq h_usr). eexists. exists H.
    split.
    unfold honest_strat.
    unfolds in Hcs. simpl in Hcs.
    unfold get_contract_state.
    destruct (env_contract_states s caddr); tryfalse.
    rewrite Hcs.
    simpl; auto.
    eauto.
    split; auto.
    eexists. splits; eauto.
  Qed.

  Lemma usr_wth_strat_drive:  
    forall (s:ChainState) (cstate: State) (tr: TransitionTrace miner s0 s),
      contract_state s caddr = Some cstate ->
      FMap.find h_usr cstate.(status) = Some status_approved ->
      transition_reachable miner contract caddr s0 s ->
      exists s' tr', 
        stratDrive miner [h_usr; adm] honest_strat s0 s tr s' tr' /\ 
          funds s' caddr = 0 /\  
          exists cs,
            contract_state s' caddr = Some cs /\
              FMap.find h_usr cs.(status) = None. 
  Proof.
    introv Hcs Hapr Htrc.
    lets H__: usr_wth_transition_correct Hcs Hapr Htrc.
    protect addr_neq.
    destruct_and_split.
    exists x. 
    eexists.
    split.
    exists usr_call_withdraw. eexists. exists H.
    split.
    unfold honest_strat.
    unfolds in Hcs. simpl in Hcs.
    unfold get_contract_state.
    destruct (env_contract_states s caddr); tryfalse.
    rewrite Hcs.
    simpl; auto.
    eauto.
    split; auto.
    eexists. splits; eauto.
  Qed.

  Definition well_strat (addrs: list Address) (stt: strat miner addrs) :=
    forall a s0 s (tr: TransitionTrace miner s0 s),  
      List.In a (stt s0 s tr) -> List.In a.(act_origin) addrs. 

  Lemma att_strat_drive_preserves_status:
    forall (s s':ChainState) cstate (att_strat: strat miner [d_usr]) tr tr', 
      contract_state s caddr = Some cstate ->
      transition_reachable miner contract caddr s0 s ->
      stratDrive miner [d_usr] att_strat s0 s tr s' tr' ->
      well_strat [d_usr] att_strat -> 
      exists cs',
        contract_state s' caddr = Some cs' /\
          FMap.find h_usr cs'.(status) = FMap.find h_usr cstate.(status) /\ 
          cs'.(admin) = cstate.(admin). 
  Proof.
    introv Hcs Htrc Hsd Hws.
    inverts Hsd.
    destruct H as (n & Htrans & Hin & Htr').
    unfolds in Hws.
    lets H__: Hws Hin.
    unfolds in H__.
    inverts H__; tryfalse.
    specialize (transition_preserves_status_d_usr s s' cstate x n Hcs Htrc Htrans).
    introv H_.
    specializes H_; eauto.
  Qed.
    
  Lemma att_multi_strat_drive_preserves_status:
    forall n (s s':ChainState) cstate (att_strat: strat miner [d_usr]) tr tr', 
      contract_state s caddr = Some cstate ->
      transition_reachable miner contract caddr s0 s ->
      multiStratDrive miner [d_usr] att_strat s0 s tr s' tr' n -> 
      well_strat [d_usr] att_strat -> 
      transition_reachable miner contract caddr s0 s' /\ 
      exists cs',
        contract_state s' caddr = Some cs' /\
          FMap.find h_usr cs'.(status) = FMap.find h_usr cstate.(status) /\ 
          cs'.(admin) = cstate.(admin). 
  Proof.
    induction n.
    -
      intros.
      inverts H1.
      split; auto.
      eexists.
      split; eauto.
      false.
      lia.
    -
      introv Hcs Htrc Hmsd Hws.
      inverts Hmsd.
      assert (count = n) by lia.
      subst.
      specialize (IHn s s'0 cstate att_strat tr tr'0 Hcs Htrc H2 Hws).
      destruct IHn as (Htrc_ & cs' & Hcs' & Hfmh & Hadm).
      specialize (transition_reachable_multiStratDrive_transition_reachable
                    miner s0 s s'0 tr att_strat [d_usr] contract caddr tr'0 n).
      introv Htrc__.
      specializes Htrc__; eauto.
      specialize (transition_reachable_stratDrive_transition_reachable
                    miner s0 s'0 tr'0 [d_usr] att_strat s' contract caddr tr').
      introv Htrc'.
      split.
      specializes Htrc'; eauto. 
      specialize (att_strat_drive_preserves_status s'0 s' cs' att_strat tr'0 tr' Hcs' Htrc_ H3 Hws).
      introv Hex.
      destruct Hex as (cs'0 & Hcs'0 & Hfh'0 & Had'0).
      eexists.
      split; eauto.
      split; congruence.
  Qed.        
          
  Lemma user_liq:
    forall s (tr: TransitionTrace miner s0 s) (att_strat: strat miner [d_usr]), 
      is_init_state contract caddr s0 -> 
      transition_reachable miner contract caddr s0 s ->
      well_strat [d_usr] att_strat -> 
      UserLiquidatesNSteps miner [h_usr; adm] honest_strat [d_usr] att_strat caddr s0 s tr.
  Proof.
    introv Hini Htrc Hws.
    assert (Hrcs: reachable s).
    {
      specialize (transition_reachable_impl_reachable miner contract caddr s0 s).
      introv H_. apply H_ in Hini; auto.
    }
    lets H__: reachable_ex_cstate Hrcs.
    specializes H__; eauto.
    eapply trans_rc_env_contracts; eauto.
    destruct H__ as (cs & Hcs & Hst & Hadm).
    destruct Hst as [Hnone | [Hreq | Hapr]].
    - lets H__: usr_req_strat_drive tr Hcs Hnone Htrc.
      destruct H__ as (s' & tr' & Hsd & Hfd & Hex).
      destruct Hex as (cs' & Hcs' & Hst' & Hadm').
      eapply ULM_Step; eauto.
      specialize (transition_reachable_stratDrive_transition_reachable
                    miner s0 s tr [h_usr; adm] honest_strat s' contract caddr tr').
      introv Htrc'.
      specializes Htrc'; eauto.
      lets Hor: Z.eqb_spec (funds s caddr) 0.
      inverts Hor.
      +
        constructors.
        congruence.
      +
        assert (Hge: funds s caddr >= 0).
        {
          eapply reachable_funds_nonnegative; eauto.
        }
        eapply EPM_Step; eauto.
        rewrite Hfd.
        lia.
        introv Hmsd.
        lets H_: att_multi_strat_drive_preserves_status Hcs' Htrc' Hmsd Hws.
        destruct H_ as (Htrc'0 & Hex').
        destruct Hex' as (cs'0 & Hcs'0 & Hfm'0 & Had'0).
        assert (Hadeq: admin cs'0 = adm) by congruence.
        assert (Hreq_: FMap.find h_usr (status cs'0) = Some status_requested) 
          by congruence.
        lets Hsd_: adm_apr_strat_drive Hcs'0 Hreq_ Hadeq Htrc'0.
        destruct Hsd_ as (s'1 & tr'1 & Hsd_ & Hfd_ & Hex).
        destruct Hex as (cs'1 & Hcs'1 & Hfm'1 & Had'1).
        eapply ULM_Step; eauto.
        specialize (transition_reachable_stratDrive_transition_reachable
                      miner s0 s'0 tr'0 [h_usr; adm] honest_strat s'1 contract caddr tr'1).
        introv Htrc'1.
        specializes Htrc'1; eauto.
        lets Hor: Z.eqb_spec (funds s'1 caddr) 0.
        inverts Hor.
        *
          constructors.
          congruence.
        *
          assert (Hrc_: reachable s'1).
          {
            specialize (transition_reachable_impl_reachable miner contract caddr s0 s'1).
            introv H__. specializes H__; eauto.
          }
          assert (Hge'1: funds s'1 caddr >= 0).
          {
            eapply reachable_funds_nonnegative; eauto.
          }
          eapply EPM_Step; eauto.
          lia.
          introv Hmsd'1.
          lets H__: att_multi_strat_drive_preserves_status Hcs'1 Htrc'1 Hmsd'1 Hws.
          destruct H__ as (Htrc'2 & Hex).
          destruct Hex as (cs'2 & Hcs'2 & Hfm'2 & Had'2).
          assert (Hadeq'2: admin cs'2 = adm) by congruence.
          assert (Hapr'2: FMap.find h_usr (status cs'2) = Some status_approved) 
            by congruence.
          lets H'': usr_wth_strat_drive Hcs'2 Hapr'2 Htrc'2.
          protect addr_neq.
          destruct_and_split.
          eapply ULM_Step; eauto.
          constructors.
          auto.
          
    - lets H__: adm_apr_strat_drive tr Hcs Hreq Hadm Htrc.
      destruct H__ as (s' & tr' & Hsd' & Hfdeq' & Hex).
      destruct Hex as (cs' & Hcs' & Hfm' & Had').
      eapply ULM_Step; eauto.
      specialize (transition_reachable_stratDrive_transition_reachable
                    miner s0 s tr [h_usr; adm] honest_strat s' contract caddr tr').
      introv Htrc''.
      specializes Htrc''; eauto.
      lets Hor: Z.eqb_spec (funds s' caddr) 0.
      inverts Hor.
      +
        constructors.
        auto.
      +
        assert (Hrc_: reachable s').
        {
          specialize (transition_reachable_impl_reachable miner contract caddr s0 s').
          introv H__. specializes H__; eauto.
        }
        assert (Hge'1: funds s' caddr >= 0).
        {
          eapply reachable_funds_nonnegative; eauto.
        }
        eapply EPM_Step; eauto.
        lia.
        introv Hmsd.
        lets H__: att_multi_strat_drive_preserves_status Hcs' Htrc'' Hmsd Hws.
        destruct H__ as (Htrc'0 & Hex).
        destruct Hex as (cs'0 & Hcs'0 & Hfm'0_ & Had'0).
        assert (Hapr'0: FMap.find h_usr (status cs'0) = Some status_approved)
          by congruence.
        lets H__: usr_wth_strat_drive Hcs'0 Hapr'0 Htrc'0.
        protect addr_neq.
        destruct_and_split.
        eapply ULM_Step; eauto.
        constructors.
        auto.
      
    - lets H__: usr_wth_strat_drive tr Hcs Hapr Htrc.
      destruct H__ as (s' & tr' & Hsd & Hfd & Hex).
      eapply ULM_Step; eauto.
      eapply EPM_Base; eauto.
      
  Qed.

  (* strategy-aware liquidity is satisfied *)
  Theorem fm_sat_strat_liquidity:
    forall (att_strat: strat miner [d_usr]),
      well_strat [d_usr] att_strat -> 
      strat_liquidity miner [h_usr; adm] honest_strat [d_usr] att_strat contract caddr s0.
  Proof.
    unfold strat_liquidity.
    introv Hws Hini Hexe.
    assert (Htr0: transition_reachable miner contract caddr s0 s0).
    {
      eapply transition_reachable_init_state; eauto.
    }    
    specialize (transition_reachable_interleavedExecution_transition_reachable
                  miner honest_strat att_strat [h_usr; adm] [d_usr] s0 s0 tr s' tr' contract caddr Tusr).   
    introv Htrc.
    specialize (Htrc Htr0 Hexe). 
    eapply user_liq; eauto.
  Qed. 

End Liquidity. 
  
