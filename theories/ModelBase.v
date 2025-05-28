Require Import Blockchain.
Require Import Serializable.
Require Import BuildUtils.
Require Import RecordUpdate.
Require Import Automation.
Require Import ResultMonad.
Require Import ChainedList.
From Coq Require Import List.
From Coq Require Import ZArith.
From Coq Require Import Lia.
Import RecordSetNotations.
Import ListNotations.

Section Base.

Context {AddrSize : N}.
Context {DepthFirst : bool}.

Definition Error : Type := nat.
Definition default_error: Error := 1%nat.

  (* 添加记法，使得 tr ( s ) 可以被识别为 tr s *)
Notation "trace( s )" := (ChainTrace empty_state s) (at level 10).

Context {BaseTypes : ChainBase}.
Set Primitive Projections.
Set Nonrecursive Elimination Schemes.

Local Open Scope Z.

  Definition build_call {A : Type}
                        {ser : Serializable A}
                        (from to : Address)
                        (amount : Amount)
                        (msg : A)
                        : Action :=
    build_act from from (act_call to amount (@serialize A ser msg)).

  Definition build_transfer (from to : Address)
                            (amount : Amount)
                            : Action :=
    build_act from from (act_transfer to amount).

  Definition build_transfers (from : Address)
                              (txs : list (Address * Amount))
                            : list Action :=
    map (fun '(to, amount) => build_transfer from to amount) txs.

  Definition build_deploy {Setup Msg State Error : Type}
                          `{Serializable Setup}
                          `{Serializable Msg}
                          `{Serializable State}
                          `{Serializable Error}
                          (from : Address)
                          (amount : Amount)
                          (contract : Contract Setup Msg State Error)
                          (setup : Setup)
                          : Action :=
    build_act from from (create_deployment amount contract setup).

  Definition get_act_origin (a : Action) : Address :=
    act_origin a.

  Definition get_act_from (a : Action) : Address :=
    act_from a.

  Definition weak_error_to_error_init
    (r : result SerializedValue SerializedValue)
    : result SerializedValue Error :=
    bind_error (fun err => default_error) r.

  Definition weak_error_to_error_receive
    (r : result (SerializedValue * list ActionBody) SerializedValue)
    : result (SerializedValue * list ActionBody) Error :=
    bind_error (fun err => default_error) r.

  Definition queue_isb_empty bstate : bool :=
    match bstate.(chain_state_queue) with
    | [] => true
    | _ => false
    end.

  Definition isNone {A : Type} (x : option A) : bool :=
    match x with
    | None => true
    | Some _ => false
    end.
  Local Open Scope Z.

  Definition correct_contract_addr (env : Environment) (caddr : Address) : bool :=
    address_is_contract caddr && isNone (env_contracts env caddr).


  Definition deploy_contract
              (origin : Address)
              (from : Address)
              (to : Address)
              (amount : Amount)
              (wc : WeakContract)
              (setup : SerializedValue)
              (env : Environment)
              : result ChainState Error :=
      if amount <? 0 then
        Err default_error
      else if amount >? env_account_balances env from then
        Err default_error
      else
        let contract_addr := to in
        if correct_contract_addr env contract_addr then
          let env := transfer_balance from contract_addr amount env in
          let ctx := build_ctx origin from contract_addr amount amount in
          match wc_init wc env ctx setup with
          | Err _ => Err default_error
          | Ok state =>
            let env := add_contract contract_addr wc env in
            let env := set_contract_state contract_addr state env in
            Ok (build_chain_state env [])
          end
        else
          Err default_error.


  Lemma set_contract_state_equiv addr state (bstate : ChainState) (env : Environment) :
      EnvironmentEquiv (bstate) env ->
      EnvironmentEquiv
        (set_contract_state addr state (bstate))
        (Blockchain.set_contract_state addr state env).
    Proof.
      intros <-.
      apply build_env_equiv; auto.
    Qed.

  Lemma transfer_balance_equiv
          (from to : Address)
          (amount : Amount)
          (bstate : ChainState)
          (env : Environment) :
    EnvironmentEquiv bstate env ->
    EnvironmentEquiv
      (transfer_balance from to amount bstate)
      (Blockchain.transfer_balance from to amount env).
    Proof.
      intros <-.
      apply build_env_equiv; auto.
    Qed.

  Lemma add_contract_equiv addr wc (bstate : ChainState) (env : Environment) :
      EnvironmentEquiv bstate env ->
      EnvironmentEquiv
        (add_contract addr wc (bstate))
        (Blockchain.add_contract addr wc env).
    Proof.
      intros <-.
      apply build_env_equiv; auto.
    Qed.


  Lemma deploy_contract_step origin from to amount wc setup act env  new_bstate :
    deploy_contract origin from to amount wc setup env = Ok new_bstate ->
      act = build_act origin from (act_deploy amount wc setup) ->
      ActionEvaluation env act (new_bstate.(chain_state_env)) new_bstate.(chain_state_queue).
  Proof.
    intros dep act_eq.
    unfold deploy_contract in dep.
    destruct (Z.ltb amount 0) eqn:amount_nonnegative;
      [cbn in *; congruence|].
    destruct (Z.gtb amount (env_account_balances env from)) eqn:balance_enough;
      [cbn in *; congruence|].
    destruct (correct_contract_addr env to) eqn: ctr_addr;try congruence.
    destruct (wc_init _ _ _ _) as [state|] eqn:recv; [|cbn in *; congruence].
    set(new_acts := (chain_state_queue new_bstate)) in *.
    assert (new_acts = []) . 
    subst new_acts.
    inversion dep.
    subst.
    simpl.
    eauto.
    apply (eval_deploy origin from to amount wc setup state); eauto.
    inversion dep;propify;eauto;try lia.
    propify.
    eauto.
    unfold correct_contract_addr  in ctr_addr.
    destruct_and_split.
    propify.
    destruct_and_split.
    eauto.
    unfold correct_contract_addr  in ctr_addr.
    destruct_and_split.
    propify.
    destruct_and_split.
    unfold isNone in H1.
    destruct (env_contracts env to );try congruence.
    inversion dep.
    eapply build_env_equiv;eauto.
  Qed.

  Local Hint Resolve deploy_contract_step : core.

  Definition msg_to_call_action 
              (from to : Address)
              (amount : Amount) 
              (msg: SerializedValue) 
              : Action :=
    build_act from from (act_call to amount msg).

  Open Scope Z.


  Open Scope Z.
  Definition send_or_call
              (origin : Address)
              (from to : Address)
              (amount : Amount)
              (msg : option SerializedValue)
              (env : Environment)
              : result ChainState Error :=
    if amount <? 0 then
      Err default_error
    else if amount >? env_account_balances env from then
      Err default_error
    else
      match env_contracts env to with
      | None =>
        (* Fail if sending a message to address without contract *)
        if address_is_contract to then
          Err default_error
        else
          match msg with
          | None =>
            let new_env := transfer_balance from to amount env in
            Ok (build_chain_state new_env [])  (* 空的动作队列 *)
          | Some _ => Err default_error
          end
      | Some wc =>
        match env_contract_states env to with
        | None => Err default_error
        | Some state =>
          let env' := transfer_balance from to amount env in
          let ctx := build_ctx origin from to (env_account_balances env' to) amount in
          match weak_error_to_error_receive( wc_receive wc env' ctx state msg) with
          | Err e => Err e
          | Ok (new_state, new_actions) =>
            let new_env := set_contract_state to new_state env' in
            Ok (build_chain_state new_env (map (build_act origin to) new_actions)) (* 将新生成的动作添加到动作队列中 *)
          end
        end
      end. 

  Definition execute_action
              (act : Action)
              (env : Environment)
              : result ChainState Error :=
    match act with
    | build_act origin from (act_transfer to amount) =>
      send_or_call origin from to amount None env
    | build_act origin from (act_call to amount msg) =>
      send_or_call origin from to amount (Some msg) env
    | _ => Err default_error
    end.
  
  Local Open Scope nat.

  Fixpoint execute_actions
            (count : nat)
            (bstate : ChainState)
            (true : bool)
            : result ChainState Error :=
    let acts := bstate.(chain_state_queue) in
    let env := bstate.(chain_state_env) in
    match count, acts with
    | _, [] => Ok (build_chain_state env []) (* 动作执行完毕，返回更新后的 ChainState *)
    | 0, _ => Err default_error (* 超过最大执行次数，返回错误 *)
    | S count, act :: acts =>
      (* 执行当前的动作 *)
      match execute_action act env with
      | Ok new_bstate =>
        let new_acts := if true
                        then new_bstate.(chain_state_queue) ++ acts (* 深度优先：先执行当前的动作 *)
                        else acts ++ new_bstate.(chain_state_queue) (* 广度优先：先执行队列中的动作 *) in
        let new_env := new_bstate.(chain_state_env) in
        (* 递归调用 execute_actions 继续处理新的动作 *)
        execute_actions count (build_chain_state new_env new_acts) true
      | Err e =>
        Err e (* 如果执行失败，返回错误 *)
      end
    end.

  Local Open Scope Z.
  
  Lemma gtb_le x y :
    x >? y = false ->
    x <= y.
  Proof.
    intros H.
    rewrite Z.gtb_ltb in H.
    apply Z.ltb_ge.
    auto.
  Qed.
  
  Lemma ltb_ge x y :
    x <? y = false ->
    x >= y.
  Proof.
    intros H.
    apply Z.ltb_ge in H.
    lia.
  Qed.
 
  Lemma send_or_call_step origin from to amount msg act lc_before bstate:
    send_or_call origin from to amount msg lc_before = Ok bstate ->
    act = build_act origin from (match msg with
                                | None => act_transfer to amount
                                | Some msg => act_call to amount msg
                                end) ->
    ActionEvaluation lc_before act bstate.(chain_state_env) bstate.(chain_state_queue).
  Proof.
    intros sent act_eq.
    unfold send_or_call in sent.
    destruct (Z.ltb amount 0) eqn:amount_nonnegative;
      [cbn in *; congruence|].
    destruct (Z.gtb amount (env_account_balances lc_before from)) eqn:balance_enough;
      [cbn in *; congruence|].
    destruct (env_contracts lc_before to) as [wc|] eqn:to_contract.
    - destruct (env_contract_states _ _) as [prev_state|] eqn:prev_state_eq;
        [|cbn in *; congruence].
      destruct (wc_receive wc _ _ _ _) as [[new_state resp_acts]|] eqn:receive;
        [|cbn in *; congruence].
      apply (eval_call origin from to amount wc msg prev_state new_state resp_acts);
        try solve [cbn in *; auto; congruence].
      + cbn in sent.
        inversion_clear sent.
        lia.
      + inversion sent; subst.
        lia.
      + inversion sent; subst. eauto.
      + cbn in sent.
        inversion_clear sent.
        simpl. eauto.
      + cbn in sent.
        inversion_clear sent.
        simpl. eauto.
        apply build_env_equiv; auto.
    - destruct (address_is_contract to) eqn:addr_format; cbn in *; try  congruence.
      destruct msg; cbn in *; try congruence.
      assert (chain_state_queue bstate = []).
      inversion sent. simpl. eauto.
      rewrite H.
      apply (eval_transfer origin from to amount); auto.
      lia. lia.
      inversion sent; subst.
      apply build_env_equiv; auto.
  Qed.

  Local Hint Resolve deploy_contract_step : core.

  Local Hint Resolve send_or_call_step : core.
  
  Lemma execute_action_step
        (act : Action)
        (lc_before : Environment)
        (bstate : ChainState) :
    execute_action act lc_before = Ok bstate ->
    ActionEvaluation lc_before act bstate.(chain_state_env) bstate.(chain_state_queue).
  Proof.
    intros exec.
    unfold execute_action in exec.
    destruct act as [orig from body].
    destruct body as [to amount|to amount msg|amount wc setup]; eauto.
    congruence.
  Defined.

  Lemma execute_action_current_slot_eq :
    forall a pre next ,
    execute_action a pre = Ok next ->
    current_slot next = current_slot pre.
  Proof.
  intros.
    eapply current_slot_post_action.
    eapply execute_action_step;eauto.
  Qed.

  Hint Constructors ChainStep : core.
  Hint Constructors ChainedList : core.
  Hint Unfold ChainTrace : core.
 
 
  Lemma execute_actions_trace count (prev_bstate next_bstate : ChainState) df (trace : ChainTrace empty_state prev_bstate) :
      df = true ->
      execute_actions count prev_bstate df = Ok next_bstate ->
      ChainTrace empty_state next_bstate.
  Proof.
    revert prev_bstate next_bstate trace.
    induction count as [| count IH]; intros prev_bstate next_bstate trace exec; cbn in *.
    - destruct (chain_state_queue prev_bstate) eqn : acts.
      destruct prev_bstate as [env queue].
      simpl in *. rewrite acts in trace.
      inversion exec. congruence.
      congruence.
    - destruct prev_bstate as [lc acts].
      cbn in *.
      destruct acts as [|x xs]; try congruence.
      destruct (execute_action x lc) as [[lc_after new_acts]|] eqn:exec_once;
        cbn in *; try congruence.
      set (step := execute_action_step _ _  _ exec_once).
      refine (IH _ _ _ exec).
      destruct df eqn : H_df;try congruence.
      + (* depth-first case *)
        eauto.
  Qed.
  
  Lemma execute_actions_next_bstate_queue:
    forall df count (prev_bstate next_bstate : ChainState),
      execute_actions count prev_bstate df = Ok next_bstate -> 
      next_bstate.(chain_state_queue) = [].
  Proof.
    intros df count.
    induction count as [| count' IH]; intros prev_bstate next_bstate Hexec.
    - simpl in Hexec.
      destruct prev_bstate.(chain_state_queue) eqn:Hqueue.
      + 
        inversion Hexec. subst.
        reflexivity.
      + discriminate Hexec.
    - simpl in Hexec.
      destruct prev_bstate.(chain_state_queue) eqn:Hqueue.
      + inversion Hexec. subst.
        reflexivity.
      + destruct (execute_action a prev_bstate.(chain_state_env)) eqn:Hexec_act.
        * destruct t as [env_after new_queue].
          destruct df.
          -- simpl in Hexec.
              set (new_acts := new_queue ++ l).
              apply IH in Hexec.
              assumption.
          -- simpl in Hexec.
              set (new_acts := l ++ new_queue).
              apply IH in Hexec.
              assumption.
        * discriminate Hexec.
  Qed.
  
  Lemma execute_actions_trace_pb count (prev_bstate next_bstate : ChainState) df (trace : ChainTrace empty_state prev_bstate) :
      df = true ->
      execute_actions count prev_bstate df = Ok next_bstate ->
      ChainTrace prev_bstate next_bstate.
  Proof.
    revert df prev_bstate next_bstate trace.
    induction count as [| count IH]; intros df prev_bstate next_bstate trace  H_df exec; cbn in *.
    - destruct (chain_state_queue prev_bstate) eqn : acts.
      destruct prev_bstate as [env queue].
      simpl in *. rewrite acts in trace.
      inversion exec.
      eauto.
      rewrite acts.
      eauto.
      congruence.
    - destruct prev_bstate as [lc acts].
      cbn in *.
      destruct acts as [|x xs]; try congruence.
      inversion exec. eauto.
      destruct (execute_action x lc) as [[lc_after new_acts]|] eqn:exec_once;
        cbn in *; try congruence.
        rewrite H_df in *.
      assert (step : ActionEvaluation lc x {| chain_state_env := lc_after; chain_state_queue := new_acts |}
      (chain_state_queue {| chain_state_env := lc_after; chain_state_queue := new_acts |})).
      {
          apply execute_action_step.
          eauto.
      }
      assert (step1 : ChainStep
      {| chain_state_env := lc; chain_state_queue := x :: xs |}
      {| chain_state_env := lc_after; chain_state_queue := new_acts ++ xs |}).
      {
        set (mid_bstate :=  {| chain_state_env := lc; chain_state_queue := x :: xs |}).
          set (next_bstate' :={| chain_state_env := lc_after; chain_state_queue := new_acts ++ xs |}).
        (* 使用 step 构造这一步的 ChainTrace *)
        eapply step_action.
        eauto.
        eauto.
        eauto.
      }
      assert (s1 :reachable  {| chain_state_env := lc; chain_state_queue := x :: xs |}).
      {
        apply trace_reachable in trace.
        eauto.
      }
      assert(s2 : reachable {| chain_state_env := lc_after; chain_state_queue := new_acts ++ xs |}).
      {
        eapply reachable_step.
        eauto.
        eauto.
      }
      unfold reachable in s2.
      assert (trace' : (ChainTrace empty_state
      {| chain_state_env := lc_after; chain_state_queue := new_acts ++ xs |})) by eauto.
      set (mid := {| chain_state_env := lc_after; chain_state_queue := new_acts ++ xs |}).
  
      assert (trace1 : ChainTrace
      {| chain_state_env := lc_after; chain_state_queue := new_acts ++ xs |}
      {| chain_state_env := next_bstate.(chain_state_env); chain_state_queue := [] |}).
    {
      apply (IH df {| chain_state_env := lc_after; chain_state_queue := new_acts ++ xs |} {| chain_state_env := next_bstate.(chain_state_env); chain_state_queue := [] |}).
      eauto.
      eauto.
      assert(execute_actions count
      {| chain_state_env := lc_after; chain_state_queue := new_acts ++ xs |} true =
    Ok next_bstate) by eauto.
    eapply execute_actions_next_bstate_queue in H.
      simpl.
      rewrite H_df in *.
      rewrite exec.
      destruct next_bstate as [env queue].
      simpl.
      simpl in H.
      rewrite H.
      eauto.
    }
    assert (trace2 : ChainTrace {| chain_state_env := lc; chain_state_queue := x :: xs |}
    {| chain_state_env := lc_after; chain_state_queue := new_acts ++ xs|}).
    {
      eauto. 
    }
    set (final_trace := clist_app trace2 trace1).
    assert(execute_actions count
      {| chain_state_env := lc_after; chain_state_queue := new_acts ++ xs |} true =
    Ok next_bstate) by eauto.
    eapply execute_actions_next_bstate_queue in H.
    destruct next_bstate as [env queue].
    simpl in *.
    rewrite H.
    eauto.
  Qed.


Hint Constructors ChainStep : core.
Hint Constructors ChainedList : core.
Hint Unfold ChainTrace : core.
  
  
  Local Open Scope nat.
  
  Definition validate_header (header : BlockHeader) (chain : Chain) : bool :=
    (block_height header =? S (chain_height chain))
    && (current_slot chain <? block_slot header)
    && (finalized_height chain <=? block_finalized_height header)
    && address_not_contract (block_creator header)
    && (block_reward header >=? 0)%Z.
  
  Definition find_origin_neq_from (actions : list Action) : option Action :=
    find (fun act => address_neqb (act_origin act) (act_from act)) actions.
  
  Definition find_invalid_root_action (actions : list Action) : option Action :=
    find (fun act => address_is_contract (act_from act)) actions.
  
  Local Open Scope Z.

  Definition add_block
            (env : Environment)
            (header : BlockHeader)
            (actions : list Action) : r(*  *)esult ChainState Error :=
    (* 第一步：验证头部 *)
    match validate_header header env with
      | true =>
          match find_origin_neq_from actions with
          | Some _ => Err default_error
          | None =>
              match find_invalid_root_action actions with
              | Some _ => Err default_error
              | None =>
                  (* 所有前置条件都满足，继续执行后续操作 *)
                  let env' := add_new_block_to_env header env in
                  Ok (build_chain_state env' actions) 
              end
          end
      | false => Err default_error
    end.

  Definition evaluate_action
            (true:bool) 
            (env : Environment)
            (header : BlockHeader)
            (actions : list Action) : result ChainState Error :=
    (* 第一步：验证头部 *)
    match validate_header header env with
    | true =>
        match find_origin_neq_from actions with
        | Some _ => Err default_error
        | None =>
            match find_invalid_root_action actions with
            | Some _ => Err default_error
            | None =>
                (* 所有前置条件都满足，继续执行后续操作 *)
                let env' := add_new_block_to_env header env in
                let new_bstate := build_chain_state env' actions in
                execute_actions 5 new_bstate true
            end
        end
    | false => Err default_error
    end.

  Local Hint Resolve validate_header find_origin_neq_from       find_invalid_root_action : core.
  
  Lemma add_block_next_state_queue_empty (prev_bstate next_bstate : ChainState) df header actions (trace : ChainTrace empty_state prev_bstate)  :
      evaluate_action df prev_bstate header actions = Ok next_bstate ->
      next_bstate.(chain_state_queue) = [].
  Proof.
    intros H_exec.
    unfold evaluate_action in H_exec.
    destruct_match in H_exec;try congruence.
    destruct_match in H_exec;try congruence.
    destruct_match in H_exec;try congruence.
    eapply execute_actions_next_bstate_queue;eauto.
  Qed.

  (* 辅助引理 *)
  Lemma find_none_implies_all_false :
    forall (A : Type) (P : A -> bool) (l : list A),
      find P l = None ->
      Forall (fun x => P x = false) l.
  Proof.
    intros A P l Hfind.
    induction l as [|a l' IH].
    - apply Forall_nil.
    - simpl in Hfind.
      destruct (P a) eqn:Heq.
      + inversion Hfind.
      + apply Forall_cons.
        * assumption.
        * apply IH. assumption.
  Qed.

  Lemma add_block_reachable_through_aux (prev_bstate next_bstate : ChainState) df header actions (trace : ChainTrace empty_state prev_bstate)  :
      df = true ->
      prev_bstate.(chain_state_queue) = [] ->
      evaluate_action df prev_bstate header actions = Ok next_bstate ->
      ChainTrace prev_bstate next_bstate.
  Proof.
    intros H_df H_queue H_exec.
    unfold evaluate_action in H_exec.
    destruct (validate_header header prev_bstate) eqn: H_header;try congruence.
    destruct (find_origin_neq_from actions) eqn:H_fonf;try congruence.
    destruct (find_invalid_root_action actions) eqn:H_fira;try congruence.
    set (mid_bstate := {|
    chain_state_env := add_new_block_to_env header prev_bstate;
    chain_state_queue := actions
    |}).
    assert (step : ChainStep prev_bstate mid_bstate).
    {
      eapply step_block;eauto.
      
      unfold validate_header in H_header.
      propify.
      destruct_and_split.
      apply build_is_valid_next_block;eauto.
      unfold address_not_contract in H1.
      destruct (address_is_contract (block_creator header));try congruence;eauto.
      lia.
      unfold act_is_from_account.
      apply find_none_implies_all_false.
      apply H_fira.
      simpl.
      unfold act_origin_is_eq_from.
      apply find_none_implies_all_false in H_fonf.
      apply Forall_impl with (P := fun act => address_neqb (act_origin act) (act_from act) = false).
      intros act H'.
      destruct_address_eq;try congruence;eauto.
      apply H_fonf.
      apply build_env_equiv.
      eauto.
      eauto.
      eauto.
      eauto.
    }
    apply execute_actions_trace_pb in H_exec;eauto.
    assert(trace_1 : ChainTrace prev_bstate prev_bstate) by eauto.
    assert(trace_2 : ChainTrace prev_bstate mid_bstate) by eauto.
    set (final_trace := clist_app trace_2 H_exec).
    eauto.
  Qed.

  Lemma add_block_trace (prev_bstate next_bstate : ChainState) df header actions (trace : ChainTrace empty_state prev_bstate) :
    df = true ->
    prev_bstate.(chain_state_queue) = [] ->
    evaluate_action df prev_bstate header actions = Ok next_bstate ->
    ChainTrace empty_state next_bstate.
  Proof.
    intros.
    assert(ChainTrace prev_bstate next_bstate).
    {
      eapply add_block_reachable_through_aux in H1;eauto.
    }
    set (trace' := clist_app trace X).
    eauto.
  Qed.


End Base.