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


Section Strat.

  Local Open Scope bool.

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
Section concert_exec_base.
  
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
      let new_acts := new_bstate.(chain_state_queue) in
      act = build_act origin from (act_deploy amount wc setup) ->
      ActionEvaluation env act (new_bstate.(chain_state_env)) new_acts.
    Proof.
      intros dep new_acts act_eq.
      unfold deploy_contract in dep.
      destruct (Z.ltb amount 0) eqn:amount_nonnegative;
        [cbn in *; congruence|].
      destruct (Z.gtb amount (env_account_balances env from)) eqn:balance_enough;
        [cbn in *; congruence|].
      destruct (correct_contract_addr env to) eqn: ctr_addr;try congruence.
      destruct (wc_init _ _ _ _) as [state|] eqn:recv; [|cbn in *; congruence].
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

  Definition current_bstate
              {from to : ChainState}
              (trace : ChainTrace from to)
              : ChainState :=
              to.

  Open Scope Z.

  Section cstExec.

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
  End cstExec.

End concert_exec_base.

Section exec_base_proof.
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

      (* + breadth-first case. Insert permute step.
        assert (Permutation (new_acts ++ xs) (xs ++ new_acts)) by perm_simplify.
        cut (ChainTrace
              empty_state
              (build_chain_state lc_after (new_acts ++ xs))); eauto.
        intros.
        econstructor; eauto.
        constructor; eauto.
        constructor; eauto. *)
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

End exec_base_proof.


  Hint Constructors ChainStep : core.
  Hint Constructors ChainedList : core.
  Hint Unfold ChainTrace : core.
  
Section exec_action.
  


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
                  Ok (build_chain_state env' actions) 
              end
          end
      | false => Err default_error
    end.
  
  Definition add_block_exec
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
      add_block_exec df prev_bstate header actions = Ok next_bstate ->
      next_bstate.(chain_state_queue) = [].
  Proof.
    intros H_exec.
    unfold add_block_exec in H_exec.
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
      add_block_exec df prev_bstate header actions = Ok next_bstate ->
      ChainTrace prev_bstate next_bstate.
  Proof.
    intros H_df H_queue H_exec.
    unfold add_block_exec in H_exec.
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
    add_block_exec df prev_bstate header actions = Ok next_bstate ->
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
End exec_action.

  Context {Setup Msg State Error : Type}
          `{Serializable Setup}
          `{Serializable Msg}
          `{Serializable State}
          `{Serializable Error}.
    
  Variable miner_address : Address.

  Hypothesis miner_always_eoa : address_is_contract miner_address = false.


  Global Definition miner_reward := 10%Z.

Section transition_trace.
    
 

  Definition funds (env : ChainState) (caddr : Address) : Amount :=
    env_account_balances env caddr.

  Lemma reachable_funds_nonnegative:
    forall s caddr,
      reachable s ->
      (funds s caddr >= 0)%Z .
  Proof.
    intros.
    unfold funds.
    eapply account_balance_nonnegative;eauto.
  Qed.

  Definition safe_Z_to_nat (z : Z) : nat :=
    if Z.leb 0 z then Z.to_nat z else 0.
  
  Global Definition time_speed := 1%nat.

  
  Definition get_valid_header bstate : BlockHeader :=
    build_block_Header 
      (S (chain_height bstate))
      (current_slot bstate + 1)%nat
      (finalized_height bstate)
      miner_reward
      miner_address.

  Definition is_init_state (contract : Contract Setup Msg State Error) 
                            (caddr : Address)
                            (init_state : ChainState) :=
      reachable init_state /\
      chain_state_queue init_state = [] /\
      env_contracts init_state caddr = Some (contract : WeakContract) /\
      let env := init_state.(chain_state_env) in
      exists ctx setup state,
        env_contract_states init_state caddr = Some (serialize state) /\
        init contract env ctx setup = Ok state.

    
  Definition is_call_act (a : Action) : bool :=
    match a with
    | build_act _ _ (act_call _ _ _) => true
    | _ => false
    end.

  Definition transition
    (prev_bstate : ChainState)
    (act : Action) : result ChainState Strat.Error :=
    if (queue_isb_empty prev_bstate) then 
        if is_call_act act then
          let header := get_valid_header prev_bstate in
          match add_block_exec true prev_bstate header [act] with
          | Ok new_bstate => Ok new_bstate
          | Err _ => Err default_error
          end
        else 
          Err default_error
    else 
      Err default_error.

  Inductive TransitionStep (prev_bstate : ChainState) (next_bstate : ChainState) :=
  | step_trans :
      forall (a : Action),
        is_call_act a = true ->
        transition prev_bstate a = Ok next_bstate ->
        TransitionStep prev_bstate next_bstate.
  
  Global Arguments step_trans {_ _  }.

  Definition aux_trace := prefixTrace ChainState TransitionStep.

  Definition TransitionTrace := ChainedList ChainState TransitionStep.

  Notation "trace( from , to )" := (TransitionTrace from to)(at level 10).

  Definition transition_reachable 
              (contract : Contract Setup Msg State Error)
              (caddr :Address)
              (s0 s : ChainState) :=
    is_init_state contract caddr s0  /\
    inhabited (trace(s0,s)).

  Definition reachable_via contract caddr s0 mid to := transition_reachable contract caddr s0 mid /\ inhabited (trace(mid, to)).



  Definition readyToStepState 
              (contract : Contract Setup Msg State Error)
              (caddr : Address )
              (s0 s : ChainState)
              : Prop :=
    transition_reachable contract caddr s0 s  /\
    chain_state_queue s = [].

    
      (* 清算能力的存在性 *)
  Definition base_liquidity 
            (c : Contract Setup Msg State Error)
            (caddr : Address)
            (s0 : ChainState) :=
    forall s ,
      is_init_state c caddr s0 ->
      readyToStepState c caddr s0 s ->
      exists s',
        (inhabited(trace( s, s')) /\ funds s' caddr = 0)%Z.
End transition_trace.

Section strat_model.

  Notation "trace( from , to )" := (TransitionTrace from to)(at level 10).

  Definition strat := forall s0 s, trace(s0, s) -> list Address -> list Action.

  Definition is_valid_action (s : ChainState) (a : Action) : bool :=
    match transition s a with
    (* 包含等待动作以及caddr的act_call *)
    | Ok _ => is_call_act a
    | Err _ => false
    end.

  Definition wellStrat (delta : strat)
                        (addrs : list Address)
                        (contract : Contract Setup Msg State Error)
                        (caddr : Address)
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
                  (caddr : Address)
                  (s0 : ChainState) :=
    wellStrat delta addrs contract caddr s0  /\ 
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
    wellStrat delta_usr addrs_usr c caddr s0  /\
    wellStrat delta_env addrs_env c caddr s0 /\
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

End strat_model.
  
  Ltac decompose_exists :=
    repeat match goal with
            | [ H : exists _, _ |- _ ] =>
                let x := fresh "x" in
                destruct H as [x H]
            end.

  Ltac decompose_wellDefinedSystem H :=
    match type of H with
    | wellDefinedSystem ?delta_usr ?addrs_usr ?delta_env ?addrs_env ?caddr ?c ?s0 =>
        unfold wellDefinedSystem in H;
        let H_usr_strat := fresh "H_usr_strat" in
        let H_env_strat := fresh "H_env_strat" in
        let H_finite := fresh "H_finite" in
        let H_init := fresh "H_init" in
        destruct H as [H_usr_strat [H_env_strat [H_finite H_init]]]
    | _ => fail "The hypothesis" H "is not of the form wellDefinedSystem."
    end.

  Ltac decompose_wellStrat H :=
    unfold wellStrat in H;
    let Hs0 := fresh "Hs0" in
    let Hs := fresh "Hs" in
    let Htr_s := fresh "Htr_s" in
    intros Hs0 Hs Htr_s;
    match type of H with
    | context[let delta_actions := ?delta _ _ _ _ in _] =>
        let Hda := fresh "Hda" in
        set (delta_actions := delta _ _ _ _) in H;
        unfold delta_actions in H
    | _ => idtac
    end;
    match type of H with
    | _ -> Forall _ _ =>
        let Hq := fresh "Hq" in
        intros Hq; specialize (H Hq)
    | Forall _ ?l =>
        let Ha := fresh "Ha" in
        apply Forall_forall in H; intros Ha
    | _ => idtac
    end.

  Ltac decompose_transition_reachable H :=
    unfold transition_reachable in H;
    destruct H as [init_bstate [trace]].
  
  Ltac decompose_reachable_via H :=
    match type of H with
    | reachable_via ?contract ?caddr ?s0 ?mid ?to =>
        unfold reachable_via in H;
        let H_reachable := fresh "H_reachable" in
        let tr := fresh "tr" in
        destruct H as [H_reachable H_trace];
        destruct H_trace as [tr] (* 只引入轨迹变量 tr，避免未使用的附加绑定 *)
    | _ => fail "The hypothesis" H "is not of the form reachable_via contract caddr s0 mid to."
    end.

  Ltac decompose_is_init_state H :=
    match type of H with
    | is_init_state ?contract ?caddr ?init_state =>
        unfold is_init_state in H;
        let H_reachable := fresh "H_reachable" in
        let H_queue := fresh "H_queue" in
        let H_env_contracts := fresh "H_env_contracts" in
        let H_env_details := fresh "H_env_details" in
        destruct H as [H_reachable [H_queue [H_env_contracts H_env_details]]];
        let ctx := fresh "ctx" in
        let setup := fresh "setup" in
        let state := fresh "state" in
        let H_env_states := fresh "H_env_states" in
        let H_init := fresh "H_init" in
        destruct H_env_details as [ctx [setup [state [H_env_states H_init]]]]
    | _ => fail "The hypothesis" H "is not of the form is_init_state contract caddr init_state."
    end.

  Ltac decompose_stratDrive H :=
    match type of H with
    | stratDrive ?s0 ?delta ?addrs ?s ?tr ?s' ?tr' =>
        unfold stratDrive in H;
        let a := fresh "a" in
        let H_trans := fresh "H_transition" in
        destruct H as [a [H_trans [H_in H_trace]]]
    | _ => fail "The hypothesis" H "is not of the form stratDrive s0 delta addrs s tr s' tr'."
    end.

  Ltac decompose_transition H :=
    unfold transition in H;
    repeat match type of H with
    | context[if queue_isb_empty ?state then _ else _] =>
        let Hqueue := fresh "Hqueue" in
        destruct (queue_isb_empty state) eqn:Hqueue; try congruence
    | context[if is_call_act ?act then _ else _] =>
        let Hcall := fresh "Hcall" in
        destruct (is_call_act act) eqn:Hcall; try congruence
    | context[let header := get_valid_header ?state in _] =>
        let Hheader := fresh "Hheader" in
        remember (get_valid_header state) as header eqn:Hheader
    | context[match add_block_exec ?mode ?state ?header ?acts with | Ok _ => _ | Err _ => _ end] =>
        let Hexec := fresh "Hexec" in
        destruct (add_block_exec mode state header acts) eqn:Hexec; try congruence
    | context[match ?res with | Ok _ => _ | Err _ => _ end] =>
        let Hres := fresh "Hres" in
        destruct res eqn:Hres; try congruence
    end;
    repeat match type of H with
    | Ok _ = Ok _ => inversion H; subst; clear H
    | Err _ = Err _ => inversion H; subst; clear H
    end.

    Notation "trace( from , to )" := (TransitionTrace from to)(at level 10).


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
        forall s0 s' flag tr tr',
          strat_subset_strict delta_env1 addrs_env1 delta_env2 addrs_env2 s0 ->
          interleavedExecution delta_usr addrs_usr delta_env1 addrs_env1 s0 s0 tr flag s' tr' ->
          interleavedExecution delta_usr addrs_usr delta_env2 addrs_env2 s0 s0 tr flag s' tr'.
      Proof.
        intros * Hsbt_delta Hrc_itv.
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
        forall s0 s s' c caddr tr tr',
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
        forall s0 s s' c caddr tr tr',
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
  
      Lemma strat_liquid_Mono_usr_unchanging (delta_usr : strat) (addrs_usr: list Address)  (delta_env1 : strat) (addrs_env1: list Address) (delta_env2 : strat) (addrs_env2: list Address) :
        forall s0 c caddr, 
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
        forall s0 c caddr, 
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
    

  Lemma transition_reachable_init_state c s0 caddr:
    is_init_state c caddr s0 ->
    transition_reachable c caddr s0 s0.
  Proof.
    intros.
    unfold transition_reachable.
    split.
    eauto.
    econstructor.
    eapply clnil.
  Qed.


  Lemma transition_reachable_trans c s0 s s' caddr:
    transition_reachable c caddr s0 s -> 
    TransitionTrace s s' -> 
    transition_reachable c caddr s0 s'.
  Proof.
    intros H_reachable H_trace.
    decompose_transition_reachable H_reachable.
    unfold transition_reachable in *.
    eauto.
    econstructor;eauto.
    econstructor;eauto.
    eapply clist_app;eauto.
  Qed.

  (* Transitivity property of reachable and ChainStep *)
  Lemma transition_reachable_step s0 c from to caddr:
    transition_reachable c caddr s0 from -> 
    TransitionStep from to -> 
    transition_reachable c caddr s0 to.
  Proof.
    intros H_reachable H_step.
    decompose_transition_reachable H_reachable.
    unfold transition_reachable .
    split.
    eauto.
    econstructor;eauto.
    eapply (snoc trace H_step).
  Qed.

  Hint Resolve transition_reachable_init_state
                transition_reachable_trans
                transition_reachable_step : core.

  Lemma reachable_via_refl : forall c caddr s0 s,
    transition_reachable c caddr s0 s -> reachable_via c caddr s0 s s.
  Proof.
    intros.
    decompose_transition_reachable H3.
    repeat (econstructor; eauto).
  Qed.

  Lemma reachable_via_trans' : 
    forall c caddr init from mid to,
      reachable_via c caddr init from mid -> 
      TransitionStep mid to -> 
      reachable_via c caddr init from to.
  Proof.
    intros * [reach [trace]] step.
    repeat (econstructor; eauto).
  Qed.

  Lemma reachable_via_trans : 
    forall c caddr init from mid to,
      reachable_via c caddr init from mid -> 
      reachable_via c caddr init mid to -> 
      reachable_via c caddr init from to.
  Proof.
    intros.
    decompose_reachable_via H3.
    decompose_reachable_via H4.
    unfold reachable_via.
    split.
    eauto.
    econstructor;eauto.
    eapply ChainedList.clist_app;eauto.
  Qed.


  Lemma reachable_via_step : 
    forall c caddr init from to,
      transition_reachable c caddr init from -> 
      TransitionStep from to -> 
      reachable_via c caddr init from to.
  Proof.
    intros * reach_from step.
    apply reachable_via_refl in reach_from.
    eapply reachable_via_trans' ; eauto.
  Qed.

  Lemma transition_reachable_through_reachable : 
    forall c caddr init from to,
      reachable_via c caddr init from to -> 
      transition_reachable c caddr init to.
  Proof.
    intros.
    decompose_reachable_via H3.
    decompose_transition_reachable H_reachable.
    econstructor.
    eauto.
    econstructor.
    eapply ChainedList.clist_app ; eauto.
  Qed.
  

  Lemma transition_trans_through c caddr:
  forall (s0 s s' : ChainState) a,
    transition_reachable c caddr s0 s ->
    transition s a = Ok s' ->
    reachable_via c caddr s0 s s'.
  Proof.
    intros.
    unfold transition_reachable in H3;
    destruct H3 as [init_bstate [trace]].
    econstructor.
    eauto.
    econstructor.
    assert(step : TransitionStep s s').
    {
      pose proof H4 as H_new.
      unfold transition in H4.
      destruct_match in H4;try congruence.
      destruct (is_call_act a) eqn : H_call;try congruence.
      eapply step_trans;eauto.
    }
    assert(TransitionTrace s s).
    {
      eauto.
      eapply clnil.
    }
    econstructor;eauto.
  Qed.


  Lemma init_ready : 
  forall s0 c caddr,
    is_init_state c caddr s0 ->
    readyToStepState c caddr s0 s0 .
  Proof.
    intros s0 c caddr H_init.
    unfold readyToStepState.
    assert (H_temp:is_init_state c caddr s0) by eauto.
    decompose_is_init_state H_temp.
    split.
    unfold transition_reachable.
    split.
    eauto.
    econstructor;eauto.
    eapply clnil.
    eauto.
  Qed.


  Hint Resolve reachable_via_refl
                reachable_via_trans'
                reachable_via_trans
                reachable_via_step
                transition_reachable_through_reachable 
                transition_trans_through 
                init_ready: core.

  Hint Unfold maxMultiStratDrive : core.

  Local Open Scope nat.

  Lemma delta_all_is_wellStrat:
    forall delta addrs contract caddr s0 ,
      is_init_state contract caddr s0 ->
      is_complete_strategy delta addrs contract caddr s0 ->
      wellStrat delta addrs contract caddr s0.
    Proof.
      intros * H_init H_complete_strategy.
      edestruct H_complete_strategy;eauto.
    Qed.

    Lemma multiStratDrive_n_zero_s_eq:
      forall s0 s s' tr tr' n delta addrs,
        multiStratDrive delta addrs s0 s tr s' tr' n -> 
        (n = 0)%nat ->
        s = s' /\ existT s tr = existT s' tr'.
    Proof.
      intros s0 s s' tr tr' n delta addrs H_multi H_n.
      induction H_multi;eauto;try lia.
    Qed.


  Lemma get_valid_header_is_valid_header s:
    validate_header( get_valid_header s )  s = true.
  Proof.
    intros.
    unfold get_valid_header.
    unfold validate_header.
    propify.
    repeat split;cbn ;try lia;eauto.
    unfold miner_reward.
    unfold address_not_contract.
    rewrite miner_always_eoa.
    simpl.
    lia.
    unfold miner_reward.
    lia. 
  Qed.


  Lemma delta_empty_is_wellStrat delta addrs contract caddr s0 :
    is_empty_strat delta addrs -> 
    wellStrat delta addrs contract caddr s0.
    Proof.
      unfold wellStrat, is_empty_strat.
      intros.
      split.
      intros.
      specialize(H3 s0 s tr_s).
      rewrite H3.
      unfold is_valid_action.
      eapply Forall_forall.
      intros.
      inversion H5.
      eapply Forall_forall.
      intros.
      specialize(H3 s0 s tr_s).
      rewrite H3 in H4.
      inversion H4.
    Qed.


    Lemma multiSuccTrace_delta_empty_refl_multr :
      forall (s0 s : ChainState) (tr : trace(s0,s)) (s' : ChainState) (tr' : trace(s0 ,s')) delta addrs n,
        is_empty_strat delta addrs ->
        multiStratDrive delta addrs s0 s tr s' tr' n ->
        n = 0 /\ multiStratDrive delta addrs s0 s tr s tr n.
    Proof.
      intros s0 s tr s' tr' delta addrs n H_empty H_multi.
      induction H_multi;try lia;eauto.
      - split.
        eauto.
        apply MS_Refl.
      - unfold stratDrive in H3.
        do 4 destruct H3.
        unfold is_empty_strat in H_empty.
        specialize(H_empty s0 s' tr').
        rewrite H_empty in H3.
        inversion H3.
    Qed.

    Lemma multiSuccTrace_delta_empty_refl_multr_end :
    forall (s0 s : ChainState) (tr : trace(s0,s)) (s' : ChainState) (tr' : trace(s0 ,s')) delta addrs n,
      is_empty_strat delta addrs ->
      multiStratDrive delta addrs s0 s tr s' tr' n ->
      n = 0 /\ 
      multiStratDrive delta addrs s0 s' tr' s' tr' n /\ 
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

    Lemma multiSuccTrace_delta_empty_refl_multr_s_tr :
    forall (s0 s : ChainState) (tr : trace(s0,s)) (s' : ChainState) (tr' : trace(s0 ,s')) delta addrs n,
      delta s0 s tr addrs = [] ->
      multiStratDrive delta addrs s0 s tr s' tr' n ->
      s = s' /\ existT s tr = existT s' tr'.
    Proof.
      intros.
      induction H4;eauto.
      destruct IHmultiStratDrive.
      eauto.
      subst.
      unfold stratDrive in H5.
      do 4 destruct H5.
      assert(delta s0 s' tr' addrs = []).
      {
        inversion H7.
        eauto.
      }
      destruct_and_split.
      rewrite H8 in H5.
      inversion H5.
      rewrite H8 in H5.
      inversion H5.
    Qed.


    Lemma multiSuccTrace_trans_thrid :
    forall delta addrs s0 s1 s2 s3  tr1 tr2 tr3 n m,
      multiStratDrive delta addrs s0 s1 tr1 s2 tr2 n ->
      multiStratDrive delta addrs s0 s2 tr2 s3 tr3 m ->
      multiStratDrive delta addrs s0 s1 tr1 s3 tr3 (n + m).
    Proof.
      clear H H0 H1 H2.
      intros delta addrs s0 s1 s2 tr0 tr1 tr2 tr3 n m H1 H2 .
      induction H2.
      - assert( n + 0 = n) by lia.
        rewrite H.
        assumption.
      - (* Case MS_Step *)
        assert(multiStratDrive delta addrs s0 s1 tr1 s'' tr''  (n + count + 1)).
        {
          eapply MS_Step with (s' := s') (s'' := s'') (tr' := tr') (tr'' := tr'') (count := n + count).
          + apply IHm0; assumption.
          + assumption.
        }
        assert((n + count + 1) = (n + (count + 1))) by lia.
        rewrite <- H3.
        eauto.
    Qed.
        

    Lemma transition_reachable_can_Inter_usr_all:
      forall s0 s (tr:trace(s0,s0)) c caddr delta_usr delta_env addrs_usr addrs_env,
        is_complete_strategy delta_usr addrs_usr c caddr s0->
        is_empty_strat delta_env addrs_env ->
        is_init_state c caddr s0  ->
        transition_reachable c caddr s0 s ->
        exists (trace:trace(s0,s)),
          interleavedExecution delta_usr addrs_usr delta_env addrs_env s0 s0 tr Tusr s trace.
    Proof.
      intros s0 s tr c caddr delta_usr delta_env addrs_usr addrs_env
      H_complete_strategy H_empty_delta H_init_state H_transition_reachable.
      assert(H_temp: transition_reachable c caddr s0 s) by eauto.
      decompose_transition_reachable H_temp.
      induction trace.
      + exists tr.
        eapply IS_Refl.
      + assert (transition_reachable c caddr from mid).
        {
          econstructor;eauto.
        }
        specialize(IHtrace tr H_complete_strategy init_bstate  H3 init_bstate).
        destruct IHtrace as [tr' IHtrace].
        pose proof l.
        inversion X.
        * set(tr'' := snoc tr' (step_trans a H4 H5)).
          exists tr''.
          pose proof H4.
          (* assert(delta_env from mid tr' addrs_env = [wait_action_vo]).
          {
            eauto.
          } *)
          assert(In a (delta_usr from mid tr' addrs_usr)).
          {
            unfold is_complete_strategy in H_complete_strategy.
            destruct_and_split.
            specialize(H8 mid to tr' a H5).
            eauto.
          }
          assert(stratDrive from delta_usr addrs_usr mid tr' to tr'').
          {
            unfold stratDrive.
            exists a , H4, H5.
            split.
            eauto.
            eauto.
          }
          eapply ISU_Step in H8;eauto.
          assert (multiStratDrive delta_env addrs_env from to tr'' to tr'' 0).
          eapply MS_Refl.
          eapply ISE_Step in H9;eauto.
        Qed.


    Lemma stratDrive_reachable_via :
      forall (s0 s s' : ChainState) tr_s delta addrs c caddr tr_s' ,
        transition_reachable c caddr s0 s ->
        stratDrive s0 delta addrs s tr_s s' tr_s' ->
        reachable_via c caddr s0 s s'.
    Proof.
      intros s0 s s' tr_s delta addrs c caddr tr_s' H_transition_reachable H_stratDrive.
      unfold stratDrive in H_stratDrive.
      destruct_and_split.
      eapply transition_trans_through;eauto.
    Qed.

  Lemma UserLiquidatesNSteps_can_reachable_via :
    forall delta_usr delta_env addrs_usr addrs_env c caddr s0 s s' tr_s tr_s' ,
      is_init_state c caddr s0 ->
      wellStrat delta_usr addrs_usr c caddr s0 ->
      wellStrat delta_env addrs_env c caddr s0->
      UserLiquidatesNSteps delta_usr addrs_usr delta_env addrs_env caddr s0 s  tr_s s' tr_s' ->
      reachable_via c caddr s0 s s'.
  Proof.
    intros * Hinit Hwell_usr Hwell_env Husr_liq.
    eapply (env_mut delta_usr addrs_usr delta_env addrs_env caddr s0 
        (fun s tr_s  s' tr_s' (_ : envProgress_Mutual delta_usr addrs_usr delta_env addrs_env caddr  s0 s tr_s  s' tr_s') => is_init_state c caddr s0 -> reachable_via c caddr s0 s s')
        (fun  s tr_s  s' tr_s' (_ : UserLiquidatesNSteps delta_usr addrs_usr delta_env addrs_env caddr  s0 s tr_s  s' tr_s') => is_init_state c caddr s0 -> reachable_via c caddr s0 s s')
        );intros;eauto.
        - intros.
          specialize(H3 s1 tr 0).
          eapply H3;eauto.
          eapply MS_Refl.

        - specialize(H3 H4).
          unfold stratDrive  in s2.
          decompose_exists.
          assert(reachable_via c caddr s0 s1 s'0).
          {
            assert(transition_reachable c caddr s0 s1).
            {
              econstructor;eauto.
            }
            eapply transition_trans_through in H5;eauto.
          }
          eauto.
    Qed.

  Lemma UserLiquidatesNSteps_can_liquid :
    forall delta_usr delta_env addrs_usr addrs_env c caddr s0 s s' tr_s tr_s' ,
      is_init_state c caddr s0 ->
      wellStrat delta_usr addrs_usr c caddr s0->
      wellStrat delta_env addrs_env c caddr s0->
      UserLiquidatesNSteps delta_usr addrs_usr delta_env  addrs_env  caddr s0 s tr_s  s' tr_s' ->
      funds s' caddr = 0%Z.
  Proof.
    intros * Hinit Hwell_usr Hwell_env Husr_liq.
    eapply (env_mut delta_usr addrs_usr delta_env addrs_env caddr s0
        (* P : For interleavedExecutionEnv *)
        (fun s tr_s  s' tr_s' (_ : envProgress_Mutual delta_usr addrs_usr delta_env addrs_env caddr  s0 s tr_s  s' tr_s') =>
        funds s' caddr = 0%Z)
        (* P0 : For interleavedExecutionUsr *)
        (fun s tr_s  s' tr_s' (_ : UserLiquidatesNSteps delta_usr addrs_usr delta_env addrs_env caddr  s0 s tr_s  s' tr_s') =>
        funds s' caddr = 0%Z)
        );eauto.
    - intros.
      specialize(H3 s1 tr 0).
      eapply H3.
      eapply MS_Refl.
  Qed.


  Lemma transition_reachable_stratDrive_transition_reachable_through:
    forall s0 s tr_s  delta s' c  caddr tr' addrs,
      transition_reachable c caddr s0 s ->
      stratDrive s0 delta addrs s tr_s s' tr' ->
      reachable_via c caddr s0 s s'.
  Proof.
    intros * H_transition_reachable H_stratDrive.
    unfold stratDrive in H_stratDrive.
    destruct_and_split.
    assert(HReachable:  transition_reachable c caddr s0 s) by eauto.
    eapply transition_trans_through.
    eauto.
    eauto.
  Qed.

    
  Lemma queue_isb_empty_true : 
    forall bstate,
      queue_isb_empty bstate = true ->
      chain_state_queue bstate = [].
  Proof.
    intros * H_empty.
    unfold queue_isb_empty in H_empty.
    destruct (chain_state_queue bstate);try congruence;eauto.
  Qed.  

  Lemma empty_true_queue_isb : 
  forall bstate,
    chain_state_queue bstate = [] ->
    queue_isb_empty bstate = true .
  Proof.
    intros * H_empty.
    unfold queue_isb_empty.
    rewrite H_empty;eauto.
  Qed.  

  Lemma transition_next_state_queue_empty : 
    forall (s s' : ChainState)  a (tr_s : trace(s)),
      transition s a = Ok s' ->
      s'.(chain_state_queue) = [].
  Proof.
    intros * tr_s H_transition.
    unfold transition in H_transition.
    destruct (queue_isb_empty s) eqn : H_queue;try congruence.
    destruct (is_call_act a) eqn : H_call ;try congruence.
    destruct (add_block_exec true s (get_valid_header s) [a]) eqn : H_exec;try congruence.
    eapply add_block_next_state_queue_empty in H_exec;eauto.
    inversion H_transition;subst. eauto.
  Qed.



  Lemma transition_reachable_prev_next_trace : 
  forall (s s' : ChainState) (tr_s : trace(s)) a,
    reachable s ->
    s.(chain_state_queue) = [] ->
    transition s a = Ok s' ->
    ChainTrace s s'.
  Proof.
    intros.
    decompose_transition H5.
    eapply add_block_reachable_through_aux in Hexec;eauto.
    (* eapply add_block_reachable_through_aux in Hexec;eauto. *)
  Qed.


  Lemma ttrace_with_trace:
    forall s (tr_s:trace(s))  s',
      reachable s ->
      TransitionTrace s s' ->
      ChainTrace s s'.
  Proof.
    intros.
    induction X.
    eauto.
    assert(ChainTrace from mid).
    {
    apply IHX in H3.
    eauto.
    eauto.
    }
    inversion l.
    eapply transition_reachable_prev_next_trace in H5.
    apply (clist_app X0 H5).
    apply (clist_app  tr_s X0).
    eapply reachable_trans;eauto.
    unfold transition in H5.
    destruct (queue_isb_empty mid) eqn :H_queue;try congruence.
    eapply queue_isb_empty_true in H_queue.
    eauto.
  Qed.

  Lemma ttreachable_to_reachable:
    forall (s0 s s' : ChainState) c caddr,
        is_init_state c caddr s0 ->
        transition_reachable c caddr s0 s ->
        reachable s.
  Proof.
    intros.
    decompose_is_init_state H3.
    decompose_transition_reachable H4.
    decompose_is_init_state init_bstate.
    assert(H_t : reachable s0) by eauto.
    destruct H_t as [tr_s0].
    assert(ChainTrace s0 s).
    {
      eapply ttrace_with_trace;eauto.
    }
    eapply reachable_trans;eauto.
  Qed.

  Lemma tthrough_to_reachable_through:
    forall (s0 s s' : ChainState) c caddr,
      is_init_state c caddr s0 ->
      reachable_via c caddr s0 s s' ->
      reachable_through s s'.
  Proof.
    intros.
    assert(reachable_via c caddr s0 s s') by eauto.
    decompose_reachable_via H5.
    assert(reachable s).
    {
      eapply ttreachable_to_reachable;eauto.
    }
    clear H_reachable.
    decompose_is_init_state H3.
    assert(reachable s) by eauto.
    destruct H5 as [trace'].
    assert(ChainTrace s s').
    {
      eapply ttrace_with_trace in tr;eauto. 
    }
    econstructor;eauto.
  Qed.

  Lemma readyToStepState_stratDrive_readyToStepState :
    forall (s0 s s' : ChainState) (tr_s : trace(s0,s)) contract caddr delta tr_s' addrs,
      readyToStepState  contract caddr s0 s  ->
      stratDrive s0 delta addrs  s  tr_s s' tr_s' ->
      readyToStepState contract caddr s0 s'.
  Proof.
    intros.
    unfold readyToStepState.
    split.
    eapply transition_reachable_stratDrive_transition_reachable_through in H4;eauto.
    unfold readyToStepState in H3.
    destruct_and_split;eauto.
    unfold stratDrive in H4.
    destruct_and_split.
    assert (transition s x = Ok s') by eauto.
    unfold readyToStepState  in H3.
    destruct H3.
    decompose_transition_reachable H3.
    unfold is_init_state in init_bstate.
    destruct init_bstate.
    destruct H3.
    assert(trace(s)).
    {
      assert(trace( s0, s)) by eauto.
      eapply ttrace_with_trace in X0;eauto.
      eauto.
      eapply (clist_app X X0).
      econstructor; eauto.
    }
    eapply transition_next_state_queue_empty in H6;eauto.
  Qed.


  Ltac decompose_TransitionStep H :=
    inversion H as [a Hcall_to_caddr Htrans ];
    subst;
    clear H.


    Lemma readyToStepState_multiStratDrive_readyToStepState:
      forall (s0 s s' : ChainState) (tr : trace(s0,s)) (delta : strat) addrs contract caddr tr' n,
        readyToStepState contract caddr s0 s  ->
        multiStratDrive delta addrs s0 s tr s' tr' n ->
        readyToStepState contract caddr s0 s'  .
    Proof.
        intros.
        induction H4;eauto.
        eapply readyToStepState_stratDrive_readyToStepState in H5;eauto.
    Qed.

    Lemma readyToStepState_interleavedExecution_readyToStepState:
      forall (delta_usr delta_env : strat) (addrs_usr addrs_env : list Address) (s0 s : ChainState) (tr : TransitionTrace s0 s) (s' : ChainState) (tr' : TransitionTrace s0 s') contract caddr flag,
        readyToStepState contract caddr s0 s ->
        interleavedExecution delta_usr addrs_usr delta_env addrs_env s0 s tr flag s' tr' ->
        readyToStepState contract caddr s0 s'.
    Proof.
      intros delta_usr delta_env addrs_usr addrs_env s0 s tr s' tr' contract caddr flag H_readyToStepState H_interaction .
      induction H_interaction;eauto.
      (* - eapply readyToStepState_timeDrive_readyToStepState in H3;eauto. *)
      - eapply readyToStepState_multiStratDrive_readyToStepState in H3;eauto.
      (* - eapply readyToStepState_multiStratDrive_readyToStepState in H3;eauto.  *)
      - eapply readyToStepState_stratDrive_readyToStepState in H3;eauto.
    Qed.

    Lemma is_delta_empty_max_succ:
      forall delta addrs n,
        is_empty_strat delta addrs ->
        strat_finite delta addrs n.
    Proof.
      intros.
      unfold strat_finite.
      intros.
      unfold is_empty_strat in H3.
      specialize(H3 s0 s tr).
      unfold maxMultiStratDrive.
      exists 0, s, tr .
      split.
      unfold maxMultiStratDriveSteps.
      lia.
      split.
      eapply MS_Refl.
      eauto.


    Qed.


    Lemma readyToStepState_multiStratDrive_reachable_via:
    forall (s0 s s' : ChainState) (delta : strat) addrs c caddr tr tr' n,
      readyToStepState c caddr s0 s   ->
      multiStratDrive delta addrs s0 s tr s' tr' n ->
      reachable_via c caddr s0 s s'.
    Proof.
        intros.
        assert(Hacs:readyToStepState c caddr s0 s ) by eauto.
        unfold readyToStepState in H3.
        destruct_and_split.
        induction H4;eauto.
        assert (reachable_via c caddr s0 s' s'').
        {
          eapply stratDrive_reachable_via.
          eauto.
          eauto.    
        }
        assert(Hsss:stratDrive s0 delta addrs s'  tr' s''  tr'') by eauto.
        unfold stratDrive in H7.
        destruct H7.
        destruct_and_split.
        assert(reachable_via c caddr s0 s s') by eauto.
        unfold reachable_via in H9.
        destruct H9.
        destruct H10 as [trace].
        set(t_trace := clist_app tr trace).
        destruct H8 as [trace'].
        unfold reachable_via.
        split.
        eauto.
        econstructor.
        eapply (clist_app trace trace').
    Qed.

    Lemma transition_reachable_readyToStepState: 
    forall s0 s c caddr,
      is_init_state c caddr s0 ->
      transition_reachable c caddr s0 s ->
      readyToStepState c caddr s0 s .
    Proof.
      intros * H_init H_transition_reachable.
      unfold readyToStepState.
      split.
      eauto.
      decompose_transition_reachable H_transition_reachable. 
      induction trace.
      - decompose_is_init_state H_init.
        eauto.
      - intuition.
        rename H4 into H_mid_queue.
        decompose_is_init_state H_init.
        assert(H_t : reachable from) by eauto.
        destruct H_t as [tr_from].
        inversion l as [a H_call H_trans ].
        + eapply transition_next_state_queue_empty in H_trans;eauto.
          eapply ttrace_with_trace in trace;eauto.
          unfold is_init_state in H_init.
          destruct_and_split.
          eapply (clist_app tr_from trace).
    Qed.

    Lemma reachable_via_multiStratDrive_reachable_via:
    forall (s0 s s' s'' : ChainState) (delta : strat) addrs c caddr tr' tr'' n,
      reachable_via c caddr s0 s s'  ->
      multiStratDrive delta addrs s0 s' tr' s'' tr'' n ->
      reachable_via c caddr s0 s s''.
    Proof.
      intros * H_reachable_via H_multi.
      assert(H_t:reachable_via c caddr s0 s s') by eauto.
      decompose_reachable_via H_t.
      rename tr into tr_s_s'.
      decompose_transition_reachable H_reachable.
      assert(transition_reachable c caddr s0 s) by eauto.
      assert(is_init_state c caddr s0) by eauto.
      decompose_is_init_state H4.
      assert(readyToStepState c caddr s0 s' ).
      {
        eapply transition_reachable_readyToStepState;eauto.
      }
      assert(readyToStepState c caddr s0 s ).
      {
        eapply transition_reachable_readyToStepState;eauto.
      }
      eapply readyToStepState_multiStratDrive_reachable_via in H_multi;eauto.
    Qed.


    Lemma reachable_via_stratDrive_reachable_via :
      forall s0 s s' s'' tr' tr'' delta addrs c caddr,
        reachable_via c caddr s0 s s' ->
        stratDrive s0 delta addrs s'  tr' s''  tr'' ->
        reachable_via c caddr s0 s s''.
    Proof.
      intros * H_reachable_via H_stratDrive.
      assert(H_t : reachable_via c caddr s0 s s') by eauto.
      decompose_reachable_via H_t.
      unfold reachable_via.
      split.
      rename tr into tr_s_s'.
      rename H_reachable into H_reachable_s.
      decompose_reachable_via H_reachable_via.
      eauto.
      assert(trace(s,s)).
      {
        apply clnil.
      }
      decompose_stratDrive H_stratDrive.
      destruct_and_split.
      assert(step := (step_trans a H_transition H_in)).
      econstructor.
      eapply (snoc tr step).
    Qed.


    Lemma BL_implies_SL_with_empty_env_and_complete_user:
      forall delta_usr delta_env addrs_usr addrs_env c caddr s0,
        is_init_state c caddr s0 ->
        is_empty_strat delta_env addrs_env->
        is_complete_strategy delta_usr addrs_usr c caddr s0->
        strat_liquidity delta_usr addrs_usr delta_env addrs_env caddr c s0 ->
        base_liquidity c caddr s0.
    Proof.
      intros * H_init H_empty H_complete H_liquidity.
      unfold base_liquidity.
      intros.
      assert(trace(s0,s0)).
      {
        eapply clnil.
      }
      unfold readyToStepState in H4.
      destruct H4 as [Htr_reachable Hqueue].
      assert(H':transition_reachable c caddr s0 s) by eauto.
      eapply (transition_reachable_can_Inter_usr_all s0 s X c caddr delta_usr delta_env)in H';eauto.
      destruct H'.
      unfold strat_liquidity in H_liquidity.
      assert(Hwell : wellDefinedSystem delta_usr addrs_usr delta_env addrs_env caddr c s0).
      {
        unfold wellDefinedSystem.
        split.
        eapply delta_all_is_wellStrat;eauto.
        split.
        eapply delta_empty_is_wellStrat;eauto.
        split.
        
        eapply is_delta_empty_max_succ;eauto.
        eauto.
      }
      specialize(H_liquidity Hwell X s x).
      rename X into tr_s0.
      rename x into tr_s.
      unfold isReachableUnderInterleavedExecution in H_liquidity.
      specialize(H_liquidity H4).
      decompose_exists.
      assert(UserLiquidatesNSteps delta_usr addrs_usr delta_env addrs_env caddr s0
      s tr_s x x0) by eauto.
      eapply UserLiquidatesNSteps_can_reachable_via in H5;eauto.
      eapply UserLiquidatesNSteps_can_liquid in H_liquidity;eauto;eauto.
      exists x.
      unfold reachable_via  in H5.
      destruct_and_split.
      eauto.
      lia.
      eapply delta_all_is_wellStrat;eauto.
      eapply delta_empty_is_wellStrat;eauto.
      eapply delta_all_is_wellStrat;eauto.
      eapply delta_empty_is_wellStrat;eauto.
    Qed.

    Lemma activest_interactionSuccession_reachable_via delta_usr addrs_usr delta_env addrs_env c caddr:
    forall s0 s s' tr tr' flag,
      readyToStepState c caddr s0 s  ->
      interleavedExecution delta_usr addrs_usr delta_env addrs_env s0 s tr flag s' tr' ->
      reachable_via c caddr s0 s s'.
      Proof.
      intros s0 s s' tr  tr' flag H_activest H_interaction.
      assert(transition_reachable c caddr s0 s).
      {
        unfold readyToStepState in H_activest.
        destruct_and_split.
        eauto.
      }
      induction H_interaction;eauto.
      (* - eapply reachable_via_timeDrive_reachable_via in H6;eauto. *)
      - eapply reachable_via_multiStratDrive_reachable_via in H4;eauto.
      - eapply reachable_via_stratDrive_reachable_via in H4;eauto.
    Qed.

    Lemma multiSuccTrace_trans :
      forall delta addrs s0 s1 s2 tr0 tr1 tr2 n m,
        multiStratDrive delta addrs s0 s0 tr0 s1 tr1 n ->
        multiStratDrive delta addrs s0 s1 tr1 s2 tr2 m->
        multiStratDrive delta addrs s0 s0 tr0 s2 tr2 (n + m).
    Proof.
      clear H H0 H1 H2.
      intros delta addrs s0 s1 s2 tr0 tr1 tr2 n m H1 H2.
      induction H2.
      - (* Case MS_Refl *)
        (* Since s1 = s2 and tr1 = tr2 *)
        assert(n + 0 = n) by lia.
        rewrite H.
        assumption.
      (* - Case multiStratDrive_end
        apply multiStratDrive_end with (s' := s') (tr' := tr').
        + lia.
        + eapply IHm0.
          assumption.
        + assumption. *)
      - (* Case MS_Step *)
        assert(multiStratDrive delta addrs s0 s0 tr0 s'' tr''  (n + count + 1)).
        {
          eapply MS_Step with (s' := s') (s'' := s'') (tr' := tr') (tr'' := tr'') (count := n + count).
          + apply IHm0; assumption.
          + assumption.
        }
        assert((n + count + 1) = (n + (count + 1))) by lia.
        rewrite <- H3.
        eauto.
    Qed.

  Lemma multiStratSucc_n_zero_s_eq:
  forall s0 s s' tr tr' n delta addrs,
    multiStratDrive delta addrs s0 s tr s' tr' n -> 
    n = 0 ->
    s = s' /\ existT s tr = existT s' tr'.
Proof.
  intros.
  induction H3;eauto;try lia.
Qed.


  Lemma SL_implies_BL_with_empty_env_and_complete_user:
    forall delta_usr delta_env addrs_usr addrs_env c caddr s0,
      is_empty_strat delta_env addrs_env ->
      is_complete_strategy delta_usr addrs_usr c caddr s0 ->
      base_liquidity c caddr s0 ->
      strat_liquidity delta_usr addrs_usr delta_env addrs_env caddr c s0.
  Proof.
      intros * Henv_empty Husr_complete Hbase_liq.
      unfold base_liquidity in Hbase_liq.
      unfold strat_liquidity.
      intros.
      rename H3 into Hwell_sys.
      rename tr into tr_s0_s0.
      rename tr' into tr_s0_s'.
      rename H4 into H_interleaved.
      decompose_wellDefinedSystem Hwell_sys.
      specialize(Hbase_liq s' H_init).
      assert(Hready_state_s':readyToStepState c caddr s0 s' ).
      {
        unfold readyToStepState.
        split.
        assert(transition_reachable c caddr s0 s').
        {
        unfold transition_reachable.
        split.
        eauto.
        econstructor.
        eauto.
        }
        eauto.
        assert(transition_reachable c caddr s0 s').
        {
          unfold transition_reachable.
          split.
          eauto.
          econstructor.
          eauto.
        }
        eapply (transition_reachable_readyToStepState s0 s' c) in H3;eauto.
        unfold readyToStepState in H3.
        destruct_and_split.
        eauto.
      }
      specialize (Hbase_liq Hready_state_s').
      destruct Hbase_liq as [s'' [H_reach H_s''_funds]].
      assert(Hvia_s'_s' : reachable_via c caddr s0 s' s').
      {
        unfold readyToStepState in Hready_state_s'.
        destruct_and_split.
        econstructor;eauto.
        econstructor;eauto.
        eapply clnil.
      }
      assert(H_t : reachable_via c caddr s0 s' s'').
      {
        econstructor;eauto.
      }
      unfold reachable_via in H_t.
      destruct H_t as [Hrc_s' [tr_s'_s'']].
      assert(tr_s0_s'' : trace(s0,s'')).
      {
        eapply (clist_app tr_s0_s' tr_s'_s'').
      }
      assert(traux_s'_s'' : aux_trace s' s'').
      {
        eapply cl_to_pt_lm.
        eauto.
      }
      induction traux_s'_s''.
      (* - exists (time_speed + time_speed). *)
      -  exists p.
        exists tr_s0_s'.
        eapply ULM_Base;eauto.
      - destruct ((funds mid caddr =? 0)%Z) eqn:H_mid_funds;propify.
        + 
          exists mid.
          assert(tl : TransitionStep from mid) by eauto.
          decompose_TransitionStep tl.
          * set(tr_s0_mid:= snoc tr_s0_s' (step_trans a Hcall_to_caddr Htrans)).
            exists (tr_s0_mid).
            eapply (ULM_Step delta_usr addrs_usr delta_env addrs_env caddr s0 from tr_s0_s' mid mid (snoc tr_s0_s' (step_trans a Hcall_to_caddr Htrans)) tr_s0_mid) ;eauto;try lia.
            **  econstructor;eauto.
                exists Hcall_to_caddr, Htrans.
                split.
                unfold is_complete_strategy in Husr_complete.
                destruct Husr_complete as [Hwell_usr Hact_in].
                specialize(Hact_in from mid tr_s0_s' a Htrans).
                eauto.
                eauto.
            **  eapply EPM_Base.
                eauto.
        + assert(H_mid_funds_gt_zero : (funds mid caddr > 0)%Z ).
          {
            assert(tr_s0_mid :trace(s0,mid)) by eapply (snoc tr_s0_s' l).
            assert (H_t:is_init_state c caddr s0) by eauto.
            decompose_is_init_state H_init.
            assert(tr_s0 : reachable s0) by eauto.
            destruct tr_s0 as [tr_s0].
            assert(Hrc_mid : reachable mid).
            {
              eapply ttrace_with_trace in tr_s0_mid;eauto.
              econstructor;eauto.
              eapply (clist_app tr_s0 tr_s0_mid).
            }
            assert(H_fund_non_neg : (funds mid caddr >= 0)%Z).
            {
              eapply reachable_funds_nonnegative;eauto.
            }
            lia.
          }
          assert(tr_mid_to:trace(mid,to)).
          {
            eapply pt_to_cl_lm.
            eauto.
          }
          assert(tr_s0_mid : trace(s0,mid)) by eapply (snoc tr_s0_s' l).
          assert(step_from_mid : TransitionStep from mid) by eauto.
          assert(Hvia_mid_to : reachable_via c caddr s0 mid to).
          {
            unfold reachable_via in Hvia_s'_s'.
            destruct_and_split.
            destruct H4 as [tr_s_from].
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
          assert(Hready_mid : readyToStepState c caddr s0 mid).
          {
            eapply transition_reachable_readyToStepState;eauto.
          }
          assert(tl:TransitionStep from mid) by eauto.
          decompose_TransitionStep tl.
          * set(sn_tr_s0_mid:= snoc tr_s0_s' (step_trans a Hcall_to_caddr Htrans)).
            assert(Hinter:interleavedExecution delta_usr addrs_usr delta_env addrs_env s0 s0 tr_s0_s0 Tenv mid sn_tr_s0_mid).
            {
              eapply (ISU_Step delta_usr addrs_usr delta_env addrs_env s0 s0 tr_s0_s0 from mid tr_s0_s' sn_tr_s0_mid).
              intuition.
              unfold stratDrive.
              exists a,Hcall_to_caddr, Htrans.
              split.

              unfold is_complete_strategy in Husr_complete.
              destruct_and_split.
              specialize(H4 from mid tr_s0_s' a Htrans).
              destruct_and_split.
              eauto.
              eauto.
            }
            assert(His_r_inter:isReachableUnderInterleavedExecution delta_usr delta_env addrs_usr
            addrs_env s0 tr_s0_s0 mid sn_tr_s0_mid).
            {
              unfold isReachableUnderInterleavedExecution.
              eauto.
              assert(multiStratDrive delta_env addrs_env s0 mid sn_tr_s0_mid mid sn_tr_s0_mid 0) by eapply MS_Refl.
              eapply ISE_Step;eauto.
              (* eapply (empty_strat_passive s0 mid sn_tr_s0_mid)  in Henv_empty.
              unfold passive_delta in Henv_empty.
              rewrite  Henv_empty.
              intuition. *)
            }
            assert(Hvia_mid_mid : reachable_via c caddr s0 mid mid).
            {
              econstructor.
              eauto.
              econstructor.
              apply clnil.
            }
            assert(Htc_mid: transition_reachable c caddr s0 mid).
            {
              econstructor;eauto.
            }
            assert(Hihb_mid_to:inhabited (trace( mid, to))) by eauto.
            specialize(IHtraux_s'_s'' Hihb_mid_to H_s''_funds sn_tr_s0_mid His_r_inter Hready_mid Hvia_mid_mid Htc_mid tr_mid_to tr_s0_to).
            decompose_exists.
            rename x0 into x1.
            rename x into x0.
            
            (* exists (n+1). *)
            exists x0, x1.
            rename tr_s0_s' into tr_s0_from.
            eapply (ULM_Step delta_usr addrs_usr delta_env addrs_env caddr s0 from tr_s0_from mid x0 (snoc tr_s0_from (step_trans a Hcall_to_caddr Htrans)) x1) ;eauto;try lia.
            unfold stratDrive.
            exists a,Hcall_to_caddr, Htrans.
            intuition.
            unfold is_complete_strategy  in Husr_complete.
            destruct Husr_complete.
            specialize(H4 from mid tr_s0_from a Htrans).
            destruct_and_split.
            eauto.
            eauto.
            eapply EPM_Step.
            eauto.
            intros.
            pose proof H3.
            eapply multiSuccTrace_delta_empty_refl_multr in H3;eauto.
            destruct_and_split.
            eapply multiStratSucc_n_zero_s_eq in H4;eauto.
            destruct_and_split.
          subst.
          inversion H6.
          eauto.
            
  Qed.
     
  Lemma SL_equiv_BL_with_empty_env_and_complete_user:
    forall delta_usr delta_env addrs_usr addrs_env c caddr s0,
      is_init_state c caddr s0 ->
      is_empty_strat delta_env addrs_env ->
      is_complete_strategy delta_usr addrs_usr c caddr s0 ->
      base_liquidity c caddr s0 <->
      strat_liquidity delta_usr addrs_usr delta_env addrs_env caddr c s0.
  Proof.
    intros.
    split.
    intros.
    eapply SL_implies_BL_with_empty_env_and_complete_user;eauto.
    intros.
    eapply BL_implies_SL_with_empty_env_and_complete_user;eauto.
  Qed.

  Definition not_base_liquidity 
  (c : Contract Setup Msg State Error)
  (caddr : Address)
  (s0 : ChainState) := 
    is_init_state c caddr s0 -> 
    exists s, 
    (readyToStepState c caddr s0 s /\ 
      forall s', 
      ~(inhabited(trace(s ,s')) /\ funds s' caddr = 0)%Z).


Lemma base_liquidity_equiv_not_base_liquidity :
  forall c caddr s0,
  is_init_state c caddr s0 ->
  base_liquidity c caddr s0 ->
    ~ not_base_liquidity c caddr s0 .
Proof.
  intros c caddr s0 Hbase Hnot_base.
  unfold base_liquidity  in Hnot_base.
  unfold not_base_liquidity .
  unfold not.
  intros.
  specialize(H3 Hbase).
  destruct_and_split.
  specialize(Hnot_base x Hbase H3).
  destruct_and_split.
  specialize(H4 x0).
  destruct_and_split.
  eapply H4.
  eauto.
Qed.

Section normal.

  Lemma reachable_via_impl_contract_deployed:
    forall c caddr s0 s s',
      is_init_state c caddr s0 ->
      reachable_via c caddr s0 s s' ->
      env_contracts s' caddr = Some (c : WeakContract).
  Proof.
    intros.
    decompose_is_init_state H3.
    assert(H_reachable_t : reachable s0) by eauto.
    destruct H_reachable_t as [tr0].
    decompose_reachable_via H4.
    decompose_transition_reachable H_reachable0.
    eapply ttrace_with_trace in tr, trace;eauto.
    assert(reachable_through s0 s').
    {
      econstructor;eauto.
      econstructor;eauto.
      eapply (clist_app trace tr).
    }
    eapply reachable_through_contract_deployed in H3;eauto.
    eapply ttrace_with_trace in trace;eauto.
    eapply (clist_app tr0 trace).
    eapply ttrace_with_trace in trace;eauto.
    econstructor;eauto.
    eapply (clist_app tr0 trace).
  Qed.
    
  Lemma reachable_via_impl_contract_state:
    forall c caddr s0 s s',
      is_init_state c caddr s0 ->
      reachable_via c caddr s0 s s' ->
      exists cstate,
        env_contract_states s' caddr = Some cstate.
  Proof.
    intros.
    decompose_is_init_state H3.
    assert(H_reachable_t : reachable s0) by eauto.
    destruct H_reachable_t as [tr0].
    decompose_reachable_via H4.
    decompose_transition_reachable H_reachable0.
    eapply ttrace_with_trace in tr, trace;eauto.
    assert(reachable_through s0 s').
    {
      econstructor;eauto.
      econstructor;eauto.
      eapply (clist_app trace tr).
    }
    eapply reachable_through_contract_state in H_env_states;eauto.
    eapply ttrace_with_trace in trace;eauto.
    eapply (clist_app tr0 trace).
    eapply ttrace_with_trace in trace;eauto.
    econstructor;eauto.
    eapply (clist_app tr0 trace).
  Qed.

  Lemma reachable_via_impl_reachable_through:
    forall c caddr s0 s s',
      is_init_state c caddr s0 ->
      reachable_via c caddr s0 s s' ->
      reachable_through s s'.
  Proof.
    intros.
    decompose_is_init_state H3.
    assert(H_reachable_t : reachable s0) by eauto.
    destruct H_reachable_t as [tr0].
    decompose_reachable_via H4.
    decompose_transition_reachable H_reachable0.
    pose proof H_reachable.
    destruct H_reachable as [tr_s].
    eapply ttrace_with_trace in tr, trace;eauto.
    econstructor;eauto.
    econstructor;eauto.
    eapply (clist_app tr0 trace).
    eapply ttrace_with_trace in trace;eauto.
    eapply (clist_app tr0 trace).
    eapply ttrace_with_trace in trace;eauto.
    econstructor;eauto.
    eapply (clist_app tr0 trace).
  Qed.

  Lemma transition_reachable_impl_reachable_through:
    forall c caddr s0 s,
      is_init_state c caddr s0 ->
      transition_reachable c caddr s0 s ->
      reachable_through s0 s.
  Proof.
    intros.
    decompose_is_init_state H3.
    assert(H_reachable_t : reachable s0) by eauto.
    destruct H_reachable_t as [tr0].
    decompose_transition_reachable H4.
    eapply ttrace_with_trace in trace;eauto.
    econstructor;eauto.
  Qed.

  Lemma transition_reachable_impl_reachable:
    forall c caddr s0 s,
      is_init_state c caddr s0 ->
      transition_reachable c caddr s0 s ->
      reachable s.
  Proof.
    intros.
    decompose_is_init_state H3.
    assert(H_reachable_t : reachable s0) by eauto.
    destruct H_reachable_t as [tr0].
    decompose_transition_reachable H4.
    eapply ttrace_with_trace in trace;eauto.
    econstructor;eauto.
    eapply (clist_app tr0 trace).
  Qed.

  Lemma reachable_via_impl_reachable:
    forall c caddr s0 s s',
      is_init_state c caddr s0 ->
      reachable_via c caddr s0 s s' ->
      reachable s'.
  Proof.
    intros.
    decompose_is_init_state H3.
    assert(H_reachable_t : reachable s0) by eauto.
    destruct H_reachable_t as [tr0].
    decompose_reachable_via H4.

    decompose_transition_reachable H_reachable0.
    eapply ttrace_with_trace in tr, trace;eauto.
    econstructor;eauto.
    assert(trace' : ChainTrace s0 s').
    {
    eapply (clist_app trace tr).
    }
    eapply (clist_app tr0 trace').
    eapply ttrace_with_trace in trace;eauto.
    eapply (clist_app tr0 trace).
    eapply ttrace_with_trace in trace;eauto.
    econstructor;eauto.
    eapply (clist_app tr0 trace).
  Qed.


  Lemma readyToStepState_transition_readyToStepState:
  forall (s0 s s' : ChainState) a c caddr,
    readyToStepState c caddr s0 s  ->
    transition s a = Ok s' ->
    readyToStepState c caddr s0 s'  .
  Proof.
    intros.
    unfold readyToStepState in *.
    destruct_and_split.
    decompose_transition_reachable H3.
    assert(trace( s, s')).
    {
      econstructor;eauto.
      pose proof H4.
      decompose_transition H3.
      (* eapply is_wait_act_vo_true_a in Hcond0.
      subst.
      eapply (step_time H4). *)
      eapply (step_trans a Hcall H4).
    }
    econstructor;eauto.
    assert(trace(s0,s')).
    {
      eapply (clist_app trace X).
    }
    econstructor;eauto.
    assert(transition_reachable c caddr s0 s ) by eauto.
    eapply transition_reachable_impl_reachable in H3.
    destruct H3 as [trace].
    eapply transition_next_state_queue_empty in H4;eauto.
    decompose_transition_reachable H3.
    eauto.
  Qed.

  Lemma readyToStepState_ttrace_readyToStepState:
  forall (s0 s s' : ChainState) (tr_s : trace(s0,s)) contract caddr,
    is_init_state contract caddr s0 ->
    readyToStepState contract caddr s0 s.
  Proof.
    intros.
    unfold readyToStepState.
    split.
    econstructor;eauto.
    induction tr_s.
    + decompose_is_init_state H3.
      eauto.
    + pose proof H3.
      eapply IHtr_s in H3.
      decompose_TransitionStep l.
      pose proof H4. 
      eapply init_ready in H4.
      assert ( readyToStepState contract caddr from mid).
      {
        unfold readyToStepState.
        split.
        econstructor;eauto.
        eauto.
      }
      eapply readyToStepState_transition_readyToStepState in Htrans;eauto.
      unfold readyToStepState in Htrans.
      destruct Htrans.
      eauto.

  Qed.

  Lemma address_not_contract_not_wc {to} (addr : Address):
    reachable to ->
    address_is_contract addr = false ->
    env_contracts to addr = None.
  Proof.
    intros [trace] contract_at_addr.
    remember empty_state eqn:eq.
    induction trace; rewrite eq in *; clear eq.
    - cbn in *; congruence.
    - destruct_chain_step;
      try now rewrite_environment_equiv.
      assert( env_contracts mid addr = None).
      eapply IHtrace;eauto.
    + 
      rewrite_environment_equiv; cbn in *; destruct_address_eq; subst; auto.
    +  destruct_action_eval; rewrite_environment_equiv; cbn in *;   
        destruct_address_eq; subst; auto.
        congruence.
  Qed.


End normal.


End Strat.


Global Ltac decompose_transition_reachable H :=
  unfold transition_reachable in H;
  destruct H as [init_bstate [trace]].


Global Ltac decompose_transition H :=
  unfold transition in H;
  repeat match type of H with
  | context[if queue_isb_empty ?state then _ else _] =>
      let Hqueue := fresh "Hqueue" in
      destruct (queue_isb_empty state) eqn:Hqueue; try congruence
  | context[if is_call_act ?act then _ else _] =>
      let Hcall := fresh "Hcall" in
      destruct (is_call_act act) eqn:Hcall; try congruence
  | context[let header := get_valid_header ?state in _] =>
      let Hheader := fresh "Hheader" in
      remember (get_valid_header state) as header eqn:Hheader
  | context[match add_block_exec ?mode ?state ?header ?acts with | Ok _ => _ | Err _ => _ end] =>
      let Hexec := fresh "Hexec" in
      destruct (add_block_exec mode state header acts) eqn:Hexec; try congruence
  | context[match ?res with | Ok _ => _ | Err _ => _ end] =>
      let Hres := fresh "Hres" in
      destruct res eqn:Hres; try congruence
  end;
  repeat match type of H with
  | Ok _ = Ok _ => inversion H; subst; clear H
  | Err _ = Err _ => inversion H; subst; clear H
  end.

Global Ltac decompose_reachable_via H :=
  match type of H with
  | reachable_via ?contract ?caddr ?s0 ?mid ?to =>
      unfold reachable_via in H;
      let H_reachable := fresh "H_reachable" in
      let tr := fresh "tr" in
      destruct H as [H_reachable H_trace];
      destruct H_trace as [tr] (* 只引入轨迹变量 tr，避免未使用的附加绑定 *)
  | _ => fail "The hypothesis" H "is not of the form reachable_via contract caddr s0 mid to."
  end.

Global Ltac decompose_is_init_state H :=
  match type of H with
  | is_init_state ?contract ?caddr ?init_state =>
      unfold is_init_state in H;
      let H_reachable := fresh "H_reachable" in
      let H_queue := fresh "H_queue" in
      let H_env_contracts := fresh "H_env_contracts" in
      let H_env_details := fresh "H_env_details" in
      destruct H as [H_reachable [H_queue [H_env_contracts H_env_details]]];
      let ctx := fresh "ctx" in
      let setup := fresh "setup" in
      let state := fresh "state" in
      let H_env_states := fresh "H_env_states" in
      let H_init := fresh "H_init" in
      destruct H_env_details as [ctx [setup [state [H_env_states H_init]]]]
  | _ => fail "The hypothesis" H "is not of the form is_init_state contract caddr init_state."
  end.


Global Ltac decompose_exists :=
    repeat match goal with
            | [ H : exists _, _ |- _ ] =>
                let x := fresh "x" in
                destruct H as [x H]
            end.

Global  Ltac decompose_stratDrive H :=
    match type of H with
    | stratDrive ?s0 ?delta ?addrs ?s ?tr ?s' ?tr' =>
        unfold stratDrive in H;
        let a := fresh "a" in
        let H_trans := fresh "H_transition" in
        destruct H as [a [H_trans [H_in H_trace]]]
    | _ => fail "The hypothesis" H "is not of the form stratDrive s0 delta addrs s tr s' tr'."
    end.


Global Ltac solve_facts :=
  repeat match goal with
    | H := ?f : nat -> nat -> nat -> nat -> nat -> nat -> Prop |- _ =>
        is_evar f; instantiate (H := fun _ _ _ _ _ _ => Logic.True)
    | H := ?f : _ -> ContractCallContext -> Prop |- _ =>
        is_evar f; instantiate (H := fun _ _ => Logic.True)
    | H := ?f : Chain -> ContractCallContext -> _ ->
    list ActionBody -> option (list (ContractCallInfo _)) -> Prop |- _ =>
        is_evar f; instantiate (H := fun _ _ _ _ _ => Logic.True)
    end;
    unset_all; subst;
    destruct_chain_step; [
       auto
     | destruct_action_eval; [
         auto
       | auto
       | auto; intros ?cstate ?deployed ?deployed_state;
          cbn; subst
       ]
    ].

Global Ltac decompose_wellStrat H :=
    unfold wellStrat in H;
    let Hs0 := fresh "Hs0" in
    let Hs := fresh "Hs" in
    let Htr_s := fresh "Htr_s" in
    intros Hs0 Hs Htr_s;
    match type of H with
    | context[let delta_actions := ?delta _ _ _ _ in _] =>
        let Hda := fresh "Hda" in
        set (delta_actions := delta _ _ _ _) in H;
        unfold delta_actions in H
    | _ => idtac
    end;
    match type of H with
    | _ -> Forall _ _ =>
        let Hq := fresh "Hq" in
        intros Hq; specialize (H Hq)
    | Forall _ ?l =>
        let Ha := fresh "Ha" in
        apply Forall_forall in H; intros Ha
    | _ => idtac
    end.
