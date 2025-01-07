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
Require Import Strat.
From Coq Require Import List.
From Coq Require Import Bool.
From Coq Require Import ZArith.
From Coq Require Import Arith.
From Coq Require Import String.
Require Import Coq.NArith.BinNatDef.
Require Import Coq.Strings.Byte.
Require Import Coq.Sorting.Permutation.
Import ListNotations.
Require Import Lia.
Import RecordSetNotations.
From Coq Require Import Permutation.

Section CrowdfundWithFMap.

  (** 与之前类似的环境依赖 *)
  Context {BaseTypes : ChainBase}.
  Set Primitive Projections.
  Set Nonrecursive Elimination Schemes.
  Context {AddrSize : N}.
  Local Open Scope Z.

  (***********************************************************)
  (** * 1. 定义合约内部用到的类型与状态                     *)
  (***********************************************************)

  (** 与之前一致的合约阶段：等待筹款、筹款已达成、合约已关闭 *)
  Inductive CrowdfundPhase :=
  | AWAITING_FUNDS
  | FUNDS_REACHED
  | CLOSED.

  (** 定义合约状态。区别在于：使用 FMap K V 存 contributions *)
  Record State := build_state {
    admin          : Address;                (* 管理员地址 *)
    beneficiary    : Address;                (* 受益人地址 *)
    fundingGoal    : Amount;                 (* 筹款目标金额 *)
    totalFunds     : Amount;                 (* 当前筹集的总金额 *)
    isClosed       : bool;                   (* 合约是否已关闭 *)
    contributions  : FMap Address Amount;    (* 使用FMap管理贡献者映射 *)
  }.

  (** 初始化参数 [Setup] *)
  Record Setup := build_setup {
    setup_admin       : Address;
    setup_beneficiary : Address;
    setup_fundingGoal : Amount
  }.

  (***********************************************************)
  (** * 2. 定义消息类型与错误类型                            *)
  (***********************************************************)

  Inductive Msg :=
  | Donate
  | WithdrawFunds
  | ClearFunds
  | Refund.

  (***********************************************************)
  (** * 3. 序列化相关 *)
  (***********************************************************)

  Global Instance state_settable : Settable State :=
    settable! build_state
      <admin; beneficiary; fundingGoal; totalFunds; isClosed; contributions>.

  Global Instance setup_settable : Settable Setup :=
    settable! build_setup
      <setup_admin; setup_beneficiary; setup_fundingGoal>.

  Section Serialization.
    Global Instance State_serializable : Serializable State :=
      Derive Serializable State_rect<build_state>.

    Global Instance Setup_serializable : Serializable Setup :=
      Derive Serializable Setup_rect<build_setup>.

    Global Instance Msg_serializable : Serializable Msg :=
    Derive Serializable Msg_rect<Donate, WithdrawFunds,ClearFunds, Refund>.

  End Serialization.

  Definition Error : Type := nat.
  Definition default_error : Error := 1%nat.
  Definition insufficient_funds_error : Error := 2%nat.
  Definition unauthorized_error : Error := 3%nat.
  Definition contract_closed_error : Error := 4%nat.

  (***********************************************************)
  (** * 4. 合约初始化函数 (init)                             *)
  (***********************************************************)

  Definition init
             (chain : Chain)
             (ctx : ContractCallContext)
             (setup : Setup)
    : result State Error :=
    let sender := ctx_from ctx in
    let amount := ctx_amount ctx in
    (* 初始化时不需要附带ETH, 并简单校验地址合法性 *)
    if (amount =? 0)%Z &&
       (address_neqb setup.(setup_admin) setup.(setup_beneficiary))
    then
      let st :=
        build_state
          setup.(setup_admin)
          setup.(setup_beneficiary)
          setup.(setup_fundingGoal)
          0               (* totalFunds *)
          false           (* isClosed *)
          (FMap.empty : FMap Address Amount)
      in Ok st
    else
      Err default_error.

  (***********************************************************)
  (** * 5. 具体操作函数：示例 - 贡献资金 (donate)            *)
  (***********************************************************)

  (** 判断当前阶段是否允许捐赠资金 *)
  Definition require_phase (st : State) (phase : CrowdfundPhase) : bool :=
    match phase with
    | AWAITING_FUNDS => negb st.(isClosed) && (st.(totalFunds) <? st.(fundingGoal))
    | FUNDS_REACHED  => negb st.(isClosed) && (st.(totalFunds) >=? st.(fundingGoal))
    | CLOSED         => st.(isClosed)
    end.

  (** donate 函数：接受 ctx_amount 的资金捐赠 *)
  Definition donate
             (chain : Chain)
             (ctx : ContractCallContext)
             (st : State)
    : result (State * list ActionBody) Error :=
    let donor := ctx_from ctx in
    let amt   := ctx_amount ctx in
    if (require_phase st AWAITING_FUNDS) && (amt >? 0)
    then
      (* 更新 totalFunds *)
      let new_total := st.(totalFunds) + amt in
      (* 查找 donor 原先的贡献金额 *)
      let old_contrib := FMap.find donor st.(contributions) in
      let old_amt := match old_contrib with
                     | Some x => x
                     | None   => 0
                     end in
      let updated_amt := old_amt + amt in
      (* 更新 contributions *)
      (* 这里用 update，也可以直接用 FMap.add donor updated_amt *)
      let new_map := FMap.add donor updated_amt st.(contributions) in
      (* 如果超过目标，则关闭合约 *)
      let new_isClosed :=
        if (new_total >=? st.(fundingGoal)) then true else st.(isClosed)
      in
      let new_st :=
        build_state
          st.(admin)
          st.(beneficiary)
          st.(fundingGoal)
          new_total
          new_isClosed
          new_map
      in
      Ok (new_st, [])
    else
      Err insufficient_funds_error.

  (***********************************************************)
  (** * 6. 提取资金 (withdrawFunds) 与 退款 (refund)         *)
  (***********************************************************)

  Definition withdrawFunds
             (chain : Chain)
             (ctx : ContractCallContext)
             (st : State)
    : result (State * list ActionBody) Error :=
    let sender := ctx_from ctx in
    if (require_phase st FUNDS_REACHED) && 
       (address_neqb sender (ctx_contract_address ctx))  (* 防止自调用 *)
    then
      let transfer_amount := (ctx_contract_balance ctx) in
      let actions := [act_transfer st.(beneficiary) transfer_amount] in
      let new_st :=
        build_state
          st.(admin)
          st.(beneficiary)
          st.(fundingGoal)
          st.(totalFunds)
          true
          st.(contributions)
      in
      Ok (new_st, actions)
    else
      Err unauthorized_error.

  (* 清理自毁资金 *)
  Definition clearFunds
            (chain : Chain)
            (ctx : ContractCallContext)
            (st : State)
    : result (State * list ActionBody) Error :=
    let sender := ctx_from ctx in
    if (st.(isClosed)) && 
        (address_neqb sender (ctx_contract_address ctx))  (* 防止自调用 *)
    then
      let transfer_amount := (ctx_contract_balance ctx) in
      let actions := [act_transfer st.(beneficiary) transfer_amount] in
      Ok (st, actions)
    else
      Err unauthorized_error.

  Definition refund
             (chain : Chain)
             (ctx : ContractCallContext)
             (st : State)
    : result (State * list ActionBody) Error :=
    let sender := ctx_from ctx in
    if (require_phase st AWAITING_FUNDS) &&
       (address_eqb sender st.(admin)) &&
       (address_neqb sender (ctx_contract_address ctx))
    then
      (* 将所有 contributions 的资金原路退回 *)
      let all_contributors := FMap.keys st.(contributions) in
      (* 生成多重转账列表 *)
      let actions := map (fun c =>
                            match FMap.find c st.(contributions) with
                            | Some amt => act_transfer c amt
                            | None     => act_transfer c 0
                            end)
                          all_contributors
      in
      let new_st :=
        build_state
          st.(admin)
          st.(beneficiary)
          st.(fundingGoal)
          st.(totalFunds)
          true  (* 合约关闭 *)
          st.(contributions)
      in
      Ok (new_st, actions)
    else
      Err unauthorized_error.

  Definition receive_eth_by_self_destruct
             (chain : Chain)
             (ctx : ContractCallContext)
             (st : State)
    : result (State * list ActionBody) Error :=
    let msg_value := ctx_amount ctx in
    if (msg_value >? 0) then
       Ok(st, [])
    else 
      Err default_error.

  (***********************************************************)
  (** * 7. 合约主接收函数 (receive)                          *)
  (***********************************************************)

  Definition receive
             (chain : Chain)
             (ctx : ContractCallContext)
             (st : State)
             (msg : option Msg)
    : result (State * list ActionBody) Error :=
    (* 同样，防止自调用 *)
    if address_neqb (ctx_from ctx) (ctx_contract_address ctx)
    then
      match msg with
      | Some Donate         => donate chain ctx st
      | Some WithdrawFunds  => withdrawFunds chain ctx st
      | Some Refund         => refund chain ctx st
      | Some ClearFunds     => clearFunds chain ctx st
      | None               => receive_eth_by_self_destruct chain ctx st
      end
    else
      Err unauthorized_error.

  (***********************************************************)
  (** * 8. 最终合约定义                                       *)
  (***********************************************************)

  Definition contract : Contract Setup Msg State Error :=
    build_contract init receive.

End CrowdfundWithFMap.

Section Lqiuidity.

  Context {BaseTypes : ChainBase}.
  Set Primitive Projections.
  Set Nonrecursive Elimination Schemes.
  Context {AddrSize : N}.
  Context {DepthFirst : bool}.
  Local Open Scope Z.


  Ltac reduce_init :=
    match goal with
    | H : init ?chain ?ctx ?setup = Ok ?st |- _ =>
        unfold init in H;
        (* 分解代码中 (amount =? 0)%Z && address_not_contract ... && address_neqb ... *)
        destruct ((ctx_amount ctx =? 0)%Z
                  && address_neqb setup.(setup_admin) setup.(setup_beneficiary))
          eqn:Einit in H;
        try discriminate;
        simpl in H
    end.

  Ltac reduce_donate :=
    match goal with
    | H : donate ?chain ?ctx ?st = Ok (?new_st, ?acts) |- _ =>
        unfold donate in H;
        (* 分解 donate 中的布尔条件 (require_phase st AWAITING_FUNDS) && (amt >? 0) *)
        destruct ((require_phase st AWAITING_FUNDS) && (_ >? 0) && (address_not_contract (ctx_from ctx)) ) eqn:Edonate in H;
        try discriminate;
        simpl in H
    end.

  Ltac reduce_withdrawFunds :=
    match goal with
    | H : withdrawFunds ?chain ?ctx ?st = Ok (?new_st, ?acts) |- _ =>
        unfold withdrawFunds in H;
        (* 分解 (require_phase st FUNDS_REACHED) && address_neqb ... *)
        destruct ((require_phase st FUNDS_REACHED) &&
                  address_neqb (ctx_from ctx) (ctx_contract_address ctx))
          eqn:Ewithd in H;
        try discriminate;
        simpl in H
    end.

  Ltac reduce_clearFunds :=
    match goal with
    | H : clearFunds ?chain ?ctx ?st = Ok (?new_st, ?acts) |- _ =>
        unfold clearFunds in H;
        (* 分解 st.(isClosed) && address_neqb ... *)
        destruct (st.(isClosed) &&
                  address_neqb (ctx_from ctx) (ctx_contract_address ctx))
          eqn:Eclear in H;
        try discriminate;
        simpl in H
    end.

  Ltac reduce_refund :=
    match goal with
    | H : refund ?chain ?ctx ?st = Ok (?new_st, ?acts) |- _ =>
        unfold refund in H;
        (* 分解 (require_phase st AWAITING_FUNDS) && address_eqb ... && address_neqb ... *)
        destruct ((require_phase st AWAITING_FUNDS) &&
                  address_eqb (ctx_from ctx) st.(admin) &&
                  address_neqb (ctx_from ctx) (ctx_contract_address ctx))
          eqn:Erefund in H;
        try discriminate;
        simpl in H
    end.

  Ltac reduce_receive_eth_by_self_destruct :=
    match goal with
    | H : receive_eth_by_self_destruct ?chain ?ctx ?st = Ok (?new_st, ?acts) |- _ =>
        unfold receive_eth_by_self_destruct in H;
        (* 分解 (msg_value >? 0) *)
        destruct (_ >? 0) eqn:Eselfd in H;
        try discriminate;
        simpl in H
    end.

  Ltac reduce_receive :=
    match goal with
    | H : receive ?chain ?ctx ?st ?msg = Ok (?new_st, ?acts) |- _ =>
        (* 1. 展开 receive 函数 *)
        unfold receive in H;
        (* 2. 分解 require_zero ctx *)
        destruct (address_neqb (ctx_from ctx) (ctx_contract_address ctx)) eqn:Eself in H; try discriminate;
        (* 3. 若 require_zero ctx = true，则进入 match msg *)
        destruct msg eqn:Emsg in H; try discriminate;
        (* 如果需要进一步分解各种消息对应的子函数，可在此继续:
          例如 unfold markAsShipped in H; destruct if-conditions ... *)
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

  Definition ubeneficiary := (init_cstate.(beneficiary)).
  Definition uadmin := (init_cstate.(admin)).

  Definition uadmin_call_clearFunds (state : State) : Action :=
    build_call uadmin caddr 0 ClearFunds.

  Definition uadmin_call_reFund (state : State) : Action :=
    build_call uadmin caddr 0 Refund.
  
  Definition uadmin_call_withdrawFunds (state : State) : Action :=
    build_call uadmin caddr 0 WithdrawFunds.

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

  Lemma contract_constants_receive :forall prev_state new_state chain ctx msg new_acts,
  receive chain ctx prev_state msg = Ok (new_state, new_acts) ->
    prev_state.(beneficiary) = new_state.(beneficiary)
    /\ prev_state.(admin) = new_state.(admin)
    /\ prev_state.(fundingGoal) = new_state.(fundingGoal).
  Proof.
    intros.
    reduce_receive.
    destruct_message;try congruence.
    - reduce_donate.
      inversion H.
      split.
      simpl.
      eauto.
      simpl.
      eauto.
    - reduce_withdrawFunds .
      inversion H.
      split.
      simpl.
      eauto.
      simpl.
      eauto.
    - reduce_clearFunds .
      inversion H.
      split.
      simpl.
      eauto.
      simpl.
      eauto.
    -  reduce_refund  .
      inversion H.
      split.
      simpl.
      eauto.
      simpl.
      eauto.
    - reduce_receive_eth_by_self_destruct.
      inversion H.
      split.
      simpl.
      eauto.
      simpl.
      eauto.
  Qed.

  Lemma contract_constants_reachable_through :
    forall s,
    reachable_through s0 s ->
    exists cstate, 
      contract_state s caddr = Some cstate /\
      cstate.(beneficiary) = init_cstate.(beneficiary) /\
      cstate.(admin) = init_cstate.(admin) /\
      cstate.(fundingGoal) = init_cstate.(fundingGoal) .
  Proof.
    intros.
    unfold reachable_through in H.
    destruct H as [Hrc_s0 [trace]].
    induction trace.
    - exists init_cstate.
      intuition.
    - specialize(IHtrace H_init H_state Hrc_s0).
      destruct_chain_step; try now rewrite_environment_equiv.
      + destruct IHtrace.
        exists x.
        rewrite_environment_equiv.
        intuition.
      + destruct_action_eval.
        * destruct IHtrace.
          exists x.
          rewrite_environment_equiv.
          intuition.
        * destruct IHtrace.
          exists x.
          rewrite_environment_equiv.
          intuition.
          cbn in *.
          destruct_address_eq;subst;eauto.
          decompose_is_init_state H_init.
          assert(reachable_through from mid).
          {
            econstructor;eauto.
          }
          eapply (reachable_through_contract_deployed from mid to_addr contract) in H2;eauto.
          congruence.
        * destruct IHtrace.
          destruct (address_eqb_spec caddr to_addr); subst; eauto.
          replace wc with (contract : WeakContract)  in * ;try congruence.
          destruct (wc_receive_strong ltac:(try eassumption))
          as (prev_state_strong & msg_strong & resp_state_strong &
            deser_state & deser_msg & <- & receive).
          exists resp_state_strong.
          intuition.
          rewrite_environment_equiv.
          cbn in *.
          destruct_address_eq;try congruence.
          setoid_rewrite deserialize_serialize.
          eauto.
          setoid_rewrite deserialize_serialize.
          eauto.
          eapply contract_constants_receive in receive.
          intuition.
          unfold contract_state in H0.
          simpl in H0.
          rewrite deployed_state in H0.
          intuition.
          eapply contract_constants_receive in receive.
          intuition.
          unfold contract_state in H0.
          simpl in H0.
          rewrite deployed_state in H0.
          intuition.
          eapply contract_constants_receive in receive.
          intuition.
          unfold contract_state in H0.
          simpl in H0.
          rewrite deployed_state in H0.
          intuition.
          assert(reachable_through from mid).
          {
            econstructor;eauto.
          }
          eapply (reachable_through_contract_deployed from mid to_addr contract) in H0;eauto.
          intuition.
          decompose_is_init_state H_init.
          intuition.
          exists x.
          intuition.
          rewrite_environment_equiv.
          cbn in *.
          destruct_address_eq;try congruence.
  Qed.

  Lemma contract_constants_transition_via :forall s,
    transition_reachable miner contract caddr s0 s ->
    exists cstate, 
      contract_state s caddr = Some cstate /\
      cstate.(beneficiary) = init_cstate.(beneficiary) /\
      cstate.(admin) = init_cstate.(admin) /\
      cstate.(fundingGoal) = init_cstate.(fundingGoal) .
  Proof.
    intros.
    assert(ttrace : transition_reachable miner contract caddr s0 s) by eauto.
    unfold transition_reachable in ttrace.
    destruct ttrace as [_ [ttrace]].
    decompose_is_init_state H_init.
    assert(reachable s0) by eauto.
    destruct H0 as [trace].
    eapply ttrace_with_trace in ttrace;eauto.
    assert(reachable_through s0 s).
    {
      econstructor;eauto.
    }
    eapply contract_constants_reachable_through in H0.
    intuition.
  Qed.

  Lemma beneficiary_and_admin_is_EOA bstate:
    reachable bstate ->
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    exists cstate,
      contract_state bstate caddr = Some cstate
      /\ address_not_contract cstate.(beneficiary) = true
      /\ address_not_contract cstate.(admin) = true
      /\ address_neqb (cstate.(beneficiary)) (cstate.(admin)) = true.
  Proof.
    contract_induction;intros;cbn in *;eauto;try congruence;try lia.
    - reduce_init.
      propify.
      destruct_and_split.
      destruct_and_split.
      inversion init_some;subst.
      eauto.
      inversion init_some;subst.
      eauto.
      inversion init_some;subst.
      simpl.
      destruct_address_eq;eauto.
    - reduce_receive.
      destruct_message;try congruence.
      + reduce_donate . cbn in *.
        inversion receive_some;subst;cbn in *.
        congruence.
      + reduce_withdrawFunds  . cbn in *.
        inversion receive_some;subst;cbn in *.
        congruence.
      + reduce_clearFunds  . cbn in *.
        inversion receive_some;subst;cbn in *.
        congruence.
      + reduce_refund  . cbn in *.
        inversion receive_some;subst;cbn in *.
        congruence.
      + reduce_receive_eth_by_self_destruct . cbn in *.
        inversion receive_some;subst;cbn in *.
        congruence.
    - reduce_receive.
      destruct_message;try congruence.
      + reduce_donate. cbn in *.
        inversion receive_some;subst;cbn in *;destruct head; cbn in *;try congruence.
      + reduce_withdrawFunds . cbn in *.
      inversion receive_some;subst;cbn in *;destruct head; cbn in *;try congruence.
      + reduce_clearFunds  . cbn in *.
      inversion receive_some;subst;cbn in *;destruct head; cbn in *;try congruence.
      + reduce_refund  . cbn in *.
      inversion receive_some;subst;cbn in *;destruct head; cbn in *;try congruence.
      + reduce_receive_eth_by_self_destruct.
      inversion receive_some;subst;cbn in *;destruct head; cbn in *;try congruence.
    - solve_facts.
  Qed.
  
  Require Import Coq.Lists.List.
  Require Import Coq.Sorting.Permutation.
  Import ListNotations.
  
  Lemma Forall_perm :
    forall (A : Type) (P : A -> Prop) (l l' : list A),
      Permutation l l' ->
      Forall P l ->
      Forall P l'.
  Proof.
    intros A P l l' Hperm HF.
    induction Hperm.
    - constructor.
    - inversion HF; subst.
      constructor; [assumption |].
      apply IHHperm.
      assumption.
    - inversion HF; subst.
      inversion H2; subst.
      constructor; [assumption | constructor; assumption].
    - apply IHHperm2.
      apply IHHperm1.
      assumption.
  Qed.
  
  Lemma contributions_is_EOA bstate:
    reachable bstate ->
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    exists cstate,
      contract_state bstate caddr = Some cstate /\
      Forall (fun addr => (address_not_contract addr) = true) (FMap.keys cstate.(contributions)).
  Proof.
    contract_induction;intros;cbn in *;eauto;try congruence;try lia.
    - reduce_init.
      propify.
      destruct_and_split.
      destruct_and_split.
      inversion init_some;subst.
      simpl.
      unfold FMap.keys.
      rewrite FMap.elements_empty.
      simpl.
      eapply Forall_nil.
    - reduce_receive.
      destruct_message;try congruence.
      + reduce_donate . propify. destruct_and_split. cbn in *.
        inversion receive_some;subst;cbn in *.
        destruct (FMap.find (ctx_from ctx) (contributions prev_state)) eqn : Hin.
        * eapply (FMap.keys_already (ctx_from ctx)  z (z + ctx_amount ctx) (contributions prev_state)) in Hin as Hperm.
          eapply Forall_perm in IH;eauto.
          intuition.
        * assert (perm : Permutation (FMap.elements (FMap.add (ctx_from ctx) (0 + ctx_amount ctx) (contributions prev_state))) (((ctx_from ctx), (0 + ctx_amount ctx))::(FMap.elements (contributions prev_state)))). { now apply FMap.elements_add. }
          set (new_elts := FMap.elements (FMap.add (ctx_from ctx) (0 + ctx_amount ctx)
          (contributions prev_state))).
          set (old_elts := FMap.elements (contributions prev_state)).
          change (FMap.keys (FMap.add (ctx_from ctx) (0 + ctx_amount ctx)
                                      (contributions prev_state)))
          with (map fst new_elts).
            assert (perm_keys :
            Permutation (map fst new_elts)
                        (map fst ((ctx_from ctx, 0 + ctx_amount ctx) :: old_elts)))
          by (apply (Permutation_map fst) in perm; assumption).
          change (map fst ((ctx_from ctx, 0 + ctx_amount ctx) :: old_elts))
          with ((ctx_from ctx) :: map fst old_elts) in perm_keys.
          assert (Forall (fun addr : Address => address_not_contract addr = true)(ctx_from ctx :: map fst old_elts)).
          {
            eapply Forall_cons;eauto.
          }
         eapply Permutation_Forall in H2;eauto.
         intuition.
      + reduce_withdrawFunds. destruct_and_split. cbn in *.
        inversion receive_some;subst;cbn in *.
        eauto.
      + reduce_clearFunds  . cbn in *.
        inversion receive_some;subst;cbn in *.
        congruence.
      + reduce_refund  . cbn in *.
        inversion receive_some;subst;cbn in *.
        congruence.
      + reduce_receive_eth_by_self_destruct . cbn in *.
        inversion receive_some;subst;cbn in *.
        congruence.
    - reduce_receive.
      destruct_message;try congruence.
      + reduce_donate. cbn in *. propify. destruct_and_split. cbn in *.
        inversion receive_some;subst;cbn in *;destruct head; cbn in *;try congruence;eauto.
        * destruct (FMap.find (ctx_from ctx) (contributions prev_state)) eqn : Hin.
          **  eapply (FMap.keys_already (ctx_from ctx)  z (z + ctx_amount ctx) (contributions prev_state)) in Hin as Hperm.
              eapply Forall_perm in IH;eauto.
              intuition.
          **  assert (perm : Permutation (FMap.elements (FMap.add (ctx_from ctx) 
              (0 + ctx_amount ctx) (contributions prev_state))) (((ctx_from ctx), (0 + ctx_amount ctx))::(FMap.elements (contributions prev_state)))). 
              { now apply FMap.elements_add. }
              set (new_elts := FMap.elements (FMap.add (ctx_from ctx) (0 + ctx_amount ctx)
              (contributions prev_state))).
              set (old_elts := FMap.elements (contributions prev_state)).
              change (FMap.keys (FMap.add (ctx_from ctx) (0 + ctx_amount ctx)
                                          (contributions prev_state)))
              with (map fst new_elts).
                assert (perm_keys :
                Permutation (map fst new_elts)
                            (map fst ((ctx_from ctx, 0 + ctx_amount ctx) :: old_elts)))
              by (apply (Permutation_map fst) in perm; assumption).
              change (map fst ((ctx_from ctx, 0 + ctx_amount ctx) :: old_elts))
              with ((ctx_from ctx) :: map fst old_elts) in perm_keys.
              assert (Forall (fun addr : Address => address_not_contract addr = true)(ctx_from ctx :: map fst old_elts)).
              {
                eapply Forall_cons;eauto.
              }
              eapply Permutation_Forall in H3;eauto.
              intuition.
        * destruct (FMap.find (ctx_from ctx) (contributions prev_state)) eqn : Hin.
          **  eapply (FMap.keys_already (ctx_from ctx)  z (z + ctx_amount ctx) (contributions prev_state)) in Hin as Hperm.
              eapply Forall_perm in IH;eauto.
              intuition.
          **  assert (perm : Permutation (FMap.elements (FMap.add (ctx_from ctx) 
              (0 + ctx_amount ctx) (contributions prev_state))) (((ctx_from ctx), (0 + ctx_amount ctx))::(FMap.elements (contributions prev_state)))). 
              { now apply FMap.elements_add. }
              set (new_elts := FMap.elements (FMap.add (ctx_from ctx) (0 + ctx_amount ctx)
              (contributions prev_state))).
              set (old_elts := FMap.elements (contributions prev_state)).
              change (FMap.keys (FMap.add (ctx_from ctx) (0 + ctx_amount ctx)
                                          (contributions prev_state)))
              with (map fst new_elts).
                assert (perm_keys :
                Permutation (map fst new_elts)
                            (map fst ((ctx_from ctx, 0 + ctx_amount ctx) :: old_elts)))
              by (apply (Permutation_map fst) in perm; assumption).
              change (map fst ((ctx_from ctx, 0 + ctx_amount ctx) :: old_elts))
              with ((ctx_from ctx) :: map fst old_elts) in perm_keys.
              assert (Forall (fun addr : Address => address_not_contract addr = true)(ctx_from ctx :: map fst old_elts)).
              {
                eapply Forall_cons;eauto.
              }
              eapply Permutation_Forall in H3;eauto.
              intuition.
        * destruct (FMap.find (ctx_from ctx) (contributions prev_state)) eqn : Hin.
          **  eapply (FMap.keys_already (ctx_from ctx)  z (z + ctx_amount ctx) (contributions prev_state)) in Hin as Hperm.
              eapply Forall_perm in IH;eauto.
              intuition.
          **  assert (perm : Permutation (FMap.elements (FMap.add (ctx_from ctx) 
              (0 + ctx_amount ctx) (contributions prev_state))) (((ctx_from ctx), (0 + ctx_amount ctx))::(FMap.elements (contributions prev_state)))). 
              { now apply FMap.elements_add. }
              set (new_elts := FMap.elements (FMap.add (ctx_from ctx) (0 + ctx_amount ctx)
              (contributions prev_state))).
              set (old_elts := FMap.elements (contributions prev_state)).
              change (FMap.keys (FMap.add (ctx_from ctx) (0 + ctx_amount ctx)
                                          (contributions prev_state)))
              with (map fst new_elts).
                assert (perm_keys :
                Permutation (map fst new_elts)
                            (map fst ((ctx_from ctx, 0 + ctx_amount ctx) :: old_elts)))
              by (apply (Permutation_map fst) in perm; assumption).
              change (map fst ((ctx_from ctx, 0 + ctx_amount ctx) :: old_elts))
              with ((ctx_from ctx) :: map fst old_elts) in perm_keys.
              assert (Forall (fun addr : Address => address_not_contract addr = true)(ctx_from ctx :: map fst old_elts)).
              {
                eapply Forall_cons;eauto.
              }
              eapply Permutation_Forall in H3;eauto.
              intuition.
      + reduce_withdrawFunds . cbn in *.
      inversion receive_some;subst;cbn in *;destruct head; cbn in *;try congruence.
      + reduce_clearFunds  . cbn in *.
      inversion receive_some;subst;cbn in *;destruct head; cbn in *;try congruence.
      + reduce_refund  . cbn in *.
      inversion receive_some;subst;cbn in *;destruct head; cbn in *;try congruence.
      + reduce_receive_eth_by_self_destruct.
      inversion receive_some;subst;cbn in *;destruct head; cbn in *;try congruence.
    - solve_facts.
  Qed.

  Local Open Scope Z.



  



End Lqiuidity.
