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

Section EtherGame.

  (** 环境依赖：区块、上下文、地址类型等由外部框架提供。 *)
  Context {BaseTypes : ChainBase}.
  Set Primitive Projections.
  Set Nonrecursive Elimination Schemes.
  Context {AddrSize : N}.

  Local Open Scope Z.

  (***********************************************************)
  (** * 1. 定义合约内部用到的类型与状态                     *)
  (***********************************************************)

  (** 定义以 ether 为单位的常量 *)
  Definition ether : Amount := 1.

  
  Variable zero_addr : Address.

  Hypothesis H_zero_addr : forall addr, address_neqb zero_addr addr = true.

  (** 合约状态记录 [State]，对应 Solidity 里的存储变量。 *)
  Record State := build_state {
    targetAmount : Amount;      (* 筹款目标金额，以 ether 为单位，固定为 7 ether *)
    balance      : Amount;      (* 当前筹集的总金额，以 ether 为单位 *)
    winner       : Address      (* 达到目标金额的赢家地址 *)
  }.

  Definition Setup : Type := unit.

  (***********************************************************)
  (** * 2. 为 Record 添加 Settable/Serializable 实例        *)
  (***********************************************************)

  (* 使用框架提供的 Derive 语法进行序列化实例的自动生成。 *)

  Instance state_settable : Settable State :=
    settable! build_state
      <targetAmount; balance; winner>.


  (** 序列化定义 *)
  Section Serialization.
    Global Instance State_serializable : Serializable State :=
      Derive Serializable State_rect<build_state>.

  End Serialization.

  (***********************************************************)
  (** * 3. 定义消息类型                                     *)
  (***********************************************************)

  (** Solidity 中对应的函数调用：
      - deposit()
      - claimReward()
  *)
  Inductive Msg :=
  | Deposit
  | ClaimReward
  | Fallback.

  Global Instance Msg_serializable : Serializable Msg :=
    Derive Serializable Msg_rect<Deposit, ClaimReward, Fallback>.

  (***********************************************************)
  (** * 4. 定义错误类型及常量                               *)
  (***********************************************************)

  Definition Error : Type := nat.
  Definition default_error : Error := 1%nat.
  Definition invalid_deposit_error : Error := 2%nat.
  Definition game_over_error : Error := 3%nat.
  Definition not_winner_error : Error := 4%nat.
  Definition transfer_failed_error : Error := 5%nat.

  (***********************************************************)
  (** * 5. 合约初始化函数 (init)                             *)
  (***********************************************************)

  (** 对应 Solidity 构造函数:
        constructor() {
            targetAmount = 7 ether;
            balance = 0;
            winner = address(0);
        }
    在 Coq 中，通过 [init] 模拟此逻辑。
   *)

  
     
  Definition init
             (chain : Chain)
             (ctx : ContractCallContext)
             (setup : Setup)
    : result State Error :=
    let st := build_state
                7              (* 7 ether *)
                0             (* balance 初始为0 *)
                zero_addr    (* winner 初始为空地址 *)
    in Ok st.

  (***********************************************************)
  (** * 6. 具体操作函数                                     *)
  (***********************************************************)

  (** 检查调用者是否为 winner *)
  Definition require_winner (ctx : ContractCallContext) (st : State) : bool :=
    address_eqb (ctx_from ctx) st.(winner).

  Definition require_no_self_call (ctx : ContractCallContext) : bool :=
    (address_neqb (ctx.(ctx_from))  (ctx.(ctx_contract_address))).

  Definition require_ctx_from_eoa (ctx : ContractCallContext) : bool :=
    (address_not_contract (ctx.(ctx_from))).

  (** ** 贡献资金 (deposit) *)
  Definition deposit
             (chain : Chain)
             (ctx : ContractCallContext)
             (st : State)
    : result (State * list ActionBody) Error :=
    let sender := ctx_from ctx in
    let amt    := ctx_amount ctx in
    if require_ctx_from_eoa ctx then
    (* 要求每次存入1 ether *)
    if (amt =? ether)%Z
    then
      let new_balance := st.(balance) + amt in
      (* 要求新的余额不超过目标金额 *)
      if (new_balance <=? st.(targetAmount))
      then
        (* 如果新的余额等于目标金额，则设置 winner *)
        let new_winner :=
          if (new_balance =? st.(targetAmount))
          then sender
          else st.(winner)
        in
        let new_st := build_state
                        st.(targetAmount)
                        new_balance
                        new_winner
        in
        Ok (new_st, [])
        else Err default_error
      else
        Err game_over_error
    else
      Err invalid_deposit_error.

  (** ** 提取奖励 (claimReward) *)
  Definition claimReward
             (chain : Chain)
             (ctx : ContractCallContext)
             (st : State)
    : result (State * list ActionBody) Error :=
    let sender := ctx_from ctx in
    let msg_value := ctx_amount ctx in
    (* 要求调用者是 winner *)
    if require_winner ctx st then
      if (msg_value =? 0) then
        (* 尝试转移所有余额给 winner *)
        let actions := [ act_transfer sender (ctx_contract_balance ctx) ] in
        let new_st := build_state
                        st.(targetAmount)
                        st.(balance)
                        st.(winner)   (* winner 保持不变 *)
        in
        Ok (new_st, actions)
      else Err default_error
    else
      Err not_winner_error.

  Definition ether_receive
              (chain : Chain)
              (ctx : ContractCallContext)
              (st : State)
    : result (State * list ActionBody) Error :=
    let msg_value := ctx_amount ctx in
    if (msg_value >=? 0) then
      Ok (st,[])
    else
      Err default_error.

  (***********************************************************)
  (** * 7. 合约主接收函数 (receive)                          *)
  (***********************************************************)

  (** 根据消息类型调用相应的操作函数。 *)
  Definition receive
             (chain : Chain)
             (ctx : ContractCallContext)
             (st : State)
             (msg : option Msg)
    : result (State * list ActionBody) Error :=
    if require_no_self_call ctx then
      match msg with
      | Some Deposit     => deposit chain ctx st
      | Some ClaimReward => claimReward chain ctx st
      | Some fallback   => ether_receive chain ctx st
      | None => Err default_error
      end
    else
      Err default_error.

  (***********************************************************)
  (** * 8. 最终合约定义                                       *)
  (***********************************************************)

  Definition contract : Contract Setup Msg State Error :=
    build_contract init receive.

Local Open Scope Z.

Section Attacker.



  (** 合约状态记录 [State]，对应 Solidity 里的存储变量。 *)
  Record AttackerState := build_attacker_state {
    target : Address;
    close : bool
  }.

  Instance attacker_state_settable : Settable AttackerState :=
  settable! build_attacker_state <target;close>.

  Global Instance AttackerState_serializable : Serializable AttackerState :=
    Derive Serializable AttackerState_rect<build_attacker_state>.

  Record AttackerSetup := build_attacker_setup {
      setup_target : Address;
      setup_close : bool
  }.

  Instance attacker_setup_settable : Settable AttackerSetup :=
  settable! build_attacker_setup <setup_target;setup_close>.

  Global Instance AttackerSetup_serializable : Serializable AttackerSetup :=
  Derive Serializable AttackerSetup_rect<build_attacker_setup>.

  Inductive AttackerMsg :=
  | SelfDestruct.

  Global Instance AttackerMsg_serializable : Serializable AttackerMsg :=
    Derive Serializable AttackerMsg_rect<SelfDestruct>.

  Definition attacker_init
             (chain : Chain)
             (ctx : ContractCallContext)
             (setup : AttackerSetup)
    : result AttackerState Error :=
    let st := build_attacker_state (setup_target setup) false
    in Ok st.

  Definition selfDestruct
              (chain : Chain)
              (ctx : ContractCallContext)
              (st : AttackerState)
    : result (AttackerState * list ActionBody) Error :=
    Ok(st, [act_call st.(target) 1 (serialize Fallback)]).

  Definition attacker_receive
             (chain : Chain)
             (ctx : ContractCallContext)
             (st : AttackerState)
             (msg : option AttackerMsg)
    : result (AttackerState * list ActionBody) Error :=
      if (st.(close)) then
        Err default_error
      else 
        match msg with
        | Some SelfDestruct   => selfDestruct chain ctx st
        | None => Err default_error
        end.

  Definition attacker_contract : Contract AttackerSetup AttackerMsg AttackerState Error :=
    build_contract attacker_init attacker_receive.

End Attacker.

Ltac reduce_init :=
  match goal with
  | H : init ?chain ?ctx ?setup = Ok ?state |- _ =>
      (* 1. 展开 init 函数 *)
      unfold init in H;
      simpl in H
  end.

Ltac reduce_receive :=
  match goal with
  | H : receive ?chain ?ctx ?st ?msg = Ok (?new_st, ?acts) |- _ =>
      
      (* 1. 展开 receive 函数 *)
      unfold receive in H;
      destruct (require_no_self_call ctx) eqn : Hself;try congruence;
      simpl in H
  end.

  Ltac reduce_deposit :=
    match goal with
    | H : deposit ?chain ?ctx ?st = Ok (?new_st, ?acts) |- _ =>
        unfold deposit in H;
        (* 提取当前交易金额 *)
        let amt := fresh "amt" in
        remember (ctx_amount ctx) as amt eqn:Eamt;
        (* 检查交易金额是否为 1 ether *)
        destruct (amt =? ether)%Z eqn:EisEther in H;
        try discriminate;
        (* 计算新余额 *)
        let new_balance := fresh "new_balance" in
        remember (st.(balance) + amt) as new_balance eqn:Ebalance;
        (* 检查新余额是否不超过目标金额 *)
        destruct (require_ctx_from_eoa ctx) eqn : Heoa in H ;try congruence ;
        destruct (new_balance <=? st.(targetAmount))%Z eqn:EwithinTarget in H;
        try discriminate;
        (* 检查新余额是否等于目标金额 *)
        destruct (new_balance =? st.(targetAmount)) eqn:EisTarget in H;
        simpl in H
    end.

    Ltac reduce_claimReward :=
      match goal with
      | H : claimReward ?chain ?ctx ?st = Ok (?new_st, ?acts) |- _ =>
          unfold claimReward in H;
          (* 提取调用者地址和交易金额 *)
          let sender := fresh "sender" in
          remember (ctx_from ctx) as sender eqn:Esender;
          let msg_value := fresh "msg_value" in
          remember (ctx_amount ctx) as msg_value eqn:Emsg_value;
          (* 检查调用者是否是赢家 *)
          destruct (require_winner ctx st) eqn:EsenderIsWinner in H;
          try discriminate;
          (* 检查交易金额是否为 0 *)
          destruct (msg_value =? 0)%Z eqn:EzeroValue in H;
          try discriminate;
          simpl in H
      end.
    

Ltac reduce_ether_receive :=
  match goal with
  | H : ether_receive ?chain ?ctx ?st = Ok (?new_st, ?acts) |- _ =>
      unfold ether_receive in H;
      (* 提取当前交易金额 *)
      let msg_value := fresh "msg_value" in
      remember (ctx_amount ctx) as msg_value eqn:Emsg_value;
      (* 检查交易金额是否非负 *)
      destruct (msg_value >=? 0)%Z eqn:EnonNegative in H;
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

    Definition get_attacker_contract_state (state : ChainState) (addr : Address) : option AttackerState :=
      match env_contract_states state addr with
      | Some serialized_state =>
        deserialize serialized_state
      | None => None
      end.

  
  Context `{caddr : Address} `{miner : Address}.

  Variable s0 : ChainState.

  Variable Attacker_s0 : ChainState.

  Hypothesis H_init: is_init_state contract caddr s0.

  Variable attacker_addr : Address.

  Hypothesis H_attacker_addr_neq_caddr : attacker_addr <> caddr.

  Hypothesis H_Attacker_init: is_init_state attacker_contract attacker_addr Attacker_s0.

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

  Variable Attacker_init_cstate : AttackerState.

  Hypothesis H_state : get_contract_state s0 caddr = Some init_cstate.

  Hypothesis H_Attacker_state : get_attacker_contract_state Attacker_s0 caddr = Some Attacker_init_cstate.

  Hypothesis H_Attacker_init_cstate : Attacker_init_cstate.(target) = caddr.

  Variable user : Address.
  Variable attacker : Address.

  Hypothesis user_eoa : address_not_contract user = true.

  Hypothesis user_bal : forall s, funds s user >= 1.

  Hypothesis attacker_bal : forall s, funds s attacker >= 1.

  Hypothesis attacker_eoa : address_not_contract attacker = true.

  Definition user_call_Deposit (state : State) : Action :=
    build_call user caddr 1 Deposit.

  Definition winner_call_ClaimReward (state : State) : Action :=
    build_call state.(winner) caddr 0 ClaimReward.

  Definition addr_call_ClaimReward (state : State) (addr : Address) : Action :=
    build_call addr caddr 0 ClaimReward.

  Definition user_call_ClaimReward (state : State) : Action :=
    build_call user caddr 0 ClaimReward.

  Definition attacker_call_Fallback (state : State) : Action :=
    build_call attacker attacker_addr 0 SelfDestruct.

  Variable ohter_participants : list Address.

  Definition participants := [user] ++ ohter_participants.

  Definition inb (x : Address) (l : list Address) : bool :=
    existsb (fun y => address_eqb x y) l.

  Lemma inb_correct :
    forall (x : Address) (l : list Address),
      In x l <-> inb x l = true.
  Proof.
    intros x l.
    unfold inb.
    rewrite existsb_exists.
    split.
    - intros HIn.
      exists x.
      split.
      + exact HIn.
      + destruct_address_eq;try congruence;eauto.
    - intros [y [Hy Heqb]].
      destruct_address_eq;try congruence;eauto.
  Qed.
  

  Hypothesis winner_in_participants : 
    forall s cstate, 
      reachable s ->
      env_contracts s caddr = Some (contract : WeakContract) ->
      contract_state s caddr = Some cstate ->
      cstate.(balance) = cstate.(targetAmount) ->
      inb cstate.(winner) participants = true.
  
  Hypothesis zero_not_in_participants : inb zero_addr participants = false.

  Definition user_strat : (strat miner participants) :=
    fun s0 s tr  =>
      match get_contract_state s caddr with
      | Some state =>
         if (inb state.(winner) participants) then
            [winner_call_ClaimReward state]
          else
            [user_call_Deposit state]
      | None => []
      end.

  Definition attacker_strat : (strat miner [attacker]) :=
    fun s0 s tr  =>
      match get_contract_state s caddr with
      | Some state =>
         if ((state.(balance) =? 6)) then
            [attacker_call_Fallback state]
          else
            []
      | None => []
      end.

  Lemma contract_constants_receive :forall prev_state new_state chain ctx msg new_acts,
    receive chain ctx prev_state msg = Ok (new_state, new_acts) ->
      prev_state.(targetAmount) = new_state.(targetAmount).
  Proof.
    intros.
    reduce_receive.
    destruct_message;try congruence.
    - reduce_deposit; inversion H;eauto.
    - reduce_claimReward;inversion H;eauto.
    - reduce_ether_receive;inversion H;eauto.
  Qed.

  Lemma win_set_receive :forall prev_state new_state chain ctx msg new_acts,
    receive chain ctx prev_state msg = Ok (new_state, new_acts) ->
    prev_state.(balance) < prev_state.(targetAmount) ->
    new_state.(balance) = new_state.(targetAmount) ->
    new_state.(winner) = ctx_from ctx.
  Proof.
    intros.
    reduce_receive.
    destruct_message;try congruence.
    - reduce_deposit; inversion H;subst;eauto.
      propify.
      simpl in *.
      lia.
    - reduce_claimReward;inversion H;subst;eauto.
      simpl in *.
      lia.
    - reduce_ether_receive;inversion H;subst;eauto.
      simpl in *.
      lia.
  Qed.

  (* concert没办法再一个文件中验证两个合约的不变量，并且无法循环依赖库 *)
  Hypothesis Attacker_target_constant :
    forall s,
    reachable s ->
    exists (cstate : AttackerState), 
      contract_state s attacker_addr = Some cstate /\
      cstate.(target) = Attacker_init_cstate.(target).

  Lemma contract_constants_reachable_through :
  forall s,
  reachable_through s0 s ->
  exists (cstate : State), 
    contract_state s caddr = Some cstate /\
    cstate.(targetAmount) = init_cstate.(targetAmount).
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
          destruct_address_eq;eauto;cbn in *;try congruence.

          rewrite e in *.
          decompose_is_init_state H_init.
          assert(reachable_through from mid).
          {
            econstructor;eauto.
          }
          eapply (reachable_through_contract_deployed from mid to_addr contract) in H;eauto.
          congruence.
        * destruct IHtrace.
          destruct (address_eqb_spec caddr to_addr); eauto;cbn in *;try congruence.
          rewrite e in *.
          replace wc with (contract : WeakContract)  in * ;try congruence.
          destruct (wc_receive_strong ltac:(try eassumption))
          as (prev_state_strong & msg_strong & resp_state_strong &
            deser_state & deser_msg & <- & receive).
          exists resp_state_strong.
          intuition.
          rewrite_environment_equiv.
          cbn in *.
          destruct_address_eq;cbn in *;try congruence.
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

  Lemma contract_constants_reachable_through_forall :
    forall s cstate,
    reachable_through s0 s ->
    contract_state s caddr = Some cstate ->
    cstate.(targetAmount) = init_cstate.(targetAmount).
  Proof.
    intros.
    eapply contract_constants_reachable_through in H.
    destruct H.
    destruct_and_split.
    intuition.
  Qed.

  Lemma contract_constants_transition_via :forall s,
  transition_reachable miner contract caddr s0 s ->
  exists cstate, 
    contract_state s caddr = Some cstate /\
    cstate.(targetAmount) = init_cstate.(targetAmount).
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



  Lemma contract_constants_transition_via_forall :forall s cstate,
    transition_reachable miner contract caddr s0 s ->
    contract_state s caddr = Some cstate ->
    cstate.(targetAmount) = init_cstate.(targetAmount).
  Proof.
    intros.
    eapply contract_constants_transition_via in H.
    destruct_and_split.
    intuition.
  Qed.

  Lemma winner_eoa_after_target bstate:
    reachable bstate ->
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    exists cstate, 
      contract_state bstate caddr = Some cstate /\
      (cstate.(balance) >= cstate.(targetAmount) -> address_not_contract cstate.(winner)= true).
  Proof.
    contract_induction;intros;cbn in *;eauto;try congruence;try lia.
    - reduce_init.
      inversion init_some.
      subst.
      cbn in *.
      lia.
    - reduce_receive.
      destruct_message;try congruence.
      + reduce_deposit.
        inversion receive_some;subst;cbn in *.
        unfold require_ctx_from_eoa.
        eauto.
        inversion receive_some;subst;cbn in *.
        unfold require_ctx_from_eoa.
        propify.
        lia.
      + reduce_claimReward.
        inversion receive_some;subst;cbn in *.
        eapply IH in H.
        intuition.
      + reduce_ether_receive.
        inversion receive_some;subst;cbn in *.
        intuition.
    - reduce_receive.
      destruct_message;try congruence.
      + reduce_deposit.
        inversion receive_some;subst;cbn in *.
        unfold require_ctx_from_eoa.
        eauto.
        inversion receive_some;subst;cbn in *.
        unfold require_ctx_from_eoa.
        propify.
        lia.
      + reduce_claimReward.
        inversion receive_some;subst;cbn in *.
        eapply IH in H.
        intuition.
      + reduce_ether_receive.
        inversion receive_some;subst;cbn in *.
        intuition.
    - solve_facts.
  Qed.

  Lemma balance_gt_zero bstate:
    reachable bstate ->
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    exists cstate, 
      contract_state bstate caddr = Some cstate /\
      (cstate.(balance) >= 0).
  Proof.
    contract_induction;intros;cbn in *;eauto;try congruence;try lia.
    - reduce_init.
      inversion init_some.
      subst.
      cbn in *.
      lia.
    - reduce_receive.
      destruct_message;try congruence.
      + reduce_deposit.
        inversion receive_some;subst;cbn in *.
        propify.
        unfold ether in *.
        intuition.
        inversion receive_some;subst;cbn in *.
        propify.
        unfold ether in *.
        intuition.
      + reduce_claimReward.
        inversion receive_some;subst;cbn in *.
        lia.
      + reduce_ether_receive.
        inversion receive_some;subst;cbn in *.
        intuition.
    - reduce_receive.
      destruct_message;try congruence.
      + reduce_deposit.
        inversion receive_some;subst;cbn in *.
        propify.
        unfold ether in *.
        intuition.
        inversion receive_some;subst;cbn in *.
        propify.
        unfold ether in *.
        intuition.
      + reduce_claimReward.
        inversion receive_some;subst;cbn in *.
        lia.
      + reduce_ether_receive.
        inversion receive_some;subst;cbn in *.
        intuition.
    - solve_facts.
  Qed.

  Lemma balance_gt_zero_forall bstate cstate:
    reachable bstate ->
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    contract_state bstate caddr = Some cstate ->
    (cstate.(balance) >= 0).
  Proof.
    intros.
    eapply balance_gt_zero in H.
    destruct_and_split.
    intuition.
    eauto.
  Qed.

  Lemma targetAmount_eq_7 : 
  forall (s : ChainState),
    reachable s ->
    env_contracts s caddr = Some (contract : WeakContract) ->
    exists (cstate : State), 
      contract_state s caddr = Some cstate /\
      cstate.(targetAmount) = 7.
  Proof.
    remember H_init as H_initt.
    contract_induction;intros;cbn in *;eauto;try congruence;try lia.
    - reduce_init.
      inversion init_some.
      simpl.
      lia.
    - reduce_receive.
      destruct_message;try congruence.
      + reduce_deposit.
        inversion receive_some;subst;cbn in *.
        unfold require_ctx_from_eoa.
        eauto.
        inversion receive_some;subst;cbn in *.
        unfold require_ctx_from_eoa.
        propify.
        lia.
      + reduce_claimReward.
        inversion receive_some;subst;cbn in *.
        intuition.
      + reduce_ether_receive.
        inversion receive_some;subst;cbn in *.
        intuition.
    - reduce_receive.
      destruct_message;try congruence.
      + reduce_deposit.
        inversion receive_some;subst;cbn in *.
        unfold require_ctx_from_eoa.
        eauto.
        inversion receive_some;subst;cbn in *.
        unfold require_ctx_from_eoa.
        propify.
        lia.
      + reduce_claimReward.
        inversion receive_some;subst;cbn in *.
        intuition.
      + reduce_ether_receive.
        inversion receive_some;subst;cbn in *.
        intuition.
    - solve_facts.
  Qed.

  Lemma targetAmount_eq_7_forall : 
  forall (s : ChainState) cstate,
    reachable s ->
    env_contracts s caddr = Some (contract : WeakContract) ->
    contract_state s caddr = Some cstate ->
    cstate.(targetAmount) = 7.
  Proof.
    intros.
    eapply targetAmount_eq_7 in H.
    destruct_and_split.
    intuition.
    eauto.
  Qed.

  Lemma balance_sub_targetAmount_geq_zero : 
    forall (s : ChainState),
    reachable s ->
    env_contracts s caddr = Some (contract : WeakContract) ->
    exists (cstate : State), 
      contract_state s caddr = Some cstate /\
      cstate.(balance) <= cstate.(targetAmount).
  Proof.
    contract_induction;intros;cbn in *;eauto;try congruence;try lia.
    - reduce_init.
      inversion init_some.
      simpl.
      lia.
    - reduce_receive.
      destruct_message;try congruence.
      + reduce_deposit.
        inversion receive_some;subst;cbn in *.
        unfold require_ctx_from_eoa.
        eauto.
        inversion receive_some;subst;cbn in *.
        unfold require_ctx_from_eoa.
        propify.
        lia.
        inversion receive_some;subst;cbn in *.
        unfold require_ctx_from_eoa.
        propify.
        lia.
      + reduce_claimReward.
        inversion receive_some;subst;cbn in *.
        intuition.
      + reduce_ether_receive.
        inversion receive_some;subst;cbn in *.
        intuition.
    - reduce_receive.
      destruct_message;try congruence.
      + reduce_deposit.
        inversion receive_some;subst;cbn in *.
        unfold require_ctx_from_eoa.
        eauto.
        inversion receive_some;subst;cbn in *.
        unfold require_ctx_from_eoa.
        propify.
        lia.
        inversion receive_some;subst;cbn in *.
        unfold require_ctx_from_eoa.
        propify.
        lia.
      + reduce_claimReward.
        inversion receive_some;subst;cbn in *.
        intuition.
      + reduce_ether_receive.
        inversion receive_some;subst;cbn in *.
        intuition.
    - solve_facts.
  Qed.

  Lemma balance_sub_targetAmount_geq_zero_forall : 
    forall (s : ChainState) cstate,
      reachable s ->
      env_contracts s caddr = Some (contract : WeakContract) ->
      contract_state s caddr = Some cstate ->
      cstate.(balance) <= cstate.(targetAmount).
  Proof.
    intros.
    eapply balance_sub_targetAmount_geq_zero in H;eauto.
    destruct_and_split.
    rewrite H in H1.
    inversion H1.
    subst.
    eauto.
  Qed.

  Lemma winner_eoa_after_target_forall bstate cstate:
    reachable bstate ->
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    contract_state bstate caddr = Some cstate ->
    (cstate.(balance) >= cstate.(targetAmount) -> address_not_contract cstate.(winner)= true ).
  Proof.
    intros.
    eapply winner_eoa_after_target in H;eauto.
    destruct_and_split.
    rewrite H in H1.
    inversion H1.
    subst.
    eauto.
  Qed.

  Lemma user_call_Deposit_is_call_act cstate:
    is_call_act (user_call_Deposit cstate) = true .
  Proof.
    unfold is_call_act.
    unfold user_call_Deposit.
    simpl.
    destruct_address_eq;eauto.
  Qed.

  Lemma winner_call_ClaimReward_is_call_act cstate:
    is_call_act (winner_call_ClaimReward cstate) = true .
  Proof.
    unfold is_call_act.
    unfold winner_call_ClaimReward.
    simpl.
    destruct_address_eq;eauto.
  Qed.

  Lemma user_call_ClaimReward_is_call_act cstate:
    is_call_act (user_call_ClaimReward cstate) = true .
  Proof.
    unfold is_call_act.
    unfold user_call_ClaimReward.
    simpl.
    destruct_address_eq;eauto.
  Qed.

  Lemma attacker_call_Fallback_is_call_act cstate:
    is_call_act (attacker_call_Fallback cstate) = true .
  Proof.
    unfold is_call_act.
    unfold attacker_call_Fallback.
    simpl.
    destruct_address_eq;eauto.
  Qed.

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

  Lemma winner_call_Claim_transition_correct:
    forall (s:ChainState) cstate,
      contract_state s caddr = Some cstate ->
      cstate.(balance) >= cstate.(targetAmount) ->
      readyToStepState miner contract caddr s0 s ->
      exists s', 
        transition miner s (winner_call_ClaimReward cstate) = Ok s'.
  Proof.
    intros * Hcs_s Hbal_state Hready_state_s.
    eexists.
    eapply address_not_contract_negb in H_miner as H_miner_eoa.
    unfold transition.
    unfold queue_isb_empty.
    pose proof Hready_state_s.
    unfold readyToStepState in H.
    destruct H as [Htrc_s Hqueue_s].
    rewrite Hqueue_s.
    rewrite winner_call_ClaimReward_is_call_act.
    unfold evaluate_action.
    rewrite get_valid_header_is_valid_header;eauto.
    unfold winner_call_ClaimReward .
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
    assert(H_constans:cstate.(targetAmount) = init_cstate.(targetAmount) ).
    {
      eapply transition_reachable_impl_reachable in Htrc_s.
      unfold readyToStepState in Hready_state_s.
      destruct_and_split.
      eapply transition_reachable_impl_reachable_through in H.
      eapply contract_constants_reachable_through in H;eauto.
      destruct_and_split.
      rewrite H in Hcs_s.
      inversion Hcs_s.
      subst.
      intuition.
      eauto.
      eauto.
    }
    assert(H_winner_eoa : address_is_contract (winner cstate) = false).
    {
      eapply transition_reachable_impl_reachable in Htrc_s.
      eapply winner_eoa_after_target_forall in Htrc_s.
      eapply address_not_contract_negb.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
    }
    assert(H_winner_eoa_t : address_not_contract (winner cstate) = true).
    {
      eapply transition_reachable_impl_reachable in Htrc_s.
      eapply winner_eoa_after_target_forall in Htrc_s;eauto.
      eauto.
    }
    rewrite H_winner_eoa.
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
    destruct_address_eq;try congruence.
    + assert ((0 >? miner_reward + env_account_balances s (winner cstate))%Z 
                = false).
      {
        unfold miner_reward.
        eapply (account_balance_nonnegative s (winner cstate)) in Hrc_s.
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
      unfold require_no_self_call.
      simpl.
      destruct_address_eq;cbn in *;try congruence.
      simpl.
      cbn.
      unfold require_ctx_from_eoa.
      simpl.
      unfold claimReward.
      simpl.
      unfold require_winner.
      simpl.
      destruct_address_eq;try congruence;cbn;eauto.
      unfold send_or_call.
      assert(0 + env_account_balances s caddr <? 0 = false).
      {
        eapply (account_balance_nonnegative s caddr) in Hrc_s.
        propify.
        lia.
      }
      rewrite H0.
      simpl.
      destruct_address_eq;try congruence;eauto.
      simpl.
      (* 1 *)
      assert( 0 + env_account_balances s caddr >?
      0 + env_account_balances s caddr = false)%Z.
      {
        lia.
      }
      rewrite H1.
      assert (H_winner_none: env_contracts s (winner cstate) = None).
      { 
        destruct (env_contracts s (winner cstate)) eqn:H_env.
        - exfalso.
          apply (contract_addr_format (winner cstate) w) in H_env; eauto.
          congruence.
        - reflexivity.
      }
      rewrite H_winner_none.
      rewrite H_winner_eoa.
      simpl.
      eauto.
    +
      assert ((0 >?  env_account_balances s (winner cstate))%Z 
                = false).
      {
        unfold miner_reward.
        eapply (account_balance_nonnegative s (winner cstate)) in Hrc_s.
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
      unfold require_no_self_call.
      simpl.
      destruct_address_eq;cbn in *;try congruence.
      simpl.
      cbn.
      unfold require_ctx_from_eoa.
      simpl.
      unfold claimReward.
      simpl.
      unfold require_winner.
      simpl.
      destruct_address_eq;cbn in *;try congruence;eauto.
      unfold send_or_call.
      assert(0 + env_account_balances s caddr <? 0 = false).
      {
        eapply (account_balance_nonnegative s caddr) in Hrc_s.
        propify.
        lia.
      }
      rewrite H0.
      simpl.
      destruct_address_eq;cbn in *;try congruence;eauto.
      (* 1 *)
      assert( 0 + env_account_balances s caddr >?
      0 + env_account_balances s caddr = false)%Z.
      {
        lia.
      }
      rewrite H1.
      assert (H_winner_none: env_contracts s (winner cstate) = None).
      { 
        destruct (env_contracts s (winner cstate)) eqn:H_env.
        - exfalso.
          apply (contract_addr_format (winner cstate) w) in H_env; eauto.
          congruence.
        - reflexivity.
      }
      rewrite H_winner_none.
      rewrite H_winner_eoa.
      simpl.
      eauto.
  Qed.

  Lemma winner_call_Claim_transition_state_correct:
    forall (s s':ChainState) cstate,
      contract_state s caddr = Some cstate ->
      cstate.(balance) >= cstate.(targetAmount) ->
      readyToStepState miner contract caddr s0 s ->
      transition miner s (winner_call_ClaimReward cstate) = Ok s' ->
      funds s' caddr = 0.
  Proof.
    intros * Hcs_s Hbal Hready Htrans.
    pose proof Hready.
    destruct H as [Htrc_s Hqueue_s].
    assert (Hact_call : is_call_act ((winner_call_ClaimReward cstate)) = true).
    {
      unfold is_call_act.
      unfold winner_call_ClaimReward.
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
    assert(H_miner_eoa : address_is_contract miner = false).
    {
      eapply address_not_contract_negb;eauto.
    }
    assert(H_winer_eoa : address_is_contract (winner cstate) = false).
    {
      eapply transition_reachable_impl_reachable in Htrc_s.
      eapply winner_eoa_after_target_forall in Htrc_s.
      eapply address_not_contract_negb.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
    }
    assert( H_caddr_not_EOA : address_is_contract caddr = true).
    {
      eapply contract_addr_format in Hec_s;eauto.
      eapply transition_reachable_impl_reachable in Htrc_s;eauto.  
    }
    eapply deployed_contract_state_typed in Hec_s';eauto.
    destruct Hec_s' as [cstate_s' Hcs_s'].
    unfold transition in Htrans.
    unfold queue_isb_empty in Htrans.
    rewrite Hqueue_s in Htrans.
    rewrite Hact_call in Htrans.
    destruct (evaluate_action true s (get_valid_header miner s)
    [winner_call_ClaimReward cstate ]) eqn : H_exec;try congruence.
    unfold evaluate_action in H_exec.
    rewrite get_valid_header_is_valid_header in H_exec;eauto.
    destruct (find_origin_neq_from [winner_call_ClaimReward cstate]) ; try congruence.
    destruct (find_invalid_root_action [winner_call_ClaimReward cstate]);try congruence.
    set (mid_state := {|
      chain_state_env := add_new_block_to_env (get_valid_header miner s) s;
      chain_state_queue := [winner_call_ClaimReward cstate]
    |}) in H_exec.
    simpl in *.
    destruct(send_or_call (winner cstate) (winner cstate) caddr 0
    (Some (serialize ClaimReward))
    (add_new_block_to_env (get_valid_header miner s) s)) eqn : H_send_or_call_ClaimReward;try congruence.
    unfold send_or_call in  H_send_or_call_ClaimReward.
    simpl in H_send_or_call_ClaimReward.
    destruct_address_eq;simpl in *;try congruence;intuition.
    (* 
      e: winner cstate = miner
      n: caddr = winner cstate -> False
      e0: caddr = caddr
      n0: caddr = miner -> False
    *)
    eapply address_not_contract_negb in H_miner.
    destruct(0 >? miner_reward + env_account_balances s (winner cstate))%Z;try congruence.
    rewrite Hec_s in H_send_or_call_ClaimReward.
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
          ctx_origin := winner cstate;
          ctx_from := winner cstate;
          ctx_contract_address := caddr;
          ctx_contract_balance := 0 + env_account_balances s caddr;
          ctx_amount := 0
        |} s1 (Some (serialize ClaimReward)))) eqn : H_wc_receive_s1;try congruence.
    unfold weak_error_to_error_receive in H_wc_receive_s1.
    unfold bind_error in H_wc_receive_s1.
    destruct (wc_receive contract
    (s <| chain_height := S (chain_height s) |> <| current_slot :=
      (current_slot s + 1)%nat |> <| finalized_height :=
      finalized_height s |>)
    {|
      ctx_origin := winner cstate;
      ctx_from := winner cstate;
      ctx_contract_address := caddr;
      ctx_contract_balance := 0 + env_account_balances s caddr;
      ctx_amount := 0
    |} s1 (Some (serialize ClaimReward)))
      eqn : H_wc_receive_s1';try congruence.
    
    set (cchain := s <| chain_height := S (chain_height s) |> <| current_slot :=
    (current_slot s + 1)%nat |> <| finalized_height :=
    finalized_height s |>) in H_wc_receive_s1'.
    set (cctx := {|
    ctx_origin := winner cstate;
    ctx_from := winner cstate;
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
    destruct ( require_no_self_call cctx) eqn : requirements_check;try congruence.
    reduce_claimReward .
    inversion receive_some.
    subst.
    inversion H_wc_receive_s1;subst.
    inversion H_send_or_call_ClaimReward;subst.
    simpl in H_exec.
    destruct ( send_or_call (winner cstate) caddr (winner cstate)
    (0 + env_account_balances s caddr) None
    (set_contract_state caddr
       (serialize
          {|
            targetAmount := targetAmount prev_state_strong;
            balance := balance prev_state_strong;
            winner := winner prev_state_strong
          |})
       (transfer_balance (winner cstate) caddr 0
          (add_new_block_to_env (get_valid_header (winner cstate) s) s)))) eqn : H_send_or_call_None;try congruence.
    unfold send_or_call in H_send_or_call_None.
    destruct_match in H_send_or_call_None;try congruence.
    destruct_match in H_send_or_call_None;try congruence.
    destruct (
      env_contracts
      (set_contract_state caddr
       (serialize
          {|
            targetAmount := targetAmount prev_state_strong;
            balance := balance prev_state_strong;
            winner := winner prev_state_strong
          |})
       (transfer_balance (winner cstate) caddr 0
          (add_new_block_to_env (get_valid_header (winner cstate) s) s)))
      (winner prev_state_strong) ) 
    eqn : H_none_wc.
    set ( mid_env:=
      (set_contract_state caddr
      (serialize
         {|
           targetAmount := targetAmount prev_state_strong;
           balance := balance prev_state_strong;
           winner := winner prev_state_strong
         |})
      (transfer_balance (winner cstate) caddr 0
         (add_new_block_to_env (get_valid_header (winner cstate) s) s)))) 
    in H_none_wc.
    set (
      mid_mid_end_state := {|
      chain_state_env := mid_env;
      chain_state_queue :=
        [{|
          act_origin := winner cstate;
          act_from := caddr;
          act_body :=
            act_transfer 
              (winner prev_state_strong) 
              (0 + env_account_balances s caddr)
        |}]
      |}
    ).
    assert(Hreachable_through_s'_mid_mid_end_state : reachable_through s mid_mid_end_state).
    {
      assert(step_s'_mid : ChainStep s mid_state).
      {
        eapply (step_block s mid_state  (get_valid_header (winner cstate) s));eauto.
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
        destruct_address_eq;cbn in *;try congruence.
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
        eapply (step_action mid_state mid_mid_end_state (winner_call_ClaimReward cstate) [] 
        [{|
        act_origin := winner cstate;
        act_from := caddr;
        act_body :=
          act_transfer (winner prev_state_strong)
            (0 + env_account_balances s caddr)
      |}] )
        ;eauto.
        eapply (eval_call (winner cstate) (winner cstate) caddr 0 
          (contract:WeakContract) (Some (serialize ClaimReward))
          ( s1) (serialize
                {|
                  targetAmount := targetAmount prev_state_strong;
                  balance := balance prev_state_strong;
                  winner := winner prev_state_strong
                |}) 
                [act_transfer (winner prev_state_strong)
                (0 + env_account_balances s caddr)]);eauto;intuition.
         
        eapply reachable_through_reachable in H.
        eapply (account_balance_nonnegative mid_state (winner cstate)) in H.
        lia.
        unfold wc_receive.
        simpl.
        destruct_address_eq;cbn in *;try congruence;
        simpl.
        unfold result_of_option .
        rewrite deser_state.
        rewrite deserialize_serialize.
        unfold error_to_weak_error.
        unfold bind_error.
        unfold receive.
        unfold require_no_self_call.
        simpl.
        destruct_address_eq;eauto;cbn in *;try congruence.
        simpl.
        unfold claimReward.
        simpl.
        unfold require_winner.
        simpl.
        inversion Hcstate_s_t0;subst.
        destruct_address_eq;cbn in *;try congruence.
        simpl.
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
    eapply (address_not_contract_not_wc (winner prev_state_strong)) in Hreachable_mid_mid.
    intuition.
    intuition.
    inversion  Hcstate_s_t0.
    subst.
    rewrite H_winer_eoa in H_send_or_call_None.
    rewrite H_none_wc in H_send_or_call_None.
    inversion H_send_or_call_None;subst.
    simpl in H_exec.
    inversion H_exec;subst.
    inversion Htrans.
    destruct_address_eq;eauto;cbn in *;try congruence.
    unfold transfer_balance in *.
    simpl in *.
    unfold funds.
    simpl.
    destruct_address_eq;cbn in *;try congruence.
    lia.
    (* 
      n: sender cstate <> miner
      n0: caddr <> sender cstate
      e: caddr = caddr
      n1: caddr <> miner
    *)
    eapply address_not_contract_negb in H_miner.
    destruct(0 >? env_account_balances s (winner cstate))%Z;try congruence.
    rewrite Hec_s in H_send_or_call_ClaimReward.
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
          ctx_origin := winner cstate;
          ctx_from := winner cstate;
          ctx_contract_address := caddr;
          ctx_contract_balance := 0 + env_account_balances s caddr;
          ctx_amount := 0
        |} s1 (Some (serialize ClaimReward)))) eqn : H_wc_receive_s1;try congruence.
    unfold weak_error_to_error_receive in H_wc_receive_s1.
    unfold bind_error in H_wc_receive_s1.
    destruct (wc_receive contract
    (s <| chain_height := S (chain_height s) |> <| current_slot :=
      (current_slot s + 1)%nat |> <| finalized_height :=
      finalized_height s |>)
    {|
      ctx_origin := winner cstate;
      ctx_from := winner cstate;
      ctx_contract_address := caddr;
      ctx_contract_balance := 0 + env_account_balances s caddr;
      ctx_amount := 0
    |} s1 (Some (serialize ClaimReward)))
      eqn : H_wc_receive_s1';try congruence.
    
    set (cchain := s <| chain_height := S (chain_height s) |> <| current_slot :=
    (current_slot s + 1)%nat |> <| finalized_height :=
    finalized_height s |>) in H_wc_receive_s1'.
    set (cctx := {|
    ctx_origin := winner cstate;
    ctx_from := winner cstate;
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
    destruct ( require_no_self_call cctx) eqn : requirements_check;try congruence.
    reduce_claimReward .
    inversion receive_some.
    subst.
    inversion H_wc_receive_s1;subst.
    inversion H_send_or_call_ClaimReward;subst.
    simpl in H_exec.
    destruct ( send_or_call (winner cstate) caddr (winner cstate)
    (0 + env_account_balances s caddr) None
    (set_contract_state caddr
       (serialize
          {|
            targetAmount := targetAmount prev_state_strong;
            balance := balance prev_state_strong;
            winner := winner prev_state_strong
          |})
       (transfer_balance (winner cstate) caddr 0
          (add_new_block_to_env (get_valid_header miner s) s)))) eqn : H_send_or_call_None;try congruence.
    unfold send_or_call in H_send_or_call_None.
    destruct_match in H_send_or_call_None;try congruence.
    destruct_match in H_send_or_call_None;try congruence.
    destruct (
      env_contracts
      (set_contract_state caddr
       (serialize
          {|
            targetAmount := targetAmount prev_state_strong;
            balance := balance prev_state_strong;
            winner := winner prev_state_strong
          |})
       (transfer_balance (winner cstate) caddr 0
          (add_new_block_to_env (get_valid_header miner s) s)))
      (winner prev_state_strong) ) 
    eqn : H_none_wc.
    set ( mid_env:=
      (set_contract_state caddr
      (serialize
         {|
           targetAmount := targetAmount prev_state_strong;
           balance := balance prev_state_strong;
           winner := winner prev_state_strong
         |})
      (transfer_balance (winner cstate) caddr 0
         (add_new_block_to_env (get_valid_header miner s) s)))) 
    in H_none_wc.
    set (
      mid_mid_end_state := {|
      chain_state_env := mid_env;
      chain_state_queue :=
        [{|
          act_origin := winner cstate;
          act_from := caddr;
          act_body :=
            act_transfer 
              (winner prev_state_strong) 
              (0 + env_account_balances s caddr)
        |}]
      |}
    ).
    assert(Hreachable_through_s'_mid_mid_end_state : reachable_through s mid_mid_end_state).
    {
      assert(step_s'_mid : ChainStep s mid_state).
      {
        eapply (step_block s mid_state  (get_valid_header miner s));eauto.
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
        destruct_address_eq;cbn in *;try congruence.
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
        eapply (step_action mid_state mid_mid_end_state (winner_call_ClaimReward cstate) [] 
        [{|
        act_origin := winner cstate;
        act_from := caddr;
        act_body :=
          act_transfer (winner prev_state_strong)
            (0 + env_account_balances s caddr)
      |}] )
        ;eauto.
        eapply (eval_call (winner cstate) (winner cstate) caddr 0 
          (contract:WeakContract) (Some (serialize ClaimReward))
          ( s1) (serialize
                {|
                  targetAmount := targetAmount prev_state_strong;
                  balance := balance prev_state_strong;
                  winner := winner prev_state_strong
                |}) 
                [act_transfer (winner prev_state_strong)
                (0 + env_account_balances s caddr)]);eauto;intuition.
         
        eapply reachable_through_reachable in H.
        eapply (account_balance_nonnegative mid_state (winner cstate)) in H.
        lia.
        unfold wc_receive.
        simpl.
        destruct_address_eq;cbn in *;try congruence;
        simpl.
        unfold result_of_option .
        rewrite deser_state.
        rewrite deserialize_serialize.
        unfold error_to_weak_error.
        unfold bind_error.
        unfold receive.
        unfold require_no_self_call.
        simpl.
        destruct_address_eq;cbn in *;eauto;try congruence.
        simpl.
        unfold claimReward.
        simpl.
        unfold require_winner.
        simpl.
        inversion Hcstate_s_t0;subst.
        destruct_address_eq;cbn in *;try congruence.
        simpl.
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
    eapply (address_not_contract_not_wc (winner prev_state_strong)) in Hreachable_mid_mid.
    intuition.
    intuition.
    inversion  Hcstate_s_t0.
    subst.
    rewrite H_winer_eoa in H_send_or_call_None.
    rewrite H_none_wc in H_send_or_call_None.
    inversion H_send_or_call_None;subst.
    simpl in H_exec.
    inversion H_exec;subst.
    inversion Htrans.
    destruct_address_eq;cbn in *;eauto;try congruence.
    unfold transfer_balance in *.
    simpl in *.
    unfold funds.
    simpl.
    destruct_address_eq;cbn in *;try congruence.
    lia.
  Qed.

  Lemma user_call_Deposit_transition_correct:
  forall (s:ChainState) cstate,
    contract_state s caddr = Some cstate ->
    cstate.(balance) < cstate.(targetAmount) ->
    readyToStepState miner contract caddr s0 s ->
    exists s', 
      transition miner s (user_call_Deposit cstate) = Ok s'.
  Proof.
    intros * Hcs_s Hbal_state Hready_state_s.
    eapply address_not_contract_negb in H_miner as H_miner_eoa.
    unfold transition.
    unfold queue_isb_empty.
    pose proof Hready_state_s.
    unfold readyToStepState in H.
    destruct H as [Htrc_s Hqueue_s].
    rewrite Hqueue_s.
    rewrite user_call_Deposit_is_call_act.
    unfold evaluate_action.
    rewrite get_valid_header_is_valid_header;eauto.
    unfold user_call_Deposit .
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
    assert(H_constans:cstate.(targetAmount) = init_cstate.(targetAmount) ).
    {
      eapply transition_reachable_impl_reachable in Htrc_s.
      unfold readyToStepState in Hready_state_s.
      destruct_and_split.
      eapply transition_reachable_impl_reachable_through in H.
      eapply contract_constants_reachable_through in H;eauto.
      destruct_and_split.
      rewrite H in Hcs_s.
      inversion Hcs_s.
      subst.
      intuition.
      eauto.
      eauto.
    }
    eapply address_not_contract_negb in user_eoa as H_user_eoa.
    rewrite H_user_eoa.
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
    destruct_address_eq;cbn in *;try congruence.
    + assert ((1 >? miner_reward + env_account_balances s user)%Z 
                = false).
      {
        unfold miner_reward.
        eapply (account_balance_nonnegative s user) in Hrc_s.
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
      unfold require_no_self_call.
      simpl.
      destruct_address_eq;cbn in *;try congruence.
      simpl.
      unfold deposit.
      simpl.
      unfold require_ctx_from_eoa.
      simpl.
      cbn.
      rewrite user_eoa.
      assert (balance cstate + 1 <=? targetAmount cstate = true).
      {
        intuition.
      }
      rewrite H0.
      destruct(balance cstate + 1 =? targetAmount cstate).
      eauto.
      simpl.
      eauto.
    + assert ((1 >? env_account_balances s user)%Z 
                = false).
      {
        unfold miner_reward.
        eapply (account_balance_nonnegative s user) in Hrc_s.
        specialize(user_bal s).
        unfold funds in user_bal.
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
      unfold require_no_self_call.
      simpl.
      destruct_address_eq;cbn in *;try congruence.
      simpl.
      unfold require_ctx_from_eoa.
      simpl.
      unfold deposit.
      simpl.
      unfold require_ctx_from_eoa.
      simpl.
      cbn.
      rewrite user_eoa.
      assert (balance cstate + 1 <=? targetAmount cstate = true).
      {
        intuition.
      }
      rewrite H0.
      destruct(balance cstate + 1 =? targetAmount cstate).
      eauto.
      simpl.
      eauto.
  Qed.

  Lemma user_call_Deposit_state_correct:
    forall (s s':ChainState) cstate,
      contract_state s caddr = Some cstate ->
      cstate.(balance) < cstate.(targetAmount) ->
      readyToStepState miner contract caddr s0 s ->
      transition miner s (user_call_Deposit cstate) = Ok s' ->
      exists cstate',
        contract_state s' caddr = Some cstate' /\
        cstate'.(balance) = cstate.(balance) + 1.
  Proof.
    intros * Hcs_s Hbal Hready Htrans.
    pose proof Hready.
    destruct H as [Htrc_s Hqueue_s].
    assert (Hact_call : is_call_act ((user_call_Deposit cstate)) = true).
    {
      unfold is_call_act.
      unfold user_call_Deposit.
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
    assert( H_caddr_not_EOA : address_is_contract caddr = true).
    {
      eapply contract_addr_format in Hec_s.
      eauto.
      eapply transition_reachable_impl_reachable in Htrc_s;eauto.
    }
    eapply deployed_contract_state_typed in Hec_s';eauto.
    eapply address_not_contract_negb in H_miner as H_miner_eoa.
    destruct Hec_s' as [cstate_s' Hcs_s'].
    exists cstate_s'.
    split.
    eauto.
    unfold transition in Htrans.
    unfold queue_isb_empty in Htrans.
    rewrite Hqueue_s in Htrans.
    rewrite Hact_call in Htrans.
    destruct (evaluate_action true s (get_valid_header miner s)
    [user_call_Deposit cstate]) eqn : H_exec;try congruence.
    unfold evaluate_action in H_exec.
    rewrite get_valid_header_is_valid_header in H_exec;eauto.
    destruct (find_origin_neq_from [user_call_Deposit cstate]) ; try congruence.
    destruct (find_invalid_root_action [user_call_Deposit cstate]);try congruence.
    set (mid_state := {|
      chain_state_env := add_new_block_to_env (get_valid_header miner s) s;
      chain_state_queue := [user_call_Deposit cstate]
    |}) in H_exec.
    simpl in *.
    destruct(send_or_call user user caddr 1 (Some (serialize Deposit))
    (add_new_block_to_env (get_valid_header miner s) s)) eqn : H_send_or_call_RejectItem;try congruence.
    unfold send_or_call in  H_send_or_call_RejectItem.
    simpl in H_send_or_call_RejectItem.
    destruct_address_eq;simpl in *;try congruence.
    (* 
        e: user = miner
        n: caddr <> user
        e0: caddr = caddr
        n0: caddr <> miner
    *)
    eapply address_not_contract_negb in H_miner.
    destruct(1 >? miner_reward + env_account_balances s user)%Z;try congruence.
    rewrite Hec_s in H_send_or_call_RejectItem.
    assert(Hcstate_s_t0:contract_state s caddr = Some cstate) by eauto.
    unfold contract_state in Hcstate_s_t0.
    simpl in Hcstate_s_t0.
    destruct (env_contract_states s caddr) eqn : Hcstate_s_t0';try congruence.
    destruct (weak_error_to_error_receive
    (wc_receive contract
       (s <| chain_height := 
        S (chain_height s) |> <| current_slot
        := (current_slot s + 1)%nat |> <|
        finalized_height := 
        finalized_height s |>)
       {|
         ctx_origin := user;
         ctx_from := user;
         ctx_contract_address := caddr;
         ctx_contract_balance :=
           1 + env_account_balances s caddr;
         ctx_amount := 1
       |} s1 (Some (serialize Deposit)))) eqn : H_wc_receive_s1;try congruence.
    unfold weak_error_to_error_receive in H_wc_receive_s1.
    unfold bind_error in H_wc_receive_s1.
    destruct (wc_receive contract
    (s <| chain_height := S (chain_height s) |> <|
     current_slot := (current_slot s + 1)%nat |> <|
     finalized_height := finalized_height s |>)
    {|
      ctx_origin := user;
      ctx_from := user;
      ctx_contract_address := caddr;
      ctx_contract_balance :=
        1 + env_account_balances s caddr;
      ctx_amount := 1
    |} s1 (Some (serialize Deposit)))
      eqn : H_wc_receive_s1';try congruence.
    
    set (cchain := s <| chain_height := S (chain_height s) |> <| current_slot :=
    (current_slot s + 1)%nat |> <| finalized_height :=
    finalized_height s |>) in H_wc_receive_s1'.
    
    set (cctx := {|
                       ctx_origin := user;
                       ctx_from := user;
                       ctx_contract_address := caddr;
                       ctx_contract_balance :=
                         1 + env_account_balances s caddr;
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
    destruct (require_no_self_call cctx) eqn : requirements_check;try congruence.
    reduce_deposit.
    inversion receive_some.
    subst.
    inversion H_wc_receive_s1;subst.
    inversion H_send_or_call_RejectItem;subst.
    simpl in H_exec.
    inversion H_exec.
    inversion  Hcstate_s_t0.
    subst.
    simpl in H_exec.
    inversion H_exec;subst.
    inversion Htrans.
    subst.
    inversion Hcs_s'.
    unfold contract_state in H0.
    simpl in H0.
    destruct_address_eq;cbn in *;eauto.
    setoid_rewrite deserialize_serialize in H0.
    inversion H0.
    intuition.
    intuition.
    inversion receive_some.
    subst.
    inversion H_wc_receive_s1;subst.
    inversion H_send_or_call_RejectItem;subst.
    simpl in H_exec.
    inversion H_exec.
    inversion  Hcstate_s_t0.
    subst.
    simpl in H_exec.
    inversion H_exec;subst.
    inversion Htrans.
    subst.
    inversion Hcs_s'.
    unfold contract_state in H0.
    simpl in H0.
    destruct_address_eq;cbn in *;eauto.
    setoid_rewrite deserialize_serialize in H0.
    inversion H0.
    intuition.
    intuition.
  

    (* caddr = user *)
    eapply address_not_contract_negb in user_eoa.
    congruence.
    (* 
      n: sender cstate <> miner
      n0: caddr <> sender cstate
      e: caddr = caddr
      n1: caddr <> miner
    *)
    
    eapply address_not_contract_negb in H_miner.
    destruct(1 >? env_account_balances s user)%Z;try congruence.
    rewrite Hec_s in H_send_or_call_RejectItem.
    assert(Hcstate_s_t0:contract_state s caddr = Some cstate) by eauto.
    unfold contract_state in Hcstate_s_t0.
    simpl in Hcstate_s_t0.
    destruct (env_contract_states s caddr) eqn : Hcstate_s_t0';try congruence.
    destruct (weak_error_to_error_receive
    (wc_receive contract
       (s <| chain_height := 
        S (chain_height s) |> <| current_slot
        := (current_slot s + 1)%nat |> <|
        finalized_height := 
        finalized_height s |>)
       {|
         ctx_origin := user;
         ctx_from := user;
         ctx_contract_address := caddr;
         ctx_contract_balance :=
           1 + env_account_balances s caddr;
         ctx_amount := 1
       |} s1 (Some (serialize Deposit)))) eqn : H_wc_receive_s1;try congruence.
    unfold weak_error_to_error_receive in H_wc_receive_s1.
    unfold bind_error in H_wc_receive_s1.
    destruct (wc_receive contract
    (s <| chain_height := S (chain_height s) |> <|
     current_slot := (current_slot s + 1)%nat |> <|
     finalized_height := finalized_height s |>)
    {|
      ctx_origin := user;
      ctx_from := user;
      ctx_contract_address := caddr;
      ctx_contract_balance :=
        1 + env_account_balances s caddr;
      ctx_amount := 1
    |} s1 (Some (serialize Deposit)))
      eqn : H_wc_receive_s1';try congruence.
    
    set (cchain := s <| chain_height := S (chain_height s) |> <| current_slot :=
    (current_slot s + 1)%nat |> <| finalized_height :=
    finalized_height s |>) in H_wc_receive_s1'.
    
    set (cctx := {|
                       ctx_origin := user;
                       ctx_from := user;
                       ctx_contract_address := caddr;
                       ctx_contract_balance :=
                         1 + env_account_balances s caddr;
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
    destruct (require_no_self_call cctx) eqn : requirements_check;try congruence.
    reduce_deposit.
    inversion receive_some.
    subst.
    inversion H_wc_receive_s1;subst.
    inversion H_send_or_call_RejectItem;subst.
    simpl in H_exec.
    inversion H_exec.
    inversion  Hcstate_s_t0.
    subst.
    simpl in H_exec.
    inversion H_exec;subst.
    inversion Htrans.
    subst.
    inversion Hcs_s'.
    unfold contract_state in H0.
    simpl in H0.
    destruct_address_eq;cbn in *;eauto.
    setoid_rewrite deserialize_serialize in H0.
    inversion H0.
    intuition.
    intuition.
    inversion receive_some.
    subst.
    inversion H_wc_receive_s1;subst.
    inversion H_send_or_call_RejectItem;subst.
    simpl in H_exec.
    inversion H_exec.
    inversion  Hcstate_s_t0.
    subst.
    simpl in H_exec.
    inversion H_exec;subst.
    inversion Htrans.
    subst.
    inversion Hcs_s'.
    unfold contract_state in H0.
    simpl in H0.
    destruct_address_eq;cbn in *;eauto.
    setoid_rewrite deserialize_serialize in H0.
    inversion H0.
    intuition.
    intuition.
  Qed.

  Lemma user_call_Deposit_funds_correct:
    forall (s s':ChainState) cstate,
      contract_state s caddr = Some cstate ->
      cstate.(balance) < cstate.(targetAmount) ->
      readyToStepState miner contract caddr s0 s ->
      transition miner s (user_call_Deposit cstate) = Ok s' ->
      funds s' caddr = funds s caddr + 1.
  Proof.
    intros * Hcs_s Hbal Hready Htrans.
    pose proof Hready.
    destruct H as [Htrc_s Hqueue_s].
    assert (Hact_call : is_call_act ((user_call_Deposit cstate)) = true).
    {
      unfold is_call_act.
      unfold user_call_Deposit.
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
    assert( H_caddr_not_EOA : address_is_contract caddr = true).
    {
      eapply contract_addr_format in Hec_s.
      eauto.
      eapply transition_reachable_impl_reachable in Htrc_s;eauto.
    }
    eapply deployed_contract_state_typed in Hec_s';eauto.
    eapply address_not_contract_negb in H_miner as H_miner_eoa.
    destruct Hec_s' as [cstate_s' Hcs_s'].
    unfold funds.
    unfold transition in Htrans.
    unfold queue_isb_empty in Htrans.
    rewrite Hqueue_s in Htrans.
    rewrite Hact_call in Htrans.
    destruct (evaluate_action true s (get_valid_header miner s)
    [user_call_Deposit cstate]) eqn : H_exec;try congruence.
    unfold evaluate_action in H_exec.
    rewrite get_valid_header_is_valid_header in H_exec;eauto.
    destruct (find_origin_neq_from [user_call_Deposit cstate]) ; try congruence.
    destruct (find_invalid_root_action [user_call_Deposit cstate]);try congruence.
    set (mid_state := {|
      chain_state_env := add_new_block_to_env (get_valid_header miner s) s;
      chain_state_queue := [user_call_Deposit cstate]
    |}) in H_exec.
    simpl in *.
    destruct(send_or_call user user caddr 1 (Some (serialize Deposit))
    (add_new_block_to_env (get_valid_header miner s) s)) eqn : H_send_or_call_RejectItem;try congruence.
    unfold send_or_call in  H_send_or_call_RejectItem.
    simpl in H_send_or_call_RejectItem.
    destruct_address_eq;simpl in *;try congruence.
    (* 
        e: user = miner
        n: caddr <> user
        e0: caddr = caddr
        n0: caddr <> miner
    *)
    eapply address_not_contract_negb in H_miner.
    destruct(1 >? miner_reward + env_account_balances s user)%Z;try congruence.
    rewrite Hec_s in H_send_or_call_RejectItem.
    assert(Hcstate_s_t0:contract_state s caddr = Some cstate) by eauto.
    unfold contract_state in Hcstate_s_t0.
    simpl in Hcstate_s_t0.
    destruct (env_contract_states s caddr) eqn : Hcstate_s_t0';try congruence.
    destruct (weak_error_to_error_receive
    (wc_receive contract
       (s <| chain_height := 
        S (chain_height s) |> <| current_slot
        := (current_slot s + 1)%nat |> <|
        finalized_height := 
        finalized_height s |>)
       {|
         ctx_origin := user;
         ctx_from := user;
         ctx_contract_address := caddr;
         ctx_contract_balance :=
           1 + env_account_balances s caddr;
         ctx_amount := 1
       |} s1 (Some (serialize Deposit)))) eqn : H_wc_receive_s1;try congruence.
    unfold weak_error_to_error_receive in H_wc_receive_s1.
    unfold bind_error in H_wc_receive_s1.
    destruct (wc_receive contract
    (s <| chain_height := S (chain_height s) |> <|
     current_slot := (current_slot s + 1)%nat |> <|
     finalized_height := finalized_height s |>)
    {|
      ctx_origin := user;
      ctx_from := user;
      ctx_contract_address := caddr;
      ctx_contract_balance :=
        1 + env_account_balances s caddr;
      ctx_amount := 1
    |} s1 (Some (serialize Deposit)))
      eqn : H_wc_receive_s1';try congruence.
    
    set (cchain := s <| chain_height := S (chain_height s) |> <| current_slot :=
    (current_slot s + 1)%nat |> <| finalized_height :=
    finalized_height s |>) in H_wc_receive_s1'.
    
    set (cctx := {|
                       ctx_origin := user;
                       ctx_from := user;
                       ctx_contract_address := caddr;
                       ctx_contract_balance :=
                         1 + env_account_balances s caddr;
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
    destruct (require_no_self_call cctx) eqn : requirements_check;try congruence.
    reduce_deposit.
    inversion receive_some.
    subst.
    inversion H_wc_receive_s1;subst.
    inversion H_send_or_call_RejectItem;subst.
    simpl in H_exec.
    inversion H_exec.
    inversion  Hcstate_s_t0.
    subst.
    simpl in H_exec.
    inversion H_exec;subst.
    inversion Htrans.
    simpl.
    destruct_address_eq;cbn in *;eauto;try congruence;try lia.
    inversion receive_some.
    subst.
    inversion H_wc_receive_s1;subst.
    inversion H_send_or_call_RejectItem;subst.
    simpl in H_exec.
    inversion H_exec.
    inversion  Hcstate_s_t0.
    subst.
    simpl in H_exec.
    inversion H_exec;subst.
    inversion Htrans.
    simpl.
    destruct_address_eq;eauto;cbn in *;try congruence;try lia.
    

    (* caddr = user *)
    eapply address_not_contract_negb in user_eoa.
    congruence.
    (* 
      n: sender cstate <> miner
      n0: caddr <> sender cstate
      e: caddr = caddr
      n1: caddr <> miner
    *)
    
    eapply address_not_contract_negb in H_miner.
    destruct(1 >? env_account_balances s user)%Z;try congruence.
    rewrite Hec_s in H_send_or_call_RejectItem.
    assert(Hcstate_s_t0:contract_state s caddr = Some cstate) by eauto.
    unfold contract_state in Hcstate_s_t0.
    simpl in Hcstate_s_t0.
    destruct (env_contract_states s caddr) eqn : Hcstate_s_t0';try congruence.
    destruct (weak_error_to_error_receive
    (wc_receive contract
       (s <| chain_height := 
        S (chain_height s) |> <| current_slot
        := (current_slot s + 1)%nat |> <|
        finalized_height := 
        finalized_height s |>)
       {|
         ctx_origin := user;
         ctx_from := user;
         ctx_contract_address := caddr;
         ctx_contract_balance :=
           1 + env_account_balances s caddr;
         ctx_amount := 1
       |} s1 (Some (serialize Deposit)))) eqn : H_wc_receive_s1;try congruence.
    unfold weak_error_to_error_receive in H_wc_receive_s1.
    unfold bind_error in H_wc_receive_s1.
    destruct (wc_receive contract
    (s <| chain_height := S (chain_height s) |> <|
     current_slot := (current_slot s + 1)%nat |> <|
     finalized_height := finalized_height s |>)
    {|
      ctx_origin := user;
      ctx_from := user;
      ctx_contract_address := caddr;
      ctx_contract_balance :=
        1 + env_account_balances s caddr;
      ctx_amount := 1
    |} s1 (Some (serialize Deposit)))
      eqn : H_wc_receive_s1';try congruence.
    
    set (cchain := s <| chain_height := S (chain_height s) |> <| current_slot :=
    (current_slot s + 1)%nat |> <| finalized_height :=
    finalized_height s |>) in H_wc_receive_s1'.
    
    set (cctx := {|
                       ctx_origin := user;
                       ctx_from := user;
                       ctx_contract_address := caddr;
                       ctx_contract_balance :=
                         1 + env_account_balances s caddr;
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
    destruct (require_no_self_call cctx) eqn : requirements_check;try congruence.
    reduce_deposit.
    inversion receive_some.
    subst.
    inversion H_wc_receive_s1;subst.
    inversion H_send_or_call_RejectItem;subst.
    simpl in H_exec.
    inversion H_exec.
    inversion  Hcstate_s_t0.
    subst.
    simpl in H_exec.
    inversion H_exec;subst.
    inversion Htrans.
    simpl.
    destruct_address_eq;eauto;cbn in *;try congruence;try lia.
    inversion receive_some.
    subst.
    inversion H_wc_receive_s1;subst.
    inversion H_send_or_call_RejectItem;subst.
    simpl in H_exec.
    inversion H_exec.
    inversion  Hcstate_s_t0.
    subst.
    simpl in H_exec.
    inversion H_exec;subst.
    inversion Htrans.
    simpl.
    destruct_address_eq;eauto;try congruence;try lia.
  Qed.

  Lemma user_call_Deposit_state_funds_correct:
    forall (s s':ChainState) cstate,
      contract_state s caddr = Some cstate ->
      cstate.(balance) < cstate.(targetAmount) ->
      readyToStepState miner contract caddr s0 s ->
      transition miner s (user_call_Deposit cstate) = Ok s' ->
      funds s' caddr = funds s caddr + 1 /\
      (exists cstate',
        contract_state s' caddr = Some cstate' /\
        cstate'.(balance) = cstate.(balance) + 1).
  Proof.
    intros.
    split.
    eapply user_call_Deposit_funds_correct;eauto.
    eapply user_call_Deposit_state_correct;eauto.
  Qed.

  Lemma user_call_Deposit_change_winner_state_correct:
    forall (s s':ChainState) cstate,
      contract_state s caddr = Some cstate ->
      cstate.(balance) < cstate.(targetAmount) ->
      readyToStepState miner contract caddr s0 s ->
      transition miner s (user_call_Deposit cstate) = Ok s' ->
      exists cstate',
        contract_state s' caddr = Some cstate' /\
        (cstate'.(balance) >= cstate'.(targetAmount) -> 
          cstate'.(winner) = user).
  Proof.
    intros * Hcs_s Hbal Hready Htrans.
    pose proof Hready.
    destruct H as [Htrc_s Hqueue_s].
    assert (Hact_call : is_call_act ((user_call_Deposit cstate)) = true).
    {
      unfold is_call_act.
      unfold user_call_Deposit.
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
    assert( H_caddr_not_EOA : address_is_contract caddr = true).
    {
      eapply contract_addr_format in Hec_s.
      eauto.
      eapply transition_reachable_impl_reachable in Htrc_s;eauto.
    }
    eapply deployed_contract_state_typed in Hec_s';eauto.
    eapply address_not_contract_negb in H_miner as H_miner_eoa.
    destruct Hec_s' as [cstate_s' Hcs_s'].
    exists cstate_s'.
    split.
    eauto.
    unfold transition in Htrans.
    unfold queue_isb_empty in Htrans.
    rewrite Hqueue_s in Htrans.
    rewrite Hact_call in Htrans.
    destruct (evaluate_action true s (get_valid_header miner s)
    [user_call_Deposit cstate]) eqn : H_exec;try congruence.
    unfold evaluate_action in H_exec.
    rewrite get_valid_header_is_valid_header in H_exec;eauto.
    destruct (find_origin_neq_from [user_call_Deposit cstate]) ; try congruence.
    destruct (find_invalid_root_action [user_call_Deposit cstate]);try congruence.
    set (mid_state := {|
      chain_state_env := add_new_block_to_env (get_valid_header miner s) s;
      chain_state_queue := [user_call_Deposit cstate]
    |}) in H_exec.
    simpl in *.
    destruct(send_or_call user user caddr 1 (Some (serialize Deposit))
    (add_new_block_to_env (get_valid_header miner s) s)) eqn : H_send_or_call_RejectItem;try congruence.
    unfold send_or_call in  H_send_or_call_RejectItem.
    simpl in H_send_or_call_RejectItem.
    destruct_address_eq;simpl in *;try congruence.
    (* 
        e: user = miner
        n: caddr <> user
        e0: caddr = caddr
        n0: caddr <> miner
    *)
    eapply address_not_contract_negb in H_miner.
    destruct(1 >? miner_reward + env_account_balances s user)%Z;try congruence.
    rewrite Hec_s in H_send_or_call_RejectItem.
    assert(Hcstate_s_t0:contract_state s caddr = Some cstate) by eauto.
    unfold contract_state in Hcstate_s_t0.
    simpl in Hcstate_s_t0.
    destruct (env_contract_states s caddr) eqn : Hcstate_s_t0';try congruence.
    destruct (weak_error_to_error_receive
    (wc_receive contract
       (s <| chain_height := 
        S (chain_height s) |> <| current_slot
        := (current_slot s + 1)%nat |> <|
        finalized_height := 
        finalized_height s |>)
       {|
         ctx_origin := user;
         ctx_from := user;
         ctx_contract_address := caddr;
         ctx_contract_balance :=
           1 + env_account_balances s caddr;
         ctx_amount := 1
       |} s1 (Some (serialize Deposit)))) eqn : H_wc_receive_s1;try congruence.
    unfold weak_error_to_error_receive in H_wc_receive_s1.
    unfold bind_error in H_wc_receive_s1.
    destruct (wc_receive contract
    (s <| chain_height := S (chain_height s) |> <|
     current_slot := (current_slot s + 1)%nat |> <|
     finalized_height := finalized_height s |>)
    {|
      ctx_origin := user;
      ctx_from := user;
      ctx_contract_address := caddr;
      ctx_contract_balance :=
        1 + env_account_balances s caddr;
      ctx_amount := 1
    |} s1 (Some (serialize Deposit)))
      eqn : H_wc_receive_s1';try congruence.
    
    set (cchain := s <| chain_height := S (chain_height s) |> <| current_slot :=
    (current_slot s + 1)%nat |> <| finalized_height :=
    finalized_height s |>) in H_wc_receive_s1'.
    
    set (cctx := {|
                       ctx_origin := user;
                       ctx_from := user;
                       ctx_contract_address := caddr;
                       ctx_contract_balance :=
                         1 + env_account_balances s caddr;
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
    destruct (require_no_self_call cctx) eqn : requirements_check;try congruence.
    reduce_deposit.
    inversion receive_some.
    subst.
    inversion H_wc_receive_s1;subst.
    inversion H_send_or_call_RejectItem;subst.
    simpl in H_exec.
    inversion H_exec.
    inversion  Hcstate_s_t0.
    subst.
    simpl in H_exec.
    inversion H_exec;subst.
    inversion Htrans.
    subst.
    inversion Hcs_s'.
    unfold contract_state in H0.
    simpl in H0.
    destruct_address_eq;cbn in *;eauto.
    setoid_rewrite deserialize_serialize in H0.
    inversion H0.
    intuition.
    intuition.
    inversion receive_some.
    subst.
    inversion H_wc_receive_s1;subst.
    inversion H_send_or_call_RejectItem;subst.
    simpl in H_exec.
    inversion H_exec.
    inversion  Hcstate_s_t0.
    subst.
    simpl in H_exec.
    inversion H_exec;subst.
    inversion Htrans.
    subst.
    inversion Hcs_s'.
    unfold contract_state in H0.
    simpl in H0.
    destruct_address_eq;cbn in *;eauto.
    setoid_rewrite deserialize_serialize in H0.
    inversion H0.
    simpl in *.
    intros.
    lia.
    congruence.
  

    (* caddr = user *)
    eapply address_not_contract_negb in user_eoa.
    congruence.
    (* 
      n: sender cstate <> miner
      n0: caddr <> sender cstate
      e: caddr = caddr
      n1: caddr <> miner
    *)
    
    eapply address_not_contract_negb in H_miner.
    destruct(1 >? env_account_balances s user)%Z;try congruence.
    rewrite Hec_s in H_send_or_call_RejectItem.
    assert(Hcstate_s_t0:contract_state s caddr = Some cstate) by eauto.
    unfold contract_state in Hcstate_s_t0.
    simpl in Hcstate_s_t0.
    destruct (env_contract_states s caddr) eqn : Hcstate_s_t0';try congruence.
    destruct (weak_error_to_error_receive
    (wc_receive contract
       (s <| chain_height := 
        S (chain_height s) |> <| current_slot
        := (current_slot s + 1)%nat |> <|
        finalized_height := 
        finalized_height s |>)
       {|
         ctx_origin := user;
         ctx_from := user;
         ctx_contract_address := caddr;
         ctx_contract_balance :=
           1 + env_account_balances s caddr;
         ctx_amount := 1
       |} s1 (Some (serialize Deposit)))) eqn : H_wc_receive_s1;try congruence.
    unfold weak_error_to_error_receive in H_wc_receive_s1.
    unfold bind_error in H_wc_receive_s1.
    destruct (wc_receive contract
    (s <| chain_height := S (chain_height s) |> <|
     current_slot := (current_slot s + 1)%nat |> <|
     finalized_height := finalized_height s |>)
    {|
      ctx_origin := user;
      ctx_from := user;
      ctx_contract_address := caddr;
      ctx_contract_balance :=
        1 + env_account_balances s caddr;
      ctx_amount := 1
    |} s1 (Some (serialize Deposit)))
      eqn : H_wc_receive_s1';try congruence.
    
    set (cchain := s <| chain_height := S (chain_height s) |> <| current_slot :=
    (current_slot s + 1)%nat |> <| finalized_height :=
    finalized_height s |>) in H_wc_receive_s1'.
    
    set (cctx := {|
                       ctx_origin := user;
                       ctx_from := user;
                       ctx_contract_address := caddr;
                       ctx_contract_balance :=
                         1 + env_account_balances s caddr;
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
    destruct (require_no_self_call cctx) eqn : requirements_check;try congruence.
    reduce_deposit.
    inversion receive_some.
    subst.
    inversion H_wc_receive_s1;subst.
    inversion H_send_or_call_RejectItem;subst.
    simpl in H_exec.
    inversion H_exec.
    inversion  Hcstate_s_t0.
    subst.
    simpl in H_exec.
    inversion H_exec;subst.
    inversion Htrans.
    subst.
    inversion Hcs_s'.
    unfold contract_state in H0.
    simpl in H0.
    destruct_address_eq;cbn in *;eauto.
    setoid_rewrite deserialize_serialize in H0.
    inversion H0.
    intuition.
    intuition.
    inversion receive_some.
    subst.
    inversion H_wc_receive_s1;subst.
    inversion H_send_or_call_RejectItem;subst.
    simpl in H_exec.
    inversion H_exec.
    inversion  Hcstate_s_t0.
    subst.
    simpl in H_exec.
    inversion H_exec;subst.
    inversion Htrans.
    subst.
    inversion Hcs_s'.
    unfold contract_state in H0.
    simpl in H0.
    destruct_address_eq;cbn in *;eauto.
    setoid_rewrite deserialize_serialize in H0.
    inversion H0.
    simpl in *.
    intros.
    intuition.
    intros.
    intuition.
  Qed.

  Lemma user_call_ClaimReward_transition_correct:
  forall (s:ChainState) cstate,
    contract_state s caddr = Some cstate ->
    (user = cstate.(winner))%address ->
    readyToStepState miner contract caddr s0 s ->
    exists s', 
      transition miner s (user_call_ClaimReward cstate) = Ok s'.
  Proof.
    intros * Hcs_s Hbal_state Hready_state_s.
    eexists.
    eapply address_not_contract_negb in H_miner as H_miner_eoa.
    unfold transition.
    unfold queue_isb_empty.
    pose proof Hready_state_s.
    unfold readyToStepState in H.
    destruct H as [Htrc_s Hqueue_s].
    rewrite Hqueue_s.
    rewrite user_call_ClaimReward_is_call_act.
    unfold evaluate_action.
    rewrite get_valid_header_is_valid_header;eauto.
    unfold user_call_ClaimReward .
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
    assert(H_constans:cstate.(targetAmount) = init_cstate.(targetAmount) ).
    {
      eapply transition_reachable_impl_reachable in Htrc_s.
      unfold readyToStepState in Hready_state_s.
      destruct_and_split.
      eapply transition_reachable_impl_reachable_through in H.
      eapply contract_constants_reachable_through in H;eauto.
      destruct_and_split.
      rewrite H in Hcs_s.
      inversion Hcs_s.
      subst.
      intuition.
      eauto.
      eauto.
    }
    assert(H_user_eoa : address_is_contract user = false).
    {
      
      eapply address_not_contract_negb.
      eauto.
    }
    rewrite H_user_eoa.
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
    destruct_address_eq;cbn in *;try congruence.
    + assert ((0 >? miner_reward + env_account_balances s user)%Z 
                = false).
      {
        unfold miner_reward.
        eapply (account_balance_nonnegative s user) in Hrc_s.
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
      unfold require_no_self_call.
      simpl.
      destruct_address_eq;cbn in *;try congruence.
      simpl.
      cbn.
      unfold require_ctx_from_eoa.
      simpl.
      unfold claimReward.
      simpl.
      unfold require_winner.
      simpl.
      destruct_address_eq;cbn in *;try congruence;cbn;eauto.
      unfold send_or_call.
      assert(0 + env_account_balances s caddr <? 0 = false).
      {
        eapply (account_balance_nonnegative s caddr) in Hrc_s.
        propify.
        lia.
      }
      rewrite H0.
      simpl.
      destruct_address_eq;cbn in *;try congruence;eauto.
      (* 1 *)
      assert( 0 + env_account_balances s caddr >?
      0 + env_account_balances s caddr = false)%Z.
      {
        lia.
      }
      rewrite H1.
      assert (H_winner_none: env_contracts s user = None).
      { 
        destruct (env_contracts s user) eqn:H_env.
        - exfalso.
          apply (contract_addr_format user w) in H_env; eauto.
          congruence.
        - reflexivity.
      }
      rewrite H_winner_none.
      rewrite H_user_eoa.
      simpl.
      eauto.
    +
      assert ((0 >?  env_account_balances s user)%Z 
                = false).
      {
        unfold miner_reward.
        eapply (account_balance_nonnegative s user) in Hrc_s.
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
      unfold require_no_self_call.
      simpl.
      destruct_address_eq;cbn in *;try congruence.
      simpl.
      cbn.
      unfold require_ctx_from_eoa.
      simpl.
      unfold claimReward.
      simpl.
      unfold require_winner.
      simpl.
      destruct_address_eq;cbn in *;try congruence;cbn;eauto.
      unfold send_or_call.
      assert(0 + env_account_balances s caddr <? 0 = false).
      {
        eapply (account_balance_nonnegative s caddr) in Hrc_s.
        propify.
        lia.
      }
      rewrite H0.
      simpl.
      destruct_address_eq;cbn in *;try congruence;eauto.
      (* 1 *)
      assert( 0 + env_account_balances s caddr >?
      0 + env_account_balances s caddr = false)%Z.
      {
        lia.
      }
      rewrite H1.
      assert (H_winner_none: env_contracts s user = None).
      { 
        destruct (env_contracts s user) eqn:H_env.
        - exfalso.
          apply (contract_addr_format user w) in H_env; eauto.
          congruence.
        - reflexivity.
      }
      rewrite H_winner_none.
      rewrite H_user_eoa.
      simpl.
      eauto.
  Qed.

  Hypothesis H_attacker_cstate : forall (s:ChainState) (cstate : State), 
    contract_state s caddr = Some cstate -> 
    exists (attacker_state : AttackerState),
      env_contracts s attacker_addr = Some (attacker_contract : WeakContract) /\
      contract_state s attacker_addr = Some attacker_state.

  Lemma attacker_call_Fallback_transition_correct:
  forall (s:ChainState) cstate attacker_state,
    contract_state s attacker_addr = Some attacker_state ->
    contract_state s caddr = Some cstate ->
    attacker_state.(close) =false ->
    funds s attacker_addr >= 1 ->
    readyToStepState miner contract caddr s0 s ->
    exists s', 
      transition miner s (attacker_call_Fallback cstate) = Ok s'.
  Proof.
    intros * Hacs_s Hcs_s Hclose Hfunds_a Hready_state_s.
    eapply address_not_contract_negb in H_miner as H_miner_eoa.
    unfold transition.
    unfold queue_isb_empty.
    pose proof Hready_state_s.
    unfold readyToStepState in H.
    destruct H as [Htrc_s Hqueue_s].
    rewrite Hqueue_s.
    rewrite attacker_call_Fallback_is_call_act.
    unfold evaluate_action.
    rewrite get_valid_header_is_valid_header;eauto.
    unfold attacker_call_Fallback .
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
    assert(H_constans:cstate.(targetAmount) = init_cstate.(targetAmount) ).
    {
      eapply transition_reachable_impl_reachable in Htrc_s.
      unfold readyToStepState in Hready_state_s.
      destruct_and_split.
      eapply transition_reachable_impl_reachable_through in H.
      eapply contract_constants_reachable_through in H;eauto.
      destruct_and_split.
      rewrite H in Hcs_s.
      inversion Hcs_s.
      subst.
      intuition.
      eauto.
      eauto.
    }
    assert(H_attacker : address_is_contract attacker = false).
    {
      eapply address_not_contract_negb;eauto.
    }
    
    unfold send_or_call.
    simpl.
    assert( H_caddr_not_EOA : address_is_contract caddr = true).
    {
      eapply contract_addr_format in Hec_s;eauto.
      eapply transition_reachable_impl_reachable in Htrc_s;eauto.  
    }
    assert( H_attacker_caddr_not_EOA : address_is_contract attacker_addr  = true).
    {
      specialize(H_attacker_cstate s cstate Hcs_s).
      destruct H_attacker_cstate as [  Ht].
      destruct H.
      eapply contract_addr_format in H.
      eauto.
      eapply transition_reachable_impl_reachable in Htrc_s;eauto.  
    }
    assert(Hrc_s:reachable s).
    {
      eapply transition_reachable_impl_reachable in Htrc_s;eauto.
    }
    rewrite H_attacker.
    destruct_address_eq;try congruence.
    + assert ((0 >? miner_reward + env_account_balances s attacker)%Z 
                = false).
      {
        unfold miner_reward.
        eapply (account_balance_nonnegative s attacker) in Hrc_s.
        lia.
      }
      rewrite H.
      specialize(H_attacker_cstate s cstate Hcs_s).
      destruct H_attacker_cstate as [attacker_state_t  [Hec_s_att Hcs_s_att]].
      pose proof  Hcs_s_att as Hcs_s_attt.
      rewrite Hec_s_att.
      unfold contract_state in Hcs_s_att.
      simpl in Hcs_s_att.
      destruct (env_contract_states s attacker_addr) eqn : Hecs_s;try congruence.
      simpl.
      rewrite Hcs_s_att.
      simpl.
      setoid_rewrite deserialize_serialize.
      simpl.
      cbn.
      unfold attacker_receive.
      assert(Hclose_t:close attacker_state_t = false).
      {
        rewrite Hacs_s in Hcs_s_attt.
        inversion Hcs_s_attt.
        intuition.
      }
      rewrite Hclose_t.
      simpl.
      unfold send_or_call.
      simpl.
      destruct_address_eq;try congruence.
      assert(1 >? 0 + env_account_balances s attacker_addr = false).
      {
        unfold funds in Hfunds_a.
        lia.
      }
      rewrite H0.
      assert(H_at_con : (target attacker_state_t) = (target Attacker_init_cstate)).
      {
        specialize(Attacker_target_constant s Hrc_s).
        decompose_exists.
        destruct Attacker_target_constant.
        destruct H1.
        rewrite Hcs_s_attt in H1.
        inversion H1.
        subst.
        eauto.
      }
      rewrite H_at_con, H_Attacker_init_cstate, Hec_s.
      simpl.
      rewrite deserialize_serialize.
      assert (Hdes_attc : deserialize (serialize attacker_state_t) = Some attacker_state_t).
      {
        rewrite deserialize_serialize.
        eauto.
      }
      unfold result_of_option .
      destruct (deserialize (serialize attacker_state_t)) eqn : Ht1;try congruence.
      assert(1 >? 0 + env_account_balances s attacker_addr = false).
      {
        unfold funds in Hfunds_a.
        lia.
      }
      rewrite H0.
      assert(H_at_con : (target attacker_state_t) = (target Attacker_init_cstate)).
      {
        specialize(Attacker_target_constant s Hrc_s).
        decompose_exists.
        destruct Attacker_target_constant.
        destruct H1.
        rewrite Hcs_s_attt in H1.
        inversion H1.
        subst.
        eauto.
      }
      rewrite H_at_con, H_Attacker_init_cstate, Hec_s.
      unfold contract_state in Hcs_s.
      simpl in Hcs_s.
      destruct (env_contract_states s caddr) eqn : Ht2;try congruence.
      assert(1 >? 0 + env_account_balances s attacker_addr = false).
      {
        unfold funds in Hfunds_a.
        lia.
      }
      rewrite H0.
      assert(H_at_con : (target attacker_state_t) = (target Attacker_init_cstate)).
      {
        specialize(Attacker_target_constant s Hrc_s).
        decompose_exists.
        destruct Attacker_target_constant.
        destruct H1.
        rewrite Hcs_s_attt in H1.
        inversion H1.
        subst.
        eauto.
      }
      rewrite H_at_con, H_Attacker_init_cstate, Hec_s.
      unfold contract_state in Hcs_s.
      simpl in Hcs_s.
      destruct (env_contract_states s caddr) eqn : Ht2;try congruence.
      simpl.
      rewrite Hcs_s.
      simpl.
      rewrite deserialize_serialize.
      simpl.
      cbn in *.
      unfold receive.
      simpl.
      unfold address_not_contract.
      unfold require_no_self_call.
      simpl.
      destruct_address_eq;cbn in *;try congruence.
      simpl.
      unfold require_ctx_from_eoa.
      simpl.
      cbn.
      eauto.
    +
      assert ((0 >? env_account_balances s attacker)%Z 
                = false).
      {
        unfold miner_reward.
        eapply (account_balance_nonnegative s attacker) in Hrc_s.
        lia.
      }
      rewrite H.
      specialize(H_attacker_cstate s cstate Hcs_s).
      destruct H_attacker_cstate as [attacker_state_t  [Hec_s_att Hcs_s_att]].
      pose proof  Hcs_s_att as Hcs_s_attt.
      rewrite Hec_s_att.
      unfold contract_state in Hcs_s_att.
      simpl in Hcs_s_att.
      destruct (env_contract_states s attacker_addr) eqn : Hecs_s;try congruence.
      simpl.
      rewrite Hcs_s_att.
      simpl.
      setoid_rewrite deserialize_serialize.
      simpl.
      assert(Hclose_t:close attacker_state_t = false).
      {
        rewrite Hacs_s in Hcs_s_attt.
        inversion Hcs_s_attt.
        intuition.
      }
      unfold attacker_receive.
      rewrite Hclose_t.
      simpl.
      unfold send_or_call.
      simpl.
      destruct_address_eq;try congruence.
      assert(1 >? 0 + env_account_balances s attacker_addr = false).
      {
        unfold funds in Hfunds_a.
        lia.
      }
      rewrite H0.
      assert(H_at_con : (target attacker_state_t) = (target Attacker_init_cstate)).
      {
        specialize(Attacker_target_constant s Hrc_s).
        decompose_exists.
        destruct Attacker_target_constant.
        destruct H1.
        rewrite Hcs_s_attt in H1.
        inversion H1.
        subst.
        eauto.
      }
      rewrite H_at_con, H_Attacker_init_cstate, Hec_s.
      simpl.
      rewrite deserialize_serialize.
      assert (Hdes_attc : deserialize (serialize attacker_state_t) = Some attacker_state_t).
      {
        rewrite deserialize_serialize.
        eauto.
      }
      unfold result_of_option .
      destruct (deserialize (serialize attacker_state_t)) eqn : Ht1;try congruence.
      assert(1 >? 0 + env_account_balances s attacker_addr = false).
      {
        unfold funds in Hfunds_a.
        lia.
      }
      rewrite H0.
      assert(H_at_con : (target attacker_state_t) = (target Attacker_init_cstate)).
      {
        specialize(Attacker_target_constant s Hrc_s).
        decompose_exists.
        destruct Attacker_target_constant.
        destruct H1.
        rewrite Hcs_s_attt in H1.
        inversion H1.
        subst.
        eauto.
      }
      rewrite H_at_con, H_Attacker_init_cstate, Hec_s.
      unfold contract_state in Hcs_s.
      simpl in Hcs_s.
      destruct (env_contract_states s caddr) eqn : Ht2;try congruence.
      assert(1 >? 0 + env_account_balances s attacker_addr = false).
      {
        unfold funds in Hfunds_a.
        lia.
      }
      rewrite H0.
      assert(H_at_con : (target attacker_state_t) = (target Attacker_init_cstate)).
      {
        specialize(Attacker_target_constant s Hrc_s).
        decompose_exists.
        destruct Attacker_target_constant.
        destruct H1.
        rewrite Hcs_s_attt in H1.
        inversion H1.
        subst.
        eauto.
      }
      rewrite H_at_con, H_Attacker_init_cstate, Hec_s.
      unfold contract_state in Hcs_s.
      simpl in Hcs_s.
      destruct (env_contract_states s caddr) eqn : Ht2;try congruence.
      assert(1 >? 0 + env_account_balances s attacker_addr = false).
      {
        unfold funds in Hfunds_a.
        lia.
      }
      rewrite H0.
      assert(H_at_con : (target attacker_state_t) = (target Attacker_init_cstate)).
      {
        specialize(Attacker_target_constant s Hrc_s).
        decompose_exists.
        destruct Attacker_target_constant.
        destruct H1.
        rewrite Hcs_s_attt in H1.
        inversion H1.
        subst.
        eauto.
      }
      rewrite H_at_con, H_Attacker_init_cstate, Hec_s.
      unfold contract_state in Hcs_s.
      simpl in Hcs_s.
      destruct (env_contract_states s caddr) eqn : Ht2;try congruence.
      simpl.
      rewrite Hcs_s.
      simpl.
      rewrite deserialize_serialize.
      simpl.
      cbn in *.
      unfold receive.
      simpl.
      unfold address_not_contract.
      unfold require_no_self_call.
      simpl.
      destruct_address_eq;cbn in *;try congruence.
      simpl.
      unfold require_ctx_from_eoa.
      simpl.
      cbn.
      eauto.
  Qed.

  Lemma attacker_call_Fallback_state_correct:
  forall (s s':ChainState) (cstate : State) (attacker_state : AttackerState),
    contract_state s attacker_addr = Some attacker_state ->
    contract_state s caddr = Some cstate ->
    funds s attacker_addr >= 1 ->
    readyToStepState miner contract caddr s0 s ->
    transition miner s (attacker_call_Fallback cstate) = Ok s' ->
    exists cstate' ,
      contract_state s' caddr = Some cstate' /\
      cstate' = cstate.
  Proof.
    intros * Hcs_s_a Hcs_s Hbal_a Hready Htrans.
    pose proof Hready.
    destruct H as [Htrc_s Hqueue_s].
    assert (Hact_call : is_call_act ((attacker_call_Fallback cstate)) = true).
    {
      unfold is_call_act.
      unfold user_call_Deposit.
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
    assert( H_caddr_not_EOA : address_is_contract caddr = true).
    {
      eapply contract_addr_format in Hec_s.
      eauto.
      eapply transition_reachable_impl_reachable in Htrc_s;eauto.
    }
    assert( H_attacker_caddr_not_EOA : address_is_contract attacker_addr  = true).
    {
      specialize(H_attacker_cstate s cstate Hcs_s).
      destruct H_attacker_cstate as [  Ht].
      destruct H.
      eapply contract_addr_format in H.
      eauto.
      eapply transition_reachable_impl_reachable in Htrc_s;eauto.  
    }
    assert( H_ec_s_a : env_contracts s attacker_addr = Some (attacker_contract : WeakContract)).
    {
      specialize(H_attacker_cstate s cstate Hcs_s).
      destruct H_attacker_cstate as [  Ht].
      destruct H.
      eauto.
    }
    assert(Hrc_s : reachable s).
    {
      unfold reachable_through in Hrt.
      intuition.
    }
    eapply deployed_contract_state_typed in Hec_s';eauto.
    eapply address_not_contract_negb in H_miner as H_miner_eoa.
    destruct Hec_s' as [cstate_s' Hcs_s'].
    exists cstate_s'.
    split.
    eauto.
    unfold transition in Htrans.
    unfold queue_isb_empty in Htrans.
    rewrite Hqueue_s in Htrans.
    rewrite Hact_call in Htrans.
    destruct (evaluate_action true s (get_valid_header miner s)
    [attacker_call_Fallback cstate]) eqn : H_exec;try congruence.
    unfold evaluate_action in H_exec.
    rewrite get_valid_header_is_valid_header in H_exec;eauto.
    destruct (find_origin_neq_from [attacker_call_Fallback cstate]) ; try congruence.
    destruct (find_invalid_root_action [attacker_call_Fallback cstate]);try congruence.
    set (mid_state := {|
      chain_state_env := add_new_block_to_env (get_valid_header miner s) s;
      chain_state_queue := [attacker_call_Fallback cstate]
    |}) in H_exec.
    simpl in *.
    destruct( send_or_call attacker attacker attacker_addr 0
    (Some (serialize SelfDestruct))
    (add_new_block_to_env (get_valid_header miner s) s)) eqn : H_send_or_call_RejectItem;try congruence.
    unfold send_or_call in  H_send_or_call_RejectItem.
    simpl in H_send_or_call_RejectItem.
    destruct_address_eq;simpl in *;try congruence.
    (* 
        e: attacker = miner
        n: attacker_addr <> attacker
        e0: attacker_addr = attacker_addr
        n0: attacker_addr <> miner
    *)
    eapply address_not_contract_negb in H_miner.
    destruct(0 >? miner_reward + env_account_balances s attacker)%Z;try congruence.
    rewrite H_ec_s_a in H_send_or_call_RejectItem.
    assert(Hcstate_s_a_t0:contract_state s attacker_addr = Some attacker_state) by eauto.
    unfold contract_state in Hcstate_s_a_t0.
    simpl in Hcstate_s_a_t0.
    destruct (env_contract_states s attacker_addr) eqn : Hcstate_s_a_t0';try congruence.
    destruct (weak_error_to_error_receive
    (wc_receive attacker_contract
       (s <| chain_height := S (chain_height s) |> <|
        current_slot := 
        (current_slot s + 1)%nat |> <|
        finalized_height := 
        finalized_height s |>)
       {|
         ctx_origin := attacker;
         ctx_from := attacker;
         ctx_contract_address := attacker_addr;
         ctx_contract_balance :=
           0 + env_account_balances s attacker_addr;
         ctx_amount := 0
       |} s1 (Some (serialize SelfDestruct)))) eqn : H_wc_receive_s1;try congruence.
    unfold weak_error_to_error_receive in H_wc_receive_s1.
    unfold bind_error in H_wc_receive_s1.
    destruct (wc_receive attacker_contract
    (s <| chain_height := S (chain_height s) |> <|
     current_slot := (current_slot s + 1)%nat |> <|
     finalized_height := finalized_height s |>)
    {|
      ctx_origin := attacker;
      ctx_from := attacker;
      ctx_contract_address := attacker_addr;
      ctx_contract_balance :=
        0 + env_account_balances s attacker_addr;
      ctx_amount := 0
    |} s1 (Some (serialize SelfDestruct)))
      eqn : H_wc_receive_s1';try congruence.
    
    set (cchain := s <| chain_height := S (chain_height s) |> <| current_slot :=
    (current_slot s + 1)%nat |> <| finalized_height :=
    finalized_height s |>) in H_wc_receive_s1'.
    
    set (cctx := {|
                       ctx_origin := attacker;
                       ctx_from := attacker;
                       ctx_contract_address := attacker_addr;
                       ctx_contract_balance :=
                         0 + env_account_balances s attacker_addr;
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
    rewrite deser_state in Hcstate_s_a_t0.
    simpl in receive.
    rename receive into receive_some.
    unfold attacker_receive in receive_some.
    destruct (close prev_state_strong) ;try congruence.
    unfold selfDestruct in receive_some.
    inversion receive_some.
    subst.
    inversion H_wc_receive_s1;subst.
    inversion H_send_or_call_RejectItem;subst.
    simpl in H_exec.

    rename mid_state into mid1.

    set (mid2 := {|
      chain_state_env :=
        set_contract_state attacker_addr
          (serialize resp_state_strong)
          (transfer_balance attacker attacker_addr 0
            (add_new_block_to_env
                (get_valid_header attacker s) s));
      chain_state_queue :=
        [{|
          act_origin := attacker;
          act_from := attacker_addr;
          act_body :=
            act_call (target resp_state_strong) 1
              (serialize Fallback)
        |}]
    |}).

    assert(s_mid_step : ChainStep s mid1).
    {
      eapply (step_block s mid1 (get_valid_header attacker s));eauto.
      eapply build_is_valid_next_block;eauto.
      unfold get_valid_header .
      simpl.
      lia.
      unfold get_valid_header .
      simpl.
      unfold miner_reward.
      lia.
      simpl.
      eapply Forall_forall.
      intros.
      inversion H.
      rewrite <- H0.
      unfold act_is_from_account.
      simpl.
      eauto.
      inversion H0.
      eapply Forall_forall.
      intros.
      inversion H.
      rewrite <- H0.
      unfold act_origin_is_eq_from .
      simpl.
      destruct_address_eq;try congruence;eauto.
      inversion H0.
      eapply build_env_equiv;eauto.
    }
    assert(Hrc_mid1 : reachable mid1).
    {
      eapply reachable_step.
      eauto.
      eauto.
    }
    assert(Hrc_s_mid1 : reachable_through s mid1).
    {
      eapply reachable_through_step.
      eauto.
      eauto.
    }
    assert(mid1_mid2_step : ChainStep mid1 mid2).
    {
      eapply (step_action mid1 mid2 (attacker_call_Fallback cstate) []
              [{|
              act_origin := attacker;
              act_from := attacker_addr;
              act_body :=
                act_call (target resp_state_strong) 1 (serialize Fallback)
              |}]
              );
      eauto.
      eapply (eval_call attacker attacker attacker_addr 0  
                        (attacker_contract:WeakContract)
                        (Some (serialize SelfDestruct))
                        s1
                        (serialize resp_state_strong)
                        [act_call (target resp_state_strong) 1
                         (serialize Fallback)]
              );eauto;try lia.
      eapply (account_balance_nonnegative mid1 attacker) in Hrc_mid1.
      lia.
      eapply build_env_equiv;eauto.
    }
    assert(Hrc_mid1_mid2 : reachable_through mid1 mid2).
    {
      eapply reachable_through_step.
      eauto.
      eauto.
    }
    assert(Hrc_s_mid2 : reachable_through s mid2).
    {
      eapply reachable_through_trans in Hrc_s_mid1.
      eauto.
      eauto.
    }

    destruct(send_or_call attacker attacker_addr (target resp_state_strong) 1
    (Some (serialize Fallback))
    (set_contract_state attacker_addr (serialize resp_state_strong)
       (transfer_balance attacker attacker_addr 0
          (add_new_block_to_env (get_valid_header attacker s) s)))) eqn : H_send_or_call_2;try congruence.

    unfold send_or_call in  H_send_or_call_2.
    simpl in H_send_or_call_2.
    destruct_address_eq;simpl in *;try congruence.
    assert(target resp_state_strong <> attacker_addr).
    {
      specialize (Attacker_target_constant s Hrc_s).
      destruct Attacker_target_constant.
      destruct H.
      rewrite H in *.
      inversion Hcs_s_a.
      intuition.
    }
    congruence.
    assert((target resp_state_strong) = target Attacker_init_cstate).
    {
      specialize (Attacker_target_constant s Hrc_s).
      destruct Attacker_target_constant.
      destruct H.
      rewrite H in *.
      inversion Hcs_s_a.
      intuition.
    }
    intuition.
      (** 
        n1: attacker_addr <> attacker
        e: attacker_addr = attacker_addr
        n2: target resp_state_strong <> attacker_addr
        e1: target resp_state_strong = target resp_state_strong
        n3: target resp_state_strong <> attacker
      **)
    assert(H_eq_tar : (target resp_state_strong) = target Attacker_init_cstate).
    {
      specialize (Attacker_target_constant s Hrc_s).
      destruct Attacker_target_constant.
      destruct H.
      rewrite H in *.
      inversion Hcs_s_a.
      intuition.
    }
    destruct(1 >? 0 + env_account_balances s attacker_addr)%Z;try congruence.
    rewrite H_eq_tar in *.
    rewrite Hec_s in H_send_or_call_2.
    pose proof Hcs_s as Hcs_s_t.
    unfold contract_state in Hcs_s_t.
    simpl in Hcs_s_t.
    destruct (env_contract_states s (target Attacker_init_cstate)) eqn : Hcs_s_t_eqn;try congruence.
    destruct (weak_error_to_error_receive
    (wc_receive contract
       (s <| chain_height := S (chain_height s) |> <|
        current_slot := (current_slot s + 1)%nat |> <|
        finalized_height := finalized_height s |>)
       {|
         ctx_origin := attacker;
         ctx_from := attacker_addr;
         ctx_contract_address := target Attacker_init_cstate;
         ctx_contract_balance :=
           1 +
           env_account_balances s
             (target Attacker_init_cstate);
         ctx_amount := 1
       |} s2 (Some (serialize Fallback)))) eqn : H_wc_receive_s2;try congruence.
    unfold weak_error_to_error_receive in H_wc_receive_s2.
    unfold bind_error in H_wc_receive_s2.
    destruct (wc_receive contract
    (s <| chain_height := S (chain_height s) |> <|
     current_slot := (current_slot s + 1)%nat |> <|
     finalized_height := finalized_height s |>)
    {|
      ctx_origin := attacker;
      ctx_from := attacker_addr;
      ctx_contract_address := target Attacker_init_cstate;
      ctx_contract_balance :=
        1 +
        env_account_balances s (target Attacker_init_cstate);
      ctx_amount := 1
    |} s2 (Some (serialize Fallback)))
      eqn : H_wc_receive_s2';try congruence.
    
    set (cchain' := 
                    s <| chain_height := S (chain_height s) |> <| current_slot
                    := (current_slot s + 1)%nat |> <| finalized_height :=
                    finalized_height s |>
        ) in H_wc_receive_s2'.
    
    set (cctx' := {|
                       ctx_origin := attacker;
                       ctx_from := attacker_addr;
                       ctx_contract_address := target Attacker_init_cstate;
                       ctx_contract_balance :=
                         1 +
                         env_account_balances s (target Attacker_init_cstate);
                       ctx_amount := 1
                     |}) in H_wc_receive_s2'.
    
    destruct t2 as [new_state' new_acts'].

    destruct (wc_receive_strong ltac:(try eassumption))
    as (prev_state_strong1 & msg_strong1 & resp_state_strong1 &
      deser_state1 & deser_msg1 & <- & receive).

    simpl in deser_msg1.
    destruct (msg_strong1) eqn : H_msg1;try congruence.
    rewrite deserialize_serialize in deser_msg1.
    rewrite <- deser_msg1 in receive.
    rewrite deser_state1 in Hcs_s_t.
    simpl in receive.
    rename receive into receive_some1.
    reduce_receive.
    reduce_ether_receive.
    inversion receive_some1.
    subst.
    inversion H_wc_receive_s2;subst.
    inversion H_send_or_call_2;subst.
    simpl in H_exec.

    set (mid3 := {|
             chain_state_env :=
               set_contract_state (target Attacker_init_cstate)
                 (serialize resp_state_strong1)
                 (transfer_balance attacker_addr (target Attacker_init_cstate) 1
                    (set_contract_state attacker_addr
                       (serialize resp_state_strong)
                       (transfer_balance attacker attacker_addr 0
                          (add_new_block_to_env (get_valid_header attacker s) s))));
             chain_state_queue := []
           |}).
    inversion H_exec.
    subst.
    inversion Htrans.
    subst.
    inversion Hcs_s'.
    unfold contract_state in H0.
    simpl in H0.
    destruct_address_eq;eauto;try congruence.
    setoid_rewrite deserialize_serialize in H0.
    inversion H0.
    intuition.
    (* 
      n: attacker <> miner
      e: attacker_addr = attacker
      e0: attacker_addr = attacker_addr
      n0: attacker_addr <> miner
    *)
    assert(address_is_contract attacker = false).
    {
      eapply address_not_contract_negb;eauto.
    }
    intuition.
    (* 
      n: attacker <> miner
      n0: attacker_addr <> attacker
      e: attacker_addr = attacker_addr
      n1: attacker_addr <> miner
    *)
    assert(H_attacker_eoa:address_is_contract attacker = false).
    {
      eapply address_not_contract_negb;eauto.
    }
    eapply address_not_contract_negb in H_miner.
    destruct(0 >? env_account_balances s attacker)%Z;try congruence.
    rewrite H_ec_s_a in H_send_or_call_RejectItem.
    assert(Hcstate_s_a_t0:contract_state s attacker_addr = Some attacker_state) by eauto.
    unfold contract_state in Hcstate_s_a_t0.
    simpl in Hcstate_s_a_t0.
    destruct (env_contract_states s attacker_addr) eqn : Hcstate_s_a_t0';try congruence.
    destruct (weak_error_to_error_receive
    (wc_receive attacker_contract
       (s <| chain_height := S (chain_height s) |> <|
        current_slot := 
        (current_slot s + 1)%nat |> <|
        finalized_height := 
        finalized_height s |>)
       {|
         ctx_origin := attacker;
         ctx_from := attacker;
         ctx_contract_address := attacker_addr;
         ctx_contract_balance :=
           0 + env_account_balances s attacker_addr;
         ctx_amount := 0
       |} s1 (Some (serialize SelfDestruct)))) eqn : H_wc_receive_s1;try congruence.
    unfold weak_error_to_error_receive in H_wc_receive_s1.
    unfold bind_error in H_wc_receive_s1.
    destruct (wc_receive attacker_contract
    (s <| chain_height := S (chain_height s) |> <|
     current_slot := (current_slot s + 1)%nat |> <|
     finalized_height := finalized_height s |>)
    {|
      ctx_origin := attacker;
      ctx_from := attacker;
      ctx_contract_address := attacker_addr;
      ctx_contract_balance :=
        0 + env_account_balances s attacker_addr;
      ctx_amount := 0
    |} s1 (Some (serialize SelfDestruct)))
      eqn : H_wc_receive_s1';try congruence.
    
    set (cchain := s <| chain_height := S (chain_height s) |> <| current_slot :=
    (current_slot s + 1)%nat |> <| finalized_height :=
    finalized_height s |>) in H_wc_receive_s1'.
    
    set (cctx := {|
                       ctx_origin := attacker;
                       ctx_from := attacker;
                       ctx_contract_address := attacker_addr;
                       ctx_contract_balance :=
                         0 + env_account_balances s attacker_addr;
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
    rewrite deser_state in Hcstate_s_a_t0.
    simpl in receive.
    rename receive into receive_some.
    unfold attacker_receive in receive_some.
    destruct (close prev_state_strong) ;try congruence.
    unfold selfDestruct in receive_some.
    inversion receive_some.
    subst.
    inversion H_wc_receive_s1;subst.
    inversion H_send_or_call_RejectItem;subst.
    simpl in H_exec.

    rename mid_state into mid1.

    set (mid2 := {|
      chain_state_env :=
        set_contract_state attacker_addr
          (serialize resp_state_strong)
          (transfer_balance attacker attacker_addr 0
            (add_new_block_to_env
                (get_valid_header miner  s) s));
      chain_state_queue :=
        [{|
          act_origin := attacker;
          act_from := attacker_addr;
          act_body :=
            act_call (target resp_state_strong) 1
              (serialize Fallback)
        |}]
    |}).

    assert(s_mid_step : ChainStep s mid1).
    {
      eapply (step_block s mid1 (get_valid_header miner  s));eauto.
      eapply build_is_valid_next_block;eauto.
      unfold get_valid_header .
      simpl.
      lia.
      unfold get_valid_header .
      simpl.
      unfold miner_reward.
      lia.
      simpl.
      eapply Forall_forall.
      intros.
      inversion H.
      rewrite <- H0.
      unfold act_is_from_account.
      simpl.
      eauto.
      inversion H0.
      eapply Forall_forall.
      intros.
      inversion H.
      rewrite <- H0.
      unfold act_origin_is_eq_from .
      simpl.
      destruct_address_eq;try congruence;eauto.
      inversion H0.
      eapply build_env_equiv;eauto.
    }
    assert(Hrc_mid1 : reachable mid1).
    {
      eapply reachable_step.
      eauto.
      eauto.
    }
    assert(Hrc_s_mid1 : reachable_through s mid1).
    {
      eapply reachable_through_step.
      eauto.
      eauto.
    }
    assert(mid1_mid2_step : ChainStep mid1 mid2).
    {
      eapply (step_action mid1 mid2 (attacker_call_Fallback cstate) []
              [{|
              act_origin := attacker;
              act_from := attacker_addr;
              act_body :=
                act_call (target resp_state_strong) 1 (serialize Fallback)
              |}]
              );
      eauto.
      eapply (eval_call attacker attacker attacker_addr 0  
                        (attacker_contract:WeakContract)
                        (Some (serialize SelfDestruct))
                        s1
                        (serialize resp_state_strong)
                        [act_call (target resp_state_strong) 1
                         (serialize Fallback)]
              );eauto;try lia.
      eapply (account_balance_nonnegative mid1 attacker) in Hrc_mid1.
      lia.
      eapply build_env_equiv;eauto.
    }
    assert(Hrc_mid1_mid2 : reachable_through mid1 mid2).
    {
      eapply reachable_through_step.
      eauto.
      eauto.
    }
    assert(Hrc_s_mid2 : reachable_through s mid2).
    {
      eapply reachable_through_trans in Hrc_s_mid1.
      eauto.
      eauto.
    }

    destruct(send_or_call attacker attacker_addr (target resp_state_strong) 1
    (Some (serialize Fallback))
    (set_contract_state attacker_addr (serialize resp_state_strong)
       (transfer_balance attacker attacker_addr 0
          (add_new_block_to_env (get_valid_header miner s) s)))) eqn : H_send_or_call_2;try congruence.

    unfold send_or_call in  H_send_or_call_2.
    simpl in H_send_or_call_2.
    destruct_address_eq;simpl in *;try congruence.
    assert(target resp_state_strong <> attacker_addr).
    {
      specialize (Attacker_target_constant s Hrc_s).
      destruct Attacker_target_constant.
      destruct H.
      rewrite H in *.
      inversion Hcs_s_a.
      intuition.
    }
    congruence.
    assert((target resp_state_strong) = target Attacker_init_cstate).
    {
      specialize (Attacker_target_constant s Hrc_s).
      destruct Attacker_target_constant.
      destruct H.
      rewrite H in *.
      inversion Hcs_s_a.
      intuition.
    }
    intuition.
      (** 
        n1: attacker_addr <> attacker
        e: attacker_addr = attacker_addr
        n2: target resp_state_strong <> attacker_addr
        e1: target resp_state_strong = target resp_state_strong
        n3: target resp_state_strong <> attacker
      **)
    assert(H_eq_tar : (target resp_state_strong) = target Attacker_init_cstate).
    {
      specialize (Attacker_target_constant s Hrc_s).
      destruct Attacker_target_constant.
      destruct H.
      rewrite H in *.
      inversion Hcs_s_a.
      intuition.
    }

    destruct(1 >? 0 + env_account_balances s attacker_addr)%Z eqn : Httt;try congruence.
    destruct(1 >? 0 + env_account_balances s attacker_addr)%Z eqn : Httt;try congruence.
    assert(H_eq_tar : (target resp_state_strong) = target Attacker_init_cstate).
    {
      specialize (Attacker_target_constant s Hrc_s).
      destruct Attacker_target_constant.
      destruct H.
      rewrite H in *.
      inversion Hcs_s_a.
      intuition.
    }
    rewrite H_eq_tar in *.
    rewrite Hec_s in H_send_or_call_2.
    pose proof Hcs_s as Hcs_s_t.
    unfold contract_state in Hcs_s_t.
    simpl in Hcs_s_t.
    destruct (env_contract_states s (target Attacker_init_cstate)) eqn : Hcs_s_t_eqn;try congruence.
    destruct (weak_error_to_error_receive
    (wc_receive contract
       (s <| chain_height := S (chain_height s) |> <|
        current_slot := (current_slot s + 1)%nat |> <|
        finalized_height := finalized_height s |>)
       {|
         ctx_origin := attacker;
         ctx_from := attacker_addr;
         ctx_contract_address := target Attacker_init_cstate;
         ctx_contract_balance :=
           1 +
           env_account_balances s
             (target Attacker_init_cstate);
         ctx_amount := 1
       |} s2 (Some (serialize Fallback)))) eqn : H_wc_receive_s2;try congruence.
    unfold weak_error_to_error_receive in H_wc_receive_s2.
    unfold bind_error in H_wc_receive_s2.
    destruct (wc_receive contract
    (s <| chain_height := S (chain_height s) |> <|
     current_slot := (current_slot s + 1)%nat |> <|
     finalized_height := finalized_height s |>)
    {|
      ctx_origin := attacker;
      ctx_from := attacker_addr;
      ctx_contract_address := target Attacker_init_cstate;
      ctx_contract_balance :=
        1 +
        env_account_balances s (target Attacker_init_cstate);
      ctx_amount := 1
    |} s2 (Some (serialize Fallback)))
      eqn : H_wc_receive_s2';try congruence.
    
    set (cchain' := 
                    s <| chain_height := S (chain_height s) |> <| current_slot
                    := (current_slot s + 1)%nat |> <| finalized_height :=
                    finalized_height s |>
        ) in H_wc_receive_s2'.
    
    set (cctx' := {|
                       ctx_origin := attacker;
                       ctx_from := attacker_addr;
                       ctx_contract_address := target Attacker_init_cstate;
                       ctx_contract_balance :=
                         1 +
                         env_account_balances s (target Attacker_init_cstate);
                       ctx_amount := 1
                     |}) in H_wc_receive_s2'.
    
    destruct t2 as [new_state' new_acts'].

    destruct (wc_receive_strong ltac:(try eassumption))
    as (prev_state_strong1 & msg_strong1 & resp_state_strong1 &
      deser_state1 & deser_msg1 & <- & receive).

    simpl in deser_msg1.
    destruct (msg_strong1) eqn : H_msg1;try congruence.
    rewrite deserialize_serialize in deser_msg1.
    rewrite <- deser_msg1 in receive.
    rewrite deser_state1 in Hcs_s_t.
    simpl in receive.
    rename receive into receive_some1.
    reduce_receive.
    reduce_ether_receive.
    inversion receive_some1.
    subst.
    inversion H_wc_receive_s2;subst.
    inversion H_send_or_call_2;subst.
    simpl in H_exec.

    set (mid3 := {|
             chain_state_env :=
               set_contract_state (target Attacker_init_cstate)
                 (serialize resp_state_strong1)
                 (transfer_balance attacker_addr (target Attacker_init_cstate) 1
                    (set_contract_state attacker_addr
                       (serialize resp_state_strong)
                       (transfer_balance attacker attacker_addr 0
                          (add_new_block_to_env (get_valid_header miner s) s))));
             chain_state_queue := []
           |}).
    inversion H_exec.
    subst.
    inversion Htrans.
    subst.
    inversion Hcs_s'.
    unfold contract_state in H0.
    simpl in H0.
    destruct_address_eq;eauto;try congruence.
    setoid_rewrite deserialize_serialize in H0.
    inversion H0.
    intuition.
  Qed.

  Lemma attacker_call_Fallback_fund_correct:
    forall (s s':ChainState) (cstate : State) (attacker_state : AttackerState),
      contract_state s attacker_addr = Some attacker_state ->
      contract_state s caddr = Some cstate ->
      funds s attacker_addr >= 1 ->
      readyToStepState miner contract caddr s0 s ->
      transition miner s (attacker_call_Fallback cstate) = Ok s' ->
      funds s' caddr = (funds s caddr + 1).
  Proof.
    intros * Hcs_s_a Hcs_s Hbal_a Hready Htrans.
    pose proof Hready.
    destruct H as [Htrc_s Hqueue_s].
    assert (Hact_call : is_call_act ((attacker_call_Fallback cstate)) = true).
    {
      unfold is_call_act.
      unfold user_call_Deposit.
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
    assert( H_caddr_not_EOA : address_is_contract caddr = true).
    {
      eapply contract_addr_format in Hec_s.
      eauto.
      eapply transition_reachable_impl_reachable in Htrc_s;eauto.
    }
    assert( H_attacker_caddr_not_EOA : address_is_contract attacker_addr  = true).
    {
      specialize(H_attacker_cstate s cstate Hcs_s).
      destruct H_attacker_cstate as [  Ht].
      destruct H.
      eapply contract_addr_format in H.
      eauto.
      eapply transition_reachable_impl_reachable in Htrc_s;eauto.  
    }
    assert( H_ec_s_a : env_contracts s attacker_addr = Some (attacker_contract : WeakContract)).
    {
      specialize(H_attacker_cstate s cstate Hcs_s).
      destruct H_attacker_cstate as [  Ht].
      destruct H.
      eauto.
    }
    assert(Hrc_s : reachable s).
    {
      unfold reachable_through in Hrt.
      intuition.
    }
    eapply deployed_contract_state_typed in Hec_s';eauto.
    eapply address_not_contract_negb in H_miner as H_miner_eoa.
    destruct Hec_s' as [cstate_s' Hcs_s'].
    unfold transition in Htrans.
    unfold queue_isb_empty in Htrans.
    rewrite Hqueue_s in Htrans.
    rewrite Hact_call in Htrans.
    destruct (evaluate_action true s (get_valid_header miner s)
    [attacker_call_Fallback cstate]) eqn : H_exec;try congruence.
    unfold evaluate_action in H_exec.
    rewrite get_valid_header_is_valid_header in H_exec;eauto.
    destruct (find_origin_neq_from [attacker_call_Fallback cstate]) ; try congruence.
    destruct (find_invalid_root_action [attacker_call_Fallback cstate]);try congruence.
    set (mid_state := {|
      chain_state_env := add_new_block_to_env (get_valid_header miner s) s;
      chain_state_queue := [attacker_call_Fallback cstate]
    |}) in H_exec.
    simpl in *.
    destruct( send_or_call attacker attacker attacker_addr 0
    (Some (serialize SelfDestruct))
    (add_new_block_to_env (get_valid_header miner s) s)) eqn : H_send_or_call_RejectItem;try congruence.
    unfold send_or_call in  H_send_or_call_RejectItem.
    simpl in H_send_or_call_RejectItem.
    destruct_address_eq;simpl in *;try congruence.
    (* 
        e: attacker = miner
        n: attacker_addr <> attacker
        e0: attacker_addr = attacker_addr
        n0: attacker_addr <> miner
    *)
    eapply address_not_contract_negb in H_miner.
    destruct(0 >? miner_reward + env_account_balances s attacker)%Z;try congruence.
    rewrite H_ec_s_a in H_send_or_call_RejectItem.
    assert(Hcstate_s_a_t0:contract_state s attacker_addr = Some attacker_state) by eauto.
    unfold contract_state in Hcstate_s_a_t0.
    simpl in Hcstate_s_a_t0.
    destruct (env_contract_states s attacker_addr) eqn : Hcstate_s_a_t0';try congruence.
    destruct (weak_error_to_error_receive
    (wc_receive attacker_contract
       (s <| chain_height := S (chain_height s) |> <|
        current_slot := 
        (current_slot s + 1)%nat |> <|
        finalized_height := 
        finalized_height s |>)
       {|
         ctx_origin := attacker;
         ctx_from := attacker;
         ctx_contract_address := attacker_addr;
         ctx_contract_balance :=
           0 + env_account_balances s attacker_addr;
         ctx_amount := 0
       |} s1 (Some (serialize SelfDestruct)))) eqn : H_wc_receive_s1;try congruence.
    unfold weak_error_to_error_receive in H_wc_receive_s1.
    unfold bind_error in H_wc_receive_s1.
    destruct (wc_receive attacker_contract
    (s <| chain_height := S (chain_height s) |> <|
     current_slot := (current_slot s + 1)%nat |> <|
     finalized_height := finalized_height s |>)
    {|
      ctx_origin := attacker;
      ctx_from := attacker;
      ctx_contract_address := attacker_addr;
      ctx_contract_balance :=
        0 + env_account_balances s attacker_addr;
      ctx_amount := 0
    |} s1 (Some (serialize SelfDestruct)))
      eqn : H_wc_receive_s1';try congruence.
    
    set (cchain := s <| chain_height := S (chain_height s) |> <| current_slot :=
    (current_slot s + 1)%nat |> <| finalized_height :=
    finalized_height s |>) in H_wc_receive_s1'.
    
    set (cctx := {|
                       ctx_origin := attacker;
                       ctx_from := attacker;
                       ctx_contract_address := attacker_addr;
                       ctx_contract_balance :=
                         0 + env_account_balances s attacker_addr;
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
    rewrite deser_state in Hcstate_s_a_t0.
    simpl in receive.
    rename receive into receive_some.
    unfold attacker_receive in receive_some.
    destruct (close prev_state_strong) ;try congruence.
    unfold selfDestruct in receive_some.
    inversion receive_some.
    subst.
    inversion H_wc_receive_s1;subst.
    inversion H_send_or_call_RejectItem;subst.
    simpl in H_exec.

    rename mid_state into mid1.

    set (mid2 := {|
      chain_state_env :=
        set_contract_state attacker_addr
          (serialize resp_state_strong)
          (transfer_balance attacker attacker_addr 0
            (add_new_block_to_env
                (get_valid_header attacker s) s));
      chain_state_queue :=
        [{|
          act_origin := attacker;
          act_from := attacker_addr;
          act_body :=
            act_call (target resp_state_strong) 1
              (serialize Fallback)
        |}]
    |}).

    assert(s_mid_step : ChainStep s mid1).
    {
      eapply (step_block s mid1 (get_valid_header attacker s));eauto.
      eapply build_is_valid_next_block;eauto.
      unfold get_valid_header .
      simpl.
      lia.
      unfold get_valid_header .
      simpl.
      unfold miner_reward.
      lia.
      simpl.
      eapply Forall_forall.
      intros.
      inversion H.
      rewrite <- H0.
      unfold act_is_from_account.
      simpl.
      eauto.
      inversion H0.
      eapply Forall_forall.
      intros.
      inversion H.
      rewrite <- H0.
      unfold act_origin_is_eq_from .
      simpl.
      destruct_address_eq;try congruence;eauto.
      inversion H0.
      eapply build_env_equiv;eauto.
    }
    assert(Hrc_mid1 : reachable mid1).
    {
      eapply reachable_step.
      eauto.
      eauto.
    }
    assert(Hrc_s_mid1 : reachable_through s mid1).
    {
      eapply reachable_through_step.
      eauto.
      eauto.
    }
    assert(mid1_mid2_step : ChainStep mid1 mid2).
    {
      eapply (step_action mid1 mid2 (attacker_call_Fallback cstate) []
              [{|
              act_origin := attacker;
              act_from := attacker_addr;
              act_body :=
                act_call (target resp_state_strong) 1 (serialize Fallback)
              |}]
              );
      eauto.
      eapply (eval_call attacker attacker attacker_addr 0  
                        (attacker_contract:WeakContract)
                        (Some (serialize SelfDestruct))
                        s1
                        (serialize resp_state_strong)
                        [act_call (target resp_state_strong) 1
                         (serialize Fallback)]
              );eauto;try lia.
      eapply (account_balance_nonnegative mid1 attacker) in Hrc_mid1.
      lia.
      eapply build_env_equiv;eauto.
    }
    assert(Hrc_mid1_mid2 : reachable_through mid1 mid2).
    {
      eapply reachable_through_step.
      eauto.
      eauto.
    }
    assert(Hrc_s_mid2 : reachable_through s mid2).
    {
      eapply reachable_through_trans in Hrc_s_mid1.
      eauto.
      eauto.
    }

    destruct(send_or_call attacker attacker_addr (target resp_state_strong) 1
    (Some (serialize Fallback))
    (set_contract_state attacker_addr (serialize resp_state_strong)
       (transfer_balance attacker attacker_addr 0
          (add_new_block_to_env (get_valid_header attacker s) s)))) eqn : H_send_or_call_2;try congruence.

    unfold send_or_call in  H_send_or_call_2.
    simpl in H_send_or_call_2.
    destruct_address_eq;simpl in *;try congruence.
    assert(target resp_state_strong <> attacker_addr).
    {
      specialize (Attacker_target_constant s Hrc_s).
      destruct Attacker_target_constant.
      destruct H.
      rewrite H in *.
      inversion Hcs_s_a.
      intuition.
    }
    congruence.
    assert((target resp_state_strong) = target Attacker_init_cstate).
    {
      specialize (Attacker_target_constant s Hrc_s).
      destruct Attacker_target_constant.
      destruct H.
      rewrite H in *.
      inversion Hcs_s_a.
      intuition.
    }
    intuition.
      (** 
        n1: attacker_addr <> attacker
        e: attacker_addr = attacker_addr
        n2: target resp_state_strong <> attacker_addr
        e1: target resp_state_strong = target resp_state_strong
        n3: target resp_state_strong <> attacker
      **)
    assert(H_eq_tar : (target resp_state_strong) = target Attacker_init_cstate).
    {
      specialize (Attacker_target_constant s Hrc_s).
      destruct Attacker_target_constant.
      destruct H.
      rewrite H in *.
      inversion Hcs_s_a.
      intuition.
    }
    destruct(1 >? 0 + env_account_balances s attacker_addr)%Z;try congruence.
    rewrite H_eq_tar in *.
    rewrite Hec_s in H_send_or_call_2.
    pose proof Hcs_s as Hcs_s_t.
    unfold contract_state in Hcs_s_t.
    simpl in Hcs_s_t.
    destruct (env_contract_states s (target Attacker_init_cstate)) eqn : Hcs_s_t_eqn;try congruence.
    destruct (weak_error_to_error_receive
    (wc_receive contract
       (s <| chain_height := S (chain_height s) |> <|
        current_slot := (current_slot s + 1)%nat |> <|
        finalized_height := finalized_height s |>)
       {|
         ctx_origin := attacker;
         ctx_from := attacker_addr;
         ctx_contract_address := target Attacker_init_cstate;
         ctx_contract_balance :=
           1 +
           env_account_balances s
             (target Attacker_init_cstate);
         ctx_amount := 1
       |} s2 (Some (serialize Fallback)))) eqn : H_wc_receive_s2;try congruence.
    unfold weak_error_to_error_receive in H_wc_receive_s2.
    unfold bind_error in H_wc_receive_s2.
    destruct (wc_receive contract
    (s <| chain_height := S (chain_height s) |> <|
     current_slot := (current_slot s + 1)%nat |> <|
     finalized_height := finalized_height s |>)
    {|
      ctx_origin := attacker;
      ctx_from := attacker_addr;
      ctx_contract_address := target Attacker_init_cstate;
      ctx_contract_balance :=
        1 +
        env_account_balances s (target Attacker_init_cstate);
      ctx_amount := 1
    |} s2 (Some (serialize Fallback)))
      eqn : H_wc_receive_s2';try congruence.
    
    set (cchain' := 
                    s <| chain_height := S (chain_height s) |> <| current_slot
                    := (current_slot s + 1)%nat |> <| finalized_height :=
                    finalized_height s |>
        ) in H_wc_receive_s2'.
    
    set (cctx' := {|
                       ctx_origin := attacker;
                       ctx_from := attacker_addr;
                       ctx_contract_address := target Attacker_init_cstate;
                       ctx_contract_balance :=
                         1 +
                         env_account_balances s (target Attacker_init_cstate);
                       ctx_amount := 1
                     |}) in H_wc_receive_s2'.
    
    destruct t2 as [new_state' new_acts'].

    destruct (wc_receive_strong ltac:(try eassumption))
    as (prev_state_strong1 & msg_strong1 & resp_state_strong1 &
      deser_state1 & deser_msg1 & <- & receive).

    simpl in deser_msg1.
    destruct (msg_strong1) eqn : H_msg1;try congruence.
    rewrite deserialize_serialize in deser_msg1.
    rewrite <- deser_msg1 in receive.
    rewrite deser_state1 in Hcs_s_t.
    simpl in receive.
    rename receive into receive_some1.
    reduce_receive.
    reduce_ether_receive.
    inversion receive_some1.
    subst.
    inversion H_wc_receive_s2;subst.
    inversion H_send_or_call_2;subst.
    simpl in H_exec.

    set (mid3 := {|
             chain_state_env :=
               set_contract_state (target Attacker_init_cstate)
                 (serialize resp_state_strong1)
                 (transfer_balance attacker_addr (target Attacker_init_cstate) 1
                    (set_contract_state attacker_addr
                       (serialize resp_state_strong)
                       (transfer_balance attacker attacker_addr 0
                          (add_new_block_to_env (get_valid_header attacker s) s))));
             chain_state_queue := []
           |}).
    inversion H_exec.
    subst.
    inversion Htrans.
    subst.
    inversion Hcs_s'.
    unfold contract_state in H0.
    simpl in H0.
    destruct_address_eq;eauto;try congruence.
    setoid_rewrite deserialize_serialize in H0.
    inversion H0.
    unfold funds.
    simpl.
    destruct_address_eq;eauto;try congruence.
    lia.
    (* 
      n: attacker <> miner
      e: attacker_addr = attacker
      e0: attacker_addr = attacker_addr
      n0: attacker_addr <> miner
    *)
    assert(address_is_contract attacker = false).
    {
      eapply address_not_contract_negb;eauto.
    }
    intuition.
    (* 
      n: attacker <> miner
      n0: attacker_addr <> attacker
      e: attacker_addr = attacker_addr
      n1: attacker_addr <> miner
    *)
    assert(H_attacker_eoa:address_is_contract attacker = false).
    {
      eapply address_not_contract_negb;eauto.
    }
    eapply address_not_contract_negb in H_miner.
    destruct(0 >? env_account_balances s attacker)%Z;try congruence.
    rewrite H_ec_s_a in H_send_or_call_RejectItem.
    assert(Hcstate_s_a_t0:contract_state s attacker_addr = Some attacker_state) by eauto.
    unfold contract_state in Hcstate_s_a_t0.
    simpl in Hcstate_s_a_t0.
    destruct (env_contract_states s attacker_addr) eqn : Hcstate_s_a_t0';try congruence.
    destruct (weak_error_to_error_receive
    (wc_receive attacker_contract
       (s <| chain_height := S (chain_height s) |> <|
        current_slot := 
        (current_slot s + 1)%nat |> <|
        finalized_height := 
        finalized_height s |>)
       {|
         ctx_origin := attacker;
         ctx_from := attacker;
         ctx_contract_address := attacker_addr;
         ctx_contract_balance :=
           0 + env_account_balances s attacker_addr;
         ctx_amount := 0
       |} s1 (Some (serialize SelfDestruct)))) eqn : H_wc_receive_s1;try congruence.
    unfold weak_error_to_error_receive in H_wc_receive_s1.
    unfold bind_error in H_wc_receive_s1.
    destruct (wc_receive attacker_contract
    (s <| chain_height := S (chain_height s) |> <|
     current_slot := (current_slot s + 1)%nat |> <|
     finalized_height := finalized_height s |>)
    {|
      ctx_origin := attacker;
      ctx_from := attacker;
      ctx_contract_address := attacker_addr;
      ctx_contract_balance :=
        0 + env_account_balances s attacker_addr;
      ctx_amount := 0
    |} s1 (Some (serialize SelfDestruct)))
      eqn : H_wc_receive_s1';try congruence.
    
    set (cchain := s <| chain_height := S (chain_height s) |> <| current_slot :=
    (current_slot s + 1)%nat |> <| finalized_height :=
    finalized_height s |>) in H_wc_receive_s1'.
    
    set (cctx := {|
                       ctx_origin := attacker;
                       ctx_from := attacker;
                       ctx_contract_address := attacker_addr;
                       ctx_contract_balance :=
                         0 + env_account_balances s attacker_addr;
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
    rewrite deser_state in Hcstate_s_a_t0.
    simpl in receive.
    rename receive into receive_some.
    unfold attacker_receive in receive_some.
    destruct (close prev_state_strong) ;try congruence.
    unfold selfDestruct in receive_some.
    inversion receive_some.
    subst.
    inversion H_wc_receive_s1;subst.
    inversion H_send_or_call_RejectItem;subst.
    simpl in H_exec.

    rename mid_state into mid1.

    set (mid2 := {|
      chain_state_env :=
        set_contract_state attacker_addr
          (serialize resp_state_strong)
          (transfer_balance attacker attacker_addr 0
            (add_new_block_to_env
                (get_valid_header miner  s) s));
      chain_state_queue :=
        [{|
          act_origin := attacker;
          act_from := attacker_addr;
          act_body :=
            act_call (target resp_state_strong) 1
              (serialize Fallback)
        |}]
    |}).

    assert(s_mid_step : ChainStep s mid1).
    {
      eapply (step_block s mid1 (get_valid_header miner  s));eauto.
      eapply build_is_valid_next_block;eauto.
      unfold get_valid_header .
      simpl.
      lia.
      unfold get_valid_header .
      simpl.
      unfold miner_reward.
      lia.
      simpl.
      eapply Forall_forall.
      intros.
      inversion H.
      rewrite <- H0.
      unfold act_is_from_account.
      simpl.
      eauto.
      inversion H0.
      eapply Forall_forall.
      intros.
      inversion H.
      rewrite <- H0.
      unfold act_origin_is_eq_from .
      simpl.
      destruct_address_eq;try congruence;eauto.
      inversion H0.
      eapply build_env_equiv;eauto.
    }
    assert(Hrc_mid1 : reachable mid1).
    {
      eapply reachable_step.
      eauto.
      eauto.
    }
    assert(Hrc_s_mid1 : reachable_through s mid1).
    {
      eapply reachable_through_step.
      eauto.
      eauto.
    }
    assert(mid1_mid2_step : ChainStep mid1 mid2).
    {
      eapply (step_action mid1 mid2 (attacker_call_Fallback cstate) []
              [{|
              act_origin := attacker;
              act_from := attacker_addr;
              act_body :=
                act_call (target resp_state_strong) 1 (serialize Fallback)
              |}]
              );
      eauto.
      eapply (eval_call attacker attacker attacker_addr 0  
                        (attacker_contract:WeakContract)
                        (Some (serialize SelfDestruct))
                        s1
                        (serialize resp_state_strong)
                        [act_call (target resp_state_strong) 1
                         (serialize Fallback)]
              );eauto;try lia.
      eapply (account_balance_nonnegative mid1 attacker) in Hrc_mid1.
      lia.
      eapply build_env_equiv;eauto.
    }
    assert(Hrc_mid1_mid2 : reachable_through mid1 mid2).
    {
      eapply reachable_through_step.
      eauto.
      eauto.
    }
    assert(Hrc_s_mid2 : reachable_through s mid2).
    {
      eapply reachable_through_trans in Hrc_s_mid1.
      eauto.
      eauto.
    }

    destruct(send_or_call attacker attacker_addr (target resp_state_strong) 1
    (Some (serialize Fallback))
    (set_contract_state attacker_addr (serialize resp_state_strong)
       (transfer_balance attacker attacker_addr 0
          (add_new_block_to_env (get_valid_header miner s) s)))) eqn : H_send_or_call_2;try congruence.

    unfold send_or_call in  H_send_or_call_2.
    simpl in H_send_or_call_2.
    destruct_address_eq;simpl in *;try congruence.
    assert(target resp_state_strong <> attacker_addr).
    {
      specialize (Attacker_target_constant s Hrc_s).
      destruct Attacker_target_constant.
      destruct H.
      rewrite H in *.
      inversion Hcs_s_a.
      intuition.
    }
    congruence.
    assert((target resp_state_strong) = target Attacker_init_cstate).
    {
      specialize (Attacker_target_constant s Hrc_s).
      destruct Attacker_target_constant.
      destruct H.
      rewrite H in *.
      inversion Hcs_s_a.
      intuition.
    }
    intuition.
      (** 
        n1: attacker_addr <> attacker
        e: attacker_addr = attacker_addr
        n2: target resp_state_strong <> attacker_addr
        e1: target resp_state_strong = target resp_state_strong
        n3: target resp_state_strong <> attacker
      **)
    assert(H_eq_tar : (target resp_state_strong) = target Attacker_init_cstate).
    {
      specialize (Attacker_target_constant s Hrc_s).
      destruct Attacker_target_constant.
      destruct H.
      rewrite H in *.
      inversion Hcs_s_a.
      intuition.
    }

    destruct(1 >? 0 + env_account_balances s attacker_addr)%Z eqn : Httt;try congruence.
    destruct(1 >? 0 + env_account_balances s attacker_addr)%Z eqn : Httt;try congruence.
    assert(H_eq_tar : (target resp_state_strong) = target Attacker_init_cstate).
    {
      specialize (Attacker_target_constant s Hrc_s).
      destruct Attacker_target_constant.
      destruct H.
      rewrite H in *.
      inversion Hcs_s_a.
      intuition.
    }
    rewrite H_eq_tar in *.
    rewrite Hec_s in H_send_or_call_2.
    pose proof Hcs_s as Hcs_s_t.
    unfold contract_state in Hcs_s_t.
    simpl in Hcs_s_t.
    destruct (env_contract_states s (target Attacker_init_cstate)) eqn : Hcs_s_t_eqn;try congruence.
    destruct (weak_error_to_error_receive
    (wc_receive contract
       (s <| chain_height := S (chain_height s) |> <|
        current_slot := (current_slot s + 1)%nat |> <|
        finalized_height := finalized_height s |>)
       {|
         ctx_origin := attacker;
         ctx_from := attacker_addr;
         ctx_contract_address := target Attacker_init_cstate;
         ctx_contract_balance :=
           1 +
           env_account_balances s
             (target Attacker_init_cstate);
         ctx_amount := 1
       |} s2 (Some (serialize Fallback)))) eqn : H_wc_receive_s2;try congruence.
    unfold weak_error_to_error_receive in H_wc_receive_s2.
    unfold bind_error in H_wc_receive_s2.
    destruct (wc_receive contract
    (s <| chain_height := S (chain_height s) |> <|
     current_slot := (current_slot s + 1)%nat |> <|
     finalized_height := finalized_height s |>)
    {|
      ctx_origin := attacker;
      ctx_from := attacker_addr;
      ctx_contract_address := target Attacker_init_cstate;
      ctx_contract_balance :=
        1 +
        env_account_balances s (target Attacker_init_cstate);
      ctx_amount := 1
    |} s2 (Some (serialize Fallback)))
      eqn : H_wc_receive_s2';try congruence.
    
    set (cchain' := 
                    s <| chain_height := S (chain_height s) |> <| current_slot
                    := (current_slot s + 1)%nat |> <| finalized_height :=
                    finalized_height s |>
        ) in H_wc_receive_s2'.
    
    set (cctx' := {|
                       ctx_origin := attacker;
                       ctx_from := attacker_addr;
                       ctx_contract_address := target Attacker_init_cstate;
                       ctx_contract_balance :=
                         1 +
                         env_account_balances s (target Attacker_init_cstate);
                       ctx_amount := 1
                     |}) in H_wc_receive_s2'.
    
    destruct t2 as [new_state' new_acts'].

    destruct (wc_receive_strong ltac:(try eassumption))
    as (prev_state_strong1 & msg_strong1 & resp_state_strong1 &
      deser_state1 & deser_msg1 & <- & receive).

    simpl in deser_msg1.
    destruct (msg_strong1) eqn : H_msg1;try congruence.
    rewrite deserialize_serialize in deser_msg1.
    rewrite <- deser_msg1 in receive.
    rewrite deser_state1 in Hcs_s_t.
    simpl in receive.
    rename receive into receive_some1.
    reduce_receive.
    reduce_ether_receive.
    inversion receive_some1.
    subst.
    inversion H_wc_receive_s2;subst.
    inversion H_send_or_call_2;subst.
    simpl in H_exec.

    set (mid3 := {|
             chain_state_env :=
               set_contract_state (target Attacker_init_cstate)
                 (serialize resp_state_strong1)
                 (transfer_balance attacker_addr (target Attacker_init_cstate) 1
                    (set_contract_state attacker_addr
                       (serialize resp_state_strong)
                       (transfer_balance attacker attacker_addr 0
                          (add_new_block_to_env (get_valid_header miner s) s))));
             chain_state_queue := []
           |}).
    inversion H_exec.
    subst.
    inversion Htrans.
    subst.
    inversion Hcs_s'.
    unfold contract_state in H0.
    simpl in H0.
    destruct_address_eq;eauto;try congruence.
    setoid_rewrite deserialize_serialize in H0.
    inversion H0.
    unfold funds.
    simpl.
    destruct_address_eq;try congruence;eauto.
    intuition.
  Qed.

  Lemma attacker_call_Fallback_fund_state_correct:
    forall (s s':ChainState) (cstate : State) (attacker_state : AttackerState),
      contract_state s attacker_addr = Some attacker_state ->
      contract_state s caddr = Some cstate ->
      funds s attacker_addr >= 1 ->
      readyToStepState miner contract caddr s0 s ->
      transition miner s (attacker_call_Fallback cstate) = Ok s' ->
      funds s' caddr = (funds s caddr + 1) /\ 
      (exists cstate' ,
        contract_state s' caddr = Some cstate' /\
        cstate' = cstate).
  Proof.
    intros.
    split.
    eapply attacker_call_Fallback_fund_correct;eauto.
    eapply attacker_call_Fallback_state_correct;eauto.
  Qed.

  Lemma game_hold_base_liquidity:
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
    pose proof H0 as Hready.
    unfold readyToStepState in H0.
    destruct H0 as [Htrc_s Hqueue_s].
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
    destruct (cstate.(balance) >=? cstate.(targetAmount)) eqn : Hcstate_bal.
    - propify.
      pose proof Hready.
      eapply winner_call_Claim_transition_correct in H;eauto;try lia.
      destruct H as [s1 Htrans1].
      pose proof Htrans1.
      eapply winner_call_Claim_transition_state_correct in H;eauto;try lia.
      eapply readyToStepState_transition_readyToStepState in Hready as Hready1;eauto.
      assert (trace_s_s' :inhabited(TransitionTrace miner s s1)).
      {
        assert (TransitionTrace miner s s) by eapply clnil.
        assert(Hcall_act : is_call_act (winner_call_ClaimReward cstate) = true).
        {
          eapply (winner_call_ClaimReward_is_call_act cstate).
        }
        econstructor;eauto.
        eapply (snoc X (step_trans miner (winner_call_ClaimReward cstate) Hcall_act  Htrans1)).
      }
      exists s1.
      split.
      eauto.
      eauto.
    - propify.
      eapply user_call_Deposit_transition_correct in Hready as Ht;eauto.
      destruct Ht as [s1 Htrans1].
      eapply user_call_Deposit_state_funds_correct in Htrans1 as Ht;eauto.
      destruct Ht as [ _ [cstate1 [Hcs_s1 Hbal_s1]]].
      eapply readyToStepState_transition_readyToStepState in Hready as Hready1;eauto.
      assert (trace_s_s1 :inhabited(TransitionTrace miner s s1)).
      {
        assert(Hcall_act : is_call_act (winner_call_ClaimReward cstate1) = true).
        {
          eapply (winner_call_ClaimReward_is_call_act cstate).
        }
        assert (TransitionTrace miner s s) by eapply clnil.
        econstructor;eauto.
        eapply (snoc X (step_trans miner (user_call_Deposit cstate) Hcall_act Htrans1)).
      }
      destruct (cstate1.(balance) >=? cstate1.(targetAmount)) eqn : Hcstate_bal1.
      + propify.
        eapply winner_call_Claim_transition_correct in Hready1 as Ht;eauto;try lia.
        destruct Ht as [s2 Htrans2].
        eapply winner_call_Claim_transition_state_correct in Htrans2 as Ht;eauto;try lia.
        assert (trace_s_s2 :inhabited(TransitionTrace miner s s2)).
        {
          assert(Hcall_act1 : is_call_act (winner_call_ClaimReward cstate1) = true).
          {
            eapply (winner_call_ClaimReward_is_call_act cstate1).
          }
          destruct trace_s_s1 as [trace_s_s1].
          assert (TransitionTrace miner s s2).
          {
            eapply (snoc trace_s_s1 (step_trans miner (winner_call_ClaimReward cstate1) Hcall_act1  Htrans2)).
          }
          econstructor;eauto.
        }
        exists s2.
        split.
        eauto.
        eauto.
      + propify.
        eapply user_call_Deposit_transition_correct in Hready1 as Ht;eauto.
        destruct Ht as [s2 Htrans2].
        eapply user_call_Deposit_state_funds_correct in Htrans2 as Ht;eauto.
        destruct Ht as [ _ [cstate2 [Hcs_s2 Hbal_s2]]].
        eapply readyToStepState_transition_readyToStepState in Hready1 as Hready2;eauto.
        assert (trace_s_s2 :inhabited(TransitionTrace miner s s2)).
        {
          assert(Hcall_act : is_call_act (user_call_Deposit cstate2) = true).
          {
            eapply (user_call_Deposit_is_call_act cstate2).
          }
          destruct trace_s_s1 as [trace_s_s1].
          econstructor;eauto.
          eapply (snoc trace_s_s1 (step_trans miner (user_call_Deposit cstate1) Hcall_act Htrans2)).
        }
        destruct (cstate2.(balance) >=? cstate2.(targetAmount)) eqn : Hcstate_bal2.
        * propify.
          eapply winner_call_Claim_transition_correct in Hready2 as Ht;eauto;try lia.
          destruct Ht as [s3 Htrans3].
          eapply winner_call_Claim_transition_state_correct in Htrans3 as Ht;eauto;try lia.
          assert (trace_s_s3 :inhabited(TransitionTrace miner s s3)).
          {
            assert(Hcall_act : is_call_act (winner_call_ClaimReward cstate2) = true).
            {
              eapply (winner_call_ClaimReward_is_call_act cstate2).
            }
            destruct trace_s_s2 as [trace_s_s2].
            assert (TransitionTrace miner s s3).
            {
              eapply (snoc trace_s_s2 (step_trans miner (winner_call_ClaimReward cstate2) Hcall_act  Htrans3)).
            }
            econstructor;eauto.
          }
          exists s3.
          split.
          eauto.
          eauto.
        * propify.
          eapply user_call_Deposit_transition_correct in Hready2 as Ht;eauto.
          destruct Ht as [s3 Htrans3].
          eapply user_call_Deposit_state_funds_correct in Htrans3 as Ht;eauto.
          destruct Ht as [ _ [cstate3 [Hcs_s3 Hbal_s3]]].
          eapply readyToStepState_transition_readyToStepState in Hready2 as Hready3;eauto.
          assert (trace_s_s3 :inhabited(TransitionTrace miner s s3)).
          {
            assert(Hcall_act : is_call_act (user_call_Deposit cstate3) = true).
            {
              eapply (user_call_Deposit_is_call_act cstate3).
            }
            destruct trace_s_s2 as [trace_s_s2].
            econstructor;eauto.
            eapply (snoc trace_s_s2 (step_trans miner (user_call_Deposit cstate2) Hcall_act Htrans3)).
          }
          destruct (cstate3.(balance) >=? cstate3.(targetAmount)) eqn : Hcstate_bal3.
          **  propify.
              eapply winner_call_Claim_transition_correct in Hready3 as Ht;eauto;try lia.
              destruct Ht as [s4 Htrans4].
              eapply winner_call_Claim_transition_state_correct in Htrans4 as Ht;eauto;try lia.
              assert (trace_s_s4 :inhabited(TransitionTrace miner s s4)).
              {
                assert(Hcall_act : is_call_act (winner_call_ClaimReward cstate3) = true).
                {
                  eapply (winner_call_ClaimReward_is_call_act cstate2).
                }
                destruct trace_s_s3 as [trace_s_s3].
                assert (TransitionTrace miner s s4).
                {
                  eapply (snoc trace_s_s3 (step_trans miner (winner_call_ClaimReward cstate3) Hcall_act  Htrans4)).
                }
                econstructor;eauto.
              }
              exists s4.
              split.
              eauto.
              eauto.
          **  propify.
              eapply user_call_Deposit_transition_correct in Hready3 as Ht;eauto.
              destruct Ht as [s4 Htrans4].
              eapply user_call_Deposit_state_funds_correct in Htrans4 as Ht;eauto.
              destruct Ht as [ _ [cstate4 [Hcs_s4 Hbal_s4]]].
              eapply readyToStepState_transition_readyToStepState in Hready3 as Hready4;eauto.
              assert (trace_s_s4 :inhabited(TransitionTrace miner s s4)).
              {
                assert(Hcall_act : is_call_act (user_call_Deposit cstate4) = true).
                {
                  eapply (user_call_Deposit_is_call_act cstate3).
                }
                destruct trace_s_s3 as [trace_s_s3].
                econstructor;eauto.
                eapply (snoc trace_s_s3 (step_trans miner (user_call_Deposit cstate2) Hcall_act Htrans4)).
              }
              destruct (cstate4.(balance) >=? cstate4.(targetAmount)) eqn : Hcstate_bal4.
              --  propify.
                  eapply winner_call_Claim_transition_correct in Hready4 as Ht;eauto;try lia.
                  destruct Ht as [s5 Htrans5].
                  eapply winner_call_Claim_transition_state_correct in Htrans5 as Ht;eauto;try lia.
                  assert (trace_s_s5 :inhabited(TransitionTrace miner s s5)).
                  {
                    assert(Hcall_act : is_call_act (winner_call_ClaimReward cstate3) = true).
                    {
                      eapply (winner_call_ClaimReward_is_call_act cstate2).
                    }
                    destruct trace_s_s4 as [trace_s_s4].
                    assert (TransitionTrace miner s s5).
                    {
                      eapply (snoc trace_s_s4 (step_trans miner (winner_call_ClaimReward cstate4) Hcall_act  Htrans5)).
                    }
                    econstructor;eauto.
                  }
                  exists s5.
                  split.
                  eauto.
                  eauto.
              --  propify.
                  eapply user_call_Deposit_transition_correct in Hready4 as Ht;eauto.
                  destruct Ht as [s5 Htrans5].
                  eapply user_call_Deposit_state_funds_correct in Htrans5 as Ht;eauto.
                  destruct Ht as [ _ [cstate5 [Hcs_s5 Hbal_s5]]].
                  eapply readyToStepState_transition_readyToStepState in Hready4 as Hready5;eauto.
                  assert (trace_s_s5 :inhabited(TransitionTrace miner s s5)).
                  {
                    assert(Hcall_act : is_call_act (user_call_Deposit cstate5) = true).
                    {
                      eapply (user_call_Deposit_is_call_act cstate3).
                    }
                    destruct trace_s_s4 as [trace_s_s4].
                    econstructor;eauto.
                    eapply (snoc trace_s_s4 (step_trans miner (user_call_Deposit cstate5) Hcall_act Htrans5)).
                  }
                  destruct (cstate5.(balance) >=? cstate5.(targetAmount)) eqn : Hcstate_bal5;propify.
                    ++  eapply winner_call_Claim_transition_correct in Hready5 as Ht;
                        eauto;try lia.
                        destruct Ht as [s6 Htrans6].
                        eapply winner_call_Claim_transition_state_correct in Htrans6 as Ht;eauto;try lia.
                        assert (trace_s_s6 :inhabited(TransitionTrace miner s s6)).
                        {
                          assert(Hcall_act : is_call_act (winner_call_ClaimReward cstate3) = true).
                          {
                            eapply (winner_call_ClaimReward_is_call_act cstate2).
                          }
                          destruct trace_s_s5 as [trace_s_s5].
                          assert (TransitionTrace miner s s6).
                          {
                            eapply (snoc trace_s_s5 (step_trans miner (winner_call_ClaimReward cstate5) Hcall_act Htrans6)).
                          }
                          econstructor;eauto.
                        }
                        exists s6.
                        split.
                        eauto.
                        eauto.
                    ++  eapply user_call_Deposit_transition_correct in Hready5 as Ht;
                        eauto.
                        destruct Ht as [s6 Htrans6].
                        eapply user_call_Deposit_state_funds_correct in Htrans6 as Ht;eauto.
                        destruct Ht as [ _ [cstate6 [Hcs_s6 Hbal_s6]]].
                        eapply readyToStepState_transition_readyToStepState in Hready5 as Hready6;eauto.
                        assert (trace_s_s6 :inhabited(TransitionTrace miner s s6)).
                        {
                          assert(Hcall_act : is_call_act (user_call_Deposit cstate6) = true).
                          {
                            eapply (user_call_Deposit_is_call_act cstate3).
                          }
                          destruct trace_s_s5 as [trace_s_s5].
                          econstructor;eauto.
                          eapply (snoc trace_s_s5 (step_trans miner (user_call_Deposit cstate5) Hcall_act Htrans6)).
                        }
                        destruct (cstate6.(balance) >=? cstate6.(targetAmount)) eqn : Hcstate_bal6;propify.
                        *** eapply winner_call_Claim_transition_correct 
                            in Hready6 as Ht;
                            eauto;try lia.
                            destruct Ht as [s7 Htrans7].
                            eapply winner_call_Claim_transition_state_correct in Htrans7 as Ht;eauto;try lia.
                            assert (trace_s_s7 :inhabited(TransitionTrace miner s s7)).
                            {
                              assert(Hcall_act : is_call_act (winner_call_ClaimReward cstate6) = true).
                              {
                                eapply (winner_call_ClaimReward_is_call_act cstate2).
                              }
                              destruct trace_s_s6 as [trace_s_s6].
                              assert (TransitionTrace miner s s7).
                              {
                                eapply (snoc trace_s_s6 (step_trans miner (winner_call_ClaimReward cstate6) Hcall_act Htrans7)).
                              }
                              econstructor;eauto.
                            }
                            exists s7.
                            split.
                            eauto.
                            eauto.
                        *** eapply user_call_Deposit_transition_correct 
                            in Hready6 as Ht;
                            eauto.
                            destruct Ht as [s7 Htrans7].
                            eapply user_call_Deposit_state_funds_correct in Htrans7 as Ht;eauto.
                            destruct Ht as [ _ [cstate7 [Hcs_s7 Hbal_s7]]].
                            eapply readyToStepState_transition_readyToStepState in Hready6 as Hready7;eauto.
                            assert (trace_s_s7 :inhabited(TransitionTrace miner s s7)).
                            {
                              assert(Hcall_act : is_call_act (user_call_Deposit cstate6) = true).
                              {
                                eapply (user_call_Deposit_is_call_act cstate3).
                              }
                              destruct trace_s_s6 as [trace_s_s6].
                              econstructor;eauto.
                              eapply (snoc trace_s_s6 (step_trans miner (user_call_Deposit cstate7) Hcall_act Htrans7)).
                            }
                            destruct (cstate7.(balance) >=? cstate7.(targetAmount)) eqn : Hcstate_bal7;propify;try congruence.
                            ----  eapply winner_call_Claim_transition_correct 
                                  in Hready7 as Ht;
                                  eauto;try lia.
                                  destruct Ht as [s8 Htrans8].
                                  eapply winner_call_Claim_transition_state_correct in Htrans8 as Ht;eauto;try lia.
                                  assert (trace_s_s8 :inhabited(TransitionTrace miner s s8)).
                                  {
                                    assert(Hcall_act : is_call_act (winner_call_ClaimReward cstate6) = true).
                                    {
                                      eapply (winner_call_ClaimReward_is_call_act cstate2).
                                    }
                                    destruct trace_s_s7 as [trace_s_s7].
                                    assert (TransitionTrace miner s s8).
                                    {
                                      eapply (snoc trace_s_s7 (step_trans miner (winner_call_ClaimReward cstate7) Hcall_act Htrans8)).
                                    }
                                    econstructor;eauto.
                                  }
                                  exists s8.
                                  split.
                                  eauto.
                                  eauto.
                            ----  assert (targetAmount cstate = 7).
                                  {
                                    eapply targetAmount_eq_7_forall in Hcs_s;eauto.
                                    eapply reachable_through_contract_deployed in Hrct_s0_s
                                    ;eauto.
                                  }
                                  assert (targetAmount cstate7 = 7).
                                  {
                                    eapply targetAmount_eq_7_forall in Hcs_s7.
                                    eauto.
                                    unfold readyToStepState in Hready7.
                                    destruct_and_split.
                                    eapply transition_reachable_impl_reachable in H0;eauto.
                                    unfold readyToStepState in Hready7.
                                    destruct_and_split.
                                    eapply transition_reachable_impl_reachable_through in H0;eauto.
                                    eapply reachable_through_contract_deployed in H0
                                    ;eauto.
                                  }
                                  rewrite H0 in *.
                                  rewrite Hbal_s1 in Hbal_s2.
                                  rewrite Hbal_s2 in Hbal_s3.
                                  rewrite Hbal_s3 in Hbal_s4.
                                  rewrite Hbal_s4 in Hbal_s5.
                                  rewrite Hbal_s5 in Hbal_s6.
                                  rewrite Hbal_s6 in Hbal_s7.
                                  rewrite Hbal_s7 in Hcstate_bal7.
                                  intuition.
                                  assert(balance cstate >= 0).
                                  {
                                    eapply reachable_through_reachable in Hrct_s0_s as Hrc.
                                    eapply balance_gt_zero_forall in Hrc;eauto.
                                    eapply reachable_through_contract_deployed in Hrct_s0_s as Ht;eauto.
                                  }
                                  intuition.
  Qed.

  Lemma game_hold_strat_liquidity:
    strat_liquidity miner [user] user_strat [attacker] attacker_strat contract caddr s0.
  Proof.
    unfold strat_liquidity.
    intros.
    unfold isReachableUnderInterleavedExecution in H0.
    rename H into Hwell_sys.
    assert(H_init_t: is_init_state contract caddr s0) by eauto.
    decompose_is_init_state H_init_t.
    assert(Hrct_s0_s : reachable_through s0 s').
    {
      eapply transition_reachable_impl_reachable_through in H_init;eauto.
      econstructor;eauto.
    }
    assert( H_caddr_not_EOA : address_is_contract caddr = true).
    {
      eapply contract_addr_format in H_reachable;eauto.  
    }
    eapply (reachable_through_contract_deployed s0 s' caddr contract) in Hrct_s0_s as Hec_s;eauto.
    assert(Hrc_s : reachable s').
    {
      assert(transition_reachable miner contract caddr  s0 s').
      {
        econstructor;eauto.
      }
      eapply transition_reachable_impl_reachable in H;eauto.
    }
    assert(Hqueue_s:chain_state_queue s' = []).
    {
      eapply init_ready in H_init.
      eapply readyToStepState_interleavedExecution_readyToStepState in H_init;eauto.
      unfold readyToStepState in H_init.
      intuition.
    }
    rename s' into s.
    pose proof Hec_s.
    eapply deployed_contract_state_typed in H;eauto.
    destruct H as [cstate Hcs].
    assert( H_attacker_caddr_not_EOA : address_is_contract attacker_addr  = true).
    {
      specialize(H_attacker_cstate s cstate Hcs).
      destruct H_attacker_cstate as [  Ht].
      destruct H.
      eapply contract_addr_format in H.
      eauto.
      eauto.
    }
    assert( H_ec_s_a : env_contracts s attacker_addr = Some (attacker_contract : WeakContract)).
    {
      specialize(H_attacker_cstate s cstate Hcs).
      destruct H_attacker_cstate as [  Ht].
      destruct H.
      eauto.
    }
    assert(Hbal_gt_zero : (cstate.(balance) >= 0)).
    {
      eapply balance_gt_zero_forall in Hrc_s;eauto.
    }
    destruct ((cstate.(balance) =? 6)) eqn : Hcs

  Qed.
  








End EtherGame.


