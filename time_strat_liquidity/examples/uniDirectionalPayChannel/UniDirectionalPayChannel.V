(* https://orneklerle-solidity.vercel.app/app/uni-directional-payment-channel

  1、部署合约： Alice 使用 Ether 为智能合约提供资金。这“打开”了支付渠道。

  2、签署消息（链下过程）： Alice 签署消息，指定应向收款人支付多少以太币。每次付款都会重复此步骤。

  3、Bob“关闭”了支付渠道，取出了他那部分以太币，并将剩余部分发回给发送者

  3.5、延长渠道生命期：Alice可以选择是否延长渠道时间

  4、渠道到期： 任何人都可以关闭渠道

   问题1：close中的授权金额未验证；
   问题3：close方法中可能的重入攻击

*)
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
Require Import ModelBase.
Require Import TimeStratModel.
From Coq Require Import List.
From Coq Require Import Bool.
From Coq Require Import ZArith.
From Coq Require Import Arith.
From Coq Require Import String.
Import ListNotations.
Require Import Lia.
Import RecordSetNotations.
From Coq Require Import Permutation.
Require Import Coq.Program.Basics.
Require Import Coq.NArith.BinNatDef.

Section PaymentChannel.

  (* 假设基础类型已经定义 *)
  Context {BaseTypes : ChainBase}.
  Set Primitive Projections.
  Set Nonrecursive Elimination Schemes.
  Context {AddrSize : N}.
  Context {DepthFirst : bool}.

  Local Open Scope Z.

  Definition BlockNumber := nat.

  Notation "x >? y" := (Nat.ltb y x) (at level 70, no associativity).

  Definition bytes := N.

  Definition Signature := bytes.

  (* 合约状态 *)
  Record State := build_state {
    frozen : bool;                 (* 是否被冻结 *)
    sender : Address;              (* 发送者地址 *)
    recipient : Address;           (* 接收者地址 *)
    expiration : BlockNumber;      (* 过期区块 *)
    balance : Amount;              (* 合约余额 *)
  }.

  (* 设置参数 *)
  Record Setup := build_setup {
    setup_recipient : Address;     (* 接收者地址 *)
    setup_duration : BlockNumber;  (* 持续时间 *)
  }.

  Definition max_extend_times := 3%nat.

  (* 设置可设置实例 *)
  Instance state_settable : Settable State :=
    settable! build_state <frozen; sender; recipient; expiration; balance>.

  Instance setup_settable : Settable Setup :=
    settable! build_setup <setup_recipient; setup_duration>.

  (* 消息类型 *)
  Inductive Msg :=
  | Close (amount : Amount) (signature : Signature)
  (* | Extend (new_expiration : nat)     扩展到期时间 *)
  | ClaimTimeout.

  (* 序列化 *)
  Section Serialization.

    Global Instance Msg_serializable : Serializable Msg :=
      Derive Serializable Msg_rect<Close, ClaimTimeout>.

    Global Instance Setup_serializable : Serializable Setup :=
      Derive Serializable Setup_rect<build_setup>.

    Global Instance State_serializable : Serializable State :=
      Derive Serializable State_rect<build_state>.

  End Serialization.

  Global Definition serializeMsg msg := (@serialize Msg _) msg.
  Global Definition serializeState state := (@serialize State _) state.
  Global Definition serializeSetup setup := (@serialize Setup _) setup.

  Global Coercion serializeMsg : Msg >-> SerializedValue.
  Global Coercion serializeState : State >-> SerializedValue.
  Global Coercion serializeSetup : Setup >-> SerializedValue.

  (* 错误类型 *)
  Definition Error : Type := nat.
  Definition default_error : Error := 1%nat.

  (* 辅助函数：签名验证的抽象 *)
  (* 由于 Coq 不支持实际的签名验证，这里将其抽象化 *)

  Parameter sign : Address -> Amount -> Signature.

  Parameter verify_and_extract : Signature -> option (Address * Amount).

  Axiom verify_and_extract_correct :
    forall sender amount,
      verify_and_extract (sign sender amount) = Some (sender, amount).

  (* 初始化合约 *)
  (* 要求为外部地址，防止重入攻击 *)
  
  Definition init
             (chain : Chain)
             (ctx : ContractCallContext)
             (setup : Setup)
    : result State Error :=
    let msg_sender := ctx_from ctx in
    let msg_value := ctx_amount ctx in
    if  (msg_value >? 0)%Z && 
        (address_not_contract msg_sender) &&
        (address_not_contract setup.(setup_recipient)) &&
        (setup.(setup_duration) >? 0)%nat
    then
      Ok (build_state
            false                              
            msg_sender                        
            setup.(setup_recipient)          
            (chain.(current_slot) + setup.(setup_duration))%nat
            msg_value                       
          )
    else
      Err default_error.

  (* 冻结状态检查 *)
  Definition is_not_frozen (state : State) : bool :=
    negb state.(frozen).

  (* 冻结合约 *)
  Definition freeze_contract (state : State) : State :=
    state <| frozen := true |>
          <| balance := 0 |>.


  (* 关闭支付通道 *)
  Definition close_channel
          (chain : Chain)
          (ctx : ContractCallContext)
          (state : State)
          (amount : Amount)
          (signature : Signature) (* 修改参数类型为 Signature *)
    : result (State * list ActionBody) Error :=
    if (is_not_frozen state)
    then
      if (ctx_from ctx =? state.(recipient))%address
      then
        match verify_and_extract signature with (* 使用 match 处理 option 类型 *)
        | Some (signature_sender, signature_amount) =>
            if (signature_sender =? state.(sender))%address && 
              (signature_amount =? amount)
            then
              if (signature_amount <=? state.(balance))%Z
              then
                let actions := [act_transfer state.(recipient) signature_amount] in
                let remaining := state.(balance) - signature_amount in
                let new_actions := actions ++ [act_transfer state.(sender) remaining] in
                let new_state := freeze_contract state in
                Ok (new_state, new_actions)
              else
                Err default_error (* 错误：签名中的金额超过余额 *)
            else
              Err default_error (* 错误：签名中的错误 *)
        | None =>
            Err default_error (* 错误：签名验证失败 *)
        end
      else
        Err default_error (* 错误：调用者不是接收者 *)
    else
        Err default_error. (* 错误：合约已被冻结 *)


  (* 认领超时 *)
  Definition claim_timeout
             (chain : Chain)
             (ctx : ContractCallContext)
             (state : State)
    : result (State * list ActionBody) Error :=
    if (is_not_frozen state)
    then
      if (state.(expiration) <=? chain.(current_slot))%nat
      then
        let actions := [act_transfer state.(sender) state.(balance)] in
        let new_state := freeze_contract state in
        Ok (new_state, actions)
      else
        Err default_error (* 错误：当前区块未到过期时间 *)
    else
      Err default_error. (* 错误：合约已被冻结 *)

  (* 合约接收函数 *)
  Definition receive
             (chain : Chain)
             (ctx : ContractCallContext)
             (state : State)
             (msg : option Msg)
    : result (State * list ActionBody) Error :=
    if (ctx_amount ctx =? 0)%Z && (address_not_contract ctx.(ctx_from )) then
      match msg with
      | Some (Close amount signature) => close_channel chain ctx state amount signature
      (* | Some (Extend new_expiration) => extend chain ctx state new_expiration *)
      | Some ClaimTimeout => claim_timeout chain ctx state
      (* 可以自己定义，类似于fallback *)
      | None => Err default_error
      end
    else Err default_error.

  (* 定义合约 *)
  Definition contract : Contract Setup Msg State Error :=
    build_contract init receive.

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

  (* Variable u_sender : Address.

  Variable pre_s : ChainState. *)

  (* Definition init_cstate := contract_state
  (set_contract_state caddr (serialize init_cstate)
     (add_contract caddr (contract:WeakContract) (transfer_balance u_sender caddr 0 s0)))
  caddr. *)

  Definition u_sender := (init_cstate.(sender)).

  Definition u_recipient := (init_cstate.(recipient)).

  Variable auth_amount : Amount.

  Definition start_time := s0.(current_slot).

  Parameter generate_signature : Address -> Amount -> Signature.

  Definition recipient_Close 
            (state : State) 
            (amount : Amount) 
            (signature : bytes) 
            : Action :=
    build_call state.(recipient) caddr 0 (Close amount signature).

  Definition anyone_ClaimTimeout 
            (state : State) 
            (addr: Address) 
            : Action :=
    build_call addr caddr 0 ClaimTimeout.

  Definition wait_to_expiration time expiration:=
    wait_action miner (Z.of_nat(expiration + 1 - time ))%Z.

  Definition sender_strategy : (strat miner [u_sender]) :=
    fun s0 s tr =>
      let time := current_slot s in
      match get_contract_state s caddr with
      | Some state =>
          if state.(frozen) then
            []
          else
            if (state.(expiration) <=? time)%nat then
              [anyone_ClaimTimeout state state.(sender)]
            else
              [wait_to_expiration time state.(expiration)]
      | None => []
      end.

  Definition recipient_strategy : (strat miner[u_recipient]) :=
    fun s0 s tr => [] .

  Tactic Notation "contract_simpl" := contract_simpl @receive @init.

  Ltac reduce_init :=
  match goal with
  | H : init ?chain ?ctx ?setup = Ok ?result |- _ =>
      unfold init in H; (* 展开 init 函数 *)
      let msg_sender := fresh "msg_sender" in
      let msg_value := fresh "msg_value" in
      remember (ctx_from ctx) as msg_sender eqn:Emsg_sender;
      remember (ctx_amount ctx) as msg_value eqn:Emsg_value;
      destruct ((msg_value >? 0)%Z && (address_not_contract msg_sender)) eqn:Econd1 in H; try discriminate;
      destruct (address_not_contract (setup.(setup_recipient))) eqn:Econd2 in H; try discriminate;
      destruct ((setup.(setup_duration) >? 0)%nat) eqn:Econd3 in H; try discriminate;
      injection H as H_build;
      clear H;
      rename H_build into H
  end.

  Ltac destruct_message :=
    repeat match goal with
      | H : Blockchain.receive _ _ _ _ _ = Ok _ |- _ => unfold Blockchain.receive in H; cbn in H
      | msg : option Msg |- _ => destruct msg
      | msg : Msg |- _ => destruct msg
      | H : Blockchain.receive _ _ _ _ None = Ok _ |- _ => now contract_simpl
      | H : receive _ _ _ None = Ok _ |- _ => now contract_simpl
      end.

  Ltac reduce_claim_timeout := 
    match goal with
    | H : claim_timeout ?chain ?ctx ?state = _ |- _ =>
        unfold claim_timeout in H;
        destruct (is_not_frozen state) eqn:EFreeze in H; try discriminate;
        destruct ((state.(expiration) <=? chain.(current_slot))%nat) eqn:EExpiration in H; try discriminate
    end.

  Ltac reduce_close_channel := 
    match goal with
    | H : close_channel ?chain ?ctx ?state ?amount ?signature = _ |- _ =>
        unfold close_channel in H;
        destruct (is_not_frozen state) eqn:EFreeze in H; try discriminate;
        destruct ((ctx_from ctx =? state.(recipient))%address) eqn:ERecipient in H; try discriminate;
        destruct (verify_and_extract signature) as [ [signature_sender signature_amount] | ] eqn:ESig in H;
        [destruct ((signature_sender =? state.(sender))%address && (signature_amount =? amount)) eqn:H_sig in H; try discriminate;
        destruct ((signature_amount <=? state.(balance))%Z) eqn:H_balance in H; try discriminate |
        discriminate
        ]
    end.

  Ltac reduce_receive_some :=
    match goal with
    | H : receive ?chain ?ctx ?prev_state ?msg = Ok (?new_state, ?new_acts) |- _ =>
        (* 1. 展开 receive 函数 *)
        unfold receive in H;
        (* 2. 分解 ctx_amount ctx 是否为 0 *)
        destruct ((ctx_amount ctx =? 0)%Z) eqn:EAmount in H; try discriminate;
        (* 3. 分解 address_not_contract ctx.(ctx_from) 是否为 true *)
        destruct (address_not_contract ctx.(ctx_from)) eqn:EFrom_R in H; try discriminate;
        simpl in *;
        destruct msg eqn:Emsg in H; try discriminate;
        destruct_message;try congruence
    end.

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
    - reduce_receive_some.
      destruct_message;try congruence.
      + reduce_close_channel. cbn in *.
        inversion receive_some. simpl.
        lia.
      (* + reduce_extend. cbn in *.
        inversion receive_some. simpl.
        lia. *)
      + reduce_claim_timeout. cbn in *.
        inversion receive_some. simpl.
        lia.
    - reduce_receive_some.
      destruct_message;try congruence.
      + reduce_close_channel. 
        inversion receive_some; destruct head; cbn in *; lia.
      + reduce_claim_timeout. 
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


  Lemma frozen_impl_bal bstate:
    reachable bstate ->
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    exists cstate, 
      contract_state bstate caddr = Some cstate /\
      (cstate.(frozen) = true -> (cstate.(balance) = 0)%Z).
  Proof.
    contract_induction;intros;cbn in *;eauto;try congruence;try lia.
    - reduce_init.
      inversion init_some.
      subst.
      cbn in *.
      congruence.
    - reduce_receive_some.
      + reduce_close_channel.
        inversion receive_some;subst;cbn in *.
        lia.
      + reduce_claim_timeout.
        inversion receive_some;subst;cbn in *.
        lia.
    - reduce_receive_some.
      + reduce_close_channel. 
        inversion receive_some; destruct head; cbn in *; lia.
      + reduce_claim_timeout. 
        inversion receive_some; destruct head; cbn in *; lia.
    - solve_facts.
  Qed.

  Lemma frozen_impl_bal_forall bstate cstate:
    reachable bstate ->
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    contract_state bstate caddr = Some cstate ->
    cstate.(frozen) = true -> 
    (cstate.(balance) = 0)%Z.
  Proof.
    intros.
    eapply frozen_impl_bal in H;eauto.
    destruct H.
    destruct_and_split.
    rewrite H in H1;
    inversion H1; subst;
    destruct_and_split.
    eauto.
  Qed.

  Lemma contract_constants_receive :forall prev_state new_state chain ctx msg new_acts,
    receive chain ctx prev_state msg = Ok (new_state, new_acts) ->
      prev_state.(sender) = new_state.(sender)
      /\ prev_state.(recipient) = new_state.(recipient)
      /\ prev_state.(expiration) = new_state.(expiration).
  Proof.
    intros.
    reduce_receive_some.
    - reduce_close_channel.
      inversion H.
      split.
      simpl.
      eauto.
      simpl.
      eauto.
    (* - reduce_extend.
      inversion H.
      split.
      simpl.
      eauto.
      simpl.
      eauto. *)
    - reduce_claim_timeout.
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
      cstate.(sender) = init_cstate.(sender) /\
      cstate.(recipient) = init_cstate.(recipient) /\
      cstate.(expiration) = init_cstate.(expiration).
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

      + try rewrite env_eq in *; try setoid_rewrite env_eq;eauto.
      + try rewrite env_eq in *; try setoid_rewrite env_eq;eauto.
  Qed.

  Lemma contract_constants_transition_via :forall s,
    transition_reachable miner contract caddr s0 s ->
    exists cstate, 
      contract_state s caddr = Some cstate /\
      cstate.(sender) = init_cstate.(sender) /\
      cstate.(recipient) = init_cstate.(recipient) /\
      cstate.(expiration) = init_cstate.(expiration).
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

    eauto.
  Qed.

  Lemma sender_and_recipient_is_EOA bstate:
    reachable bstate ->
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    exists cstate,
      contract_state bstate caddr = Some cstate
      /\ address_not_contract cstate.(sender) = true
      /\ address_not_contract cstate.(recipient) = true.
  Proof.
    contract_induction;intros;cbn in *;eauto;try congruence;try lia.
    - reduce_init;
      inversion init_some;
      split;simpl;eauto.
      propify.
      destruct_and_split.
      eauto.
    - reduce_receive_some.
      + reduce_close_channel.
        inversion receive_some.
        simpl.
        eauto.
      (* + reduce_extend.
        inversion receive_some.
        simpl.
        eauto. *)
      + reduce_claim_timeout.
        inversion receive_some.
        simpl.
        eauto.
    - reduce_receive_some.
      + reduce_close_channel.
        inversion receive_some; destruct head; cbn in *;eauto.
      (* + reduce_extend.
        inversion receive_some; destruct head; cbn in *;eauto. *)
      + reduce_claim_timeout.
        inversion receive_some; destruct head; cbn in *;eauto.
    - solve_facts.
  Qed.

  Lemma sender_and_recipient_is_EOA_forall bstate cstate:
    reachable bstate ->
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    contract_state bstate caddr = Some cstate ->
    (address_not_contract cstate.(sender) = true
      /\ address_not_contract cstate.(recipient) = true).
  Proof.
    intros.
    eapply sender_and_recipient_is_EOA in H;eauto.
    destruct H.
    destruct_and_split.
    rewrite H in H1;
    inversion H1; subst;
    destruct_and_split.
    eauto.
    rewrite H in H1;
    inversion H1; subst;
    destruct_and_split.
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

  Lemma anyone_ClaimTimeout_is_call_act cstate:
    is_call_act (anyone_ClaimTimeout  cstate (sender cstate)) = true.
  Proof.
    unfold is_call_act.
    unfold anyone_ClaimTimeout .
    simpl.
    eauto.
  Qed.

  Lemma wait_to_expiration_is_normal_wait :
    forall time expiration,
      (expiration > time)%nat ->
      is_normal_wait_act (wait_to_expiration time expiration) = true.
  Proof.
    intros.
    unfold is_normal_wait_act.
    unfold wait_to_expiration.
    simpl.
    destruct_address_eq;eauto.
    simpl.
    unfold wait_action.
    unfold act_amount.
    simpl.
    assert ((expiration0 + 1 - time) >? 0 = true).
    {
      propify.
      lia.
    }
    unfold Z.of_nat.
    destruct ((expiration0 + 1 - time)%nat) eqn : HE.
    lia.
    simpl.
    eauto.
  Qed.
  
  Lemma anyone_ClaimTimeout_transition_correct:
    forall (s:ChainState) cstate,
      contract_state s caddr = Some cstate ->
      frozen cstate = false ->
      (expiration cstate <=? current_slot s)%nat = true ->
      transition_reachable miner contract caddr s0 s ->
      exists s', transition miner s (anyone_ClaimTimeout cstate (sender cstate)) = Ok s' .
  Proof.
    intros * Hcs_s Hfrozen_cstate Hexpir_s Htrc_s.
    unfold transition.
    eapply transition_reachable_queue_is_empty in Htrc_s as Hqueue_s;eauto.
    unfold queue_isb_empty.
    rewrite Hqueue_s.
    simpl.
    unfold evaluate_action .
    assert (H_header:validate_header (get_valid_header miner s) s = true).
    {
      eapply get_valid_header_is_valid_header.
    }
    rewrite H_header.
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
    assert(H_EOA: address_is_contract (sender cstate) = false /\ address_is_contract (recipient cstate) = false).
    {
      eapply transition_reachable_impl_reachable in Htrc_s.
      eapply sender_and_recipient_is_EOA_forall in Hcs_s;eauto.
      destruct_and_split.
      eapply address_not_contract_negb in H0.
      eapply address_not_contract_negb in H.
      eauto.
      eapply address_not_contract_negb in H0.
      eapply address_not_contract_negb in H.
      eauto.
      eauto.
    }

    destruct H_EOA as [H_sender_EOA H_recipient_EOA].
    destruct_address_eq;try congruence.
    simpl.
    rewrite H_sender_EOA.
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
    + assert ((0 >? miner_reward + env_account_balances s (sender cstate))%Z 
                = false).
      {
        unfold miner_reward.
        eapply (account_balance_nonnegative s (sender cstate)) in Hrc_s.
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
      rewrite H_sender_EOA.
      unfold negb.
      simpl.
      unfold claim_timeout.
      unfold is_not_frozen.
      rewrite Hfrozen_cstate.
      simpl.
      assert(expiration cstate <=? current_slot s + 1 = true)%nat.
      {
        propify.
        lia.
      }
      rewrite H0.
      simpl.
      unfold send_or_call.
      assert(balance cstate <? 0 = false).
      {
        eapply (account_balance_nonnegative s caddr) in Hrc_s.
        propify.
        lia.
      }
      rewrite H1.
      simpl.
      destruct_address_eq;try congruence.
      assert(balance cstate >? 0 + (env_account_balances s caddr) = false)%Z.
      {
        propify.
        lia.
      }
      rewrite H2.
      assert (H_sender_none: env_contracts s (sender cstate) = None).
      { 
        destruct (env_contracts s (sender cstate)) eqn:H_env.
        - exfalso.
          apply (contract_addr_format (sender cstate) w) in H_env; eauto.
          congruence.
        - reflexivity.
      }
      rewrite H_sender_none.
      rewrite H_sender_EOA.
      simpl.
      eauto.
    + eapply address_not_contract_negb in H_miner.
      congruence.
    + assert ((0 >? env_account_balances s (sender cstate))%Z = false).
      {
        unfold miner_reward.
        eapply (account_balance_nonnegative s (sender cstate)) in Hrc_s.
        lia.
      }
      rewrite H.
      rewrite Hec_s.
      unfold contract_state in Hcs_s.
      simpl in Hcs_s.
      destruct (env_contract_states s caddr) eqn : Ht;try congruence.
      simpl.
      rewrite Hcs_s.
      simpl.
      setoid_rewrite deserialize_serialize.
      simpl.
      cbn in *.
      unfold receive.
      simpl.
      unfold address_not_contract.
      rewrite H_sender_EOA.
      unfold negb.
      simpl.
      unfold claim_timeout.
      unfold is_not_frozen.
      rewrite Hfrozen_cstate.
      simpl.
      assert(expiration cstate <=? current_slot s + 1 = true)%nat.
      {
        propify.
        lia.
      }
      rewrite H0.
      simpl.
      unfold send_or_call.
      assert(balance cstate <? 0 = false).
      {
        eapply (account_balance_nonnegative s caddr) in Hrc_s.
        propify.
        lia.
      }
      rewrite H1.
      simpl.
      destruct_address_eq;try congruence.
      assert(balance cstate >? 0 + (env_account_balances s caddr) = false)%Z.
      {
        propify.
        lia.
      }
      rewrite H2.
      assert (H_sender_none: env_contracts s (sender cstate) = None).
      { 
        destruct (env_contracts s (sender cstate)) eqn:H_env.
        - exfalso.
          apply (contract_addr_format (sender cstate) w) in H_env; eauto.
          congruence.
        - reflexivity.
      }
      rewrite H_sender_none.
      rewrite H_sender_EOA.
      simpl.
      eauto.
  Qed.

  Lemma wait_to_expiration_transition_correct:
    forall (s:ChainState) cstate,
      contract_state s caddr = Some cstate ->
      frozen cstate = false ->
      (expiration cstate <=? current_slot s)%nat = false ->
      transition_reachable miner contract caddr s0 s ->
      exists s', transition miner s (wait_to_expiration (current_slot s) (expiration cstate)) = Ok s' .
  Proof.
    intros * Hcs_s Hfrozen_cstate Hexpir_s Htrc_s.
    unfold transition.
    eapply transition_reachable_queue_is_empty in Htrc_s as Hqueue_s;eauto.
    unfold queue_isb_empty.
    rewrite Hqueue_s.
    simpl.
    unfold evaluate_action .
    specialize(wait_to_expiration_is_normal_wait (current_slot s) (expiration cstate)) as Hwait.
    propify.
    assert ((expiration cstate > current_slot s)%nat).
    {
      lia.
    }
    eapply Hwait in H.
    clear Hwait.
    rename H into Hwait.
    rewrite Hwait.
    eapply get_normal_wait_valid_header_is_valid_header in Hwait as Hheader.
    rewrite Hheader.
    simpl.
    eauto.
    eapply address_not_contract_negb in H_miner.
    eauto.
  Qed.

  Definition correct_signature s signature amount:=
    env_contracts s caddr = Some (contract : WeakContract) ->
    exists cstate signature_sender signature_amount,
      contract_state s caddr = Some cstate /\
      verify_and_extract signature = Some (signature_sender, signature_amount) /\
      signature_sender = cstate.(sender) /\
      amount = signature_amount /\
      signature_amount <= cstate.(balance). 

  Lemma anyone_ClaimTimeout_state_correct:
    forall (s s':ChainState) cstate,
      contract_state s caddr = Some cstate ->
      frozen cstate = false ->
      (expiration cstate <=? current_slot s)%nat = true ->
      transition_reachable miner contract caddr s0 s ->
      transition miner s (anyone_ClaimTimeout cstate (sender cstate)) = Ok s' ->
      exists state,
        contract_state s' caddr = Some state /\
        state.(frozen) = true.
  Proof.
    intros * Hcs_s Hfrozen Htime Htrc_s Htrans.
    pose proof Htrc_s.
    eapply transition_reachable_queue_is_empty in Htrc_s as Hqueue_s;eauto.
    assert (Hact_call : is_call_act (anyone_ClaimTimeout cstate (sender cstate)) = true).
    {
      eapply anyone_ClaimTimeout_is_call_act.
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
    assert(H_EOA: address_is_contract (sender cstate) = false /\ address_is_contract (recipient cstate) = false).
    {
      eapply transition_reachable_impl_reachable in Htrc_s.
      eapply sender_and_recipient_is_EOA_forall in Hcs_s;eauto.
      intuition.
      eapply address_not_contract_negb;eauto.
      eapply address_not_contract_negb;eauto.
      eauto.
    }
    destruct H_EOA as [H_sender_EOA H_recipient_EOA].
    assert( H_caddr_not_EOA : address_is_contract caddr = true).
    {
      eapply contract_addr_format in Hec_s.
      eauto.
      eapply transition_reachable_impl_reachable in Htrc_s;eauto.
    }
    eapply deployed_contract_state_typed in Hec_s';eauto.
    destruct Hec_s' as [cstate_s' Hcs_s'].
    exists cstate_s'.
    split.
    eauto.
    unfold transition in Htrans.
    unfold queue_isb_empty in Htrans.
    rewrite Hqueue_s in Htrans.
    destruct (is_normal_wait_act  (anyone_ClaimTimeout cstate (sender cstate))) eqn : Hb_wait.
    eapply is_call_act_true_is_wait_act_false in Hact_call.
    eapply normal_wait_action_is_wait_act in Hb_wait.
    congruence.
    rewrite Hact_call in Htrans.
    destruct (evaluate_action  true s (get_valid_header miner s) [anyone_ClaimTimeout cstate  (sender cstate)]) eqn : H_exec;try congruence.
    unfold evaluate_action in H_exec.
    destruct (validate_header (get_valid_header miner s) s) ; try congruence.
    destruct (find_origin_neq_from [anyone_ClaimTimeout cstate (sender cstate)]) ;try congruence.
    destruct (find_invalid_root_action
    [anyone_ClaimTimeout cstate  (sender cstate)]) ; try congruence.
    set (mid_state := {|
      chain_state_env := add_new_block_to_env (get_valid_header miner s) s;
      chain_state_queue := [anyone_ClaimTimeout cstate  (sender cstate)]
    |}) in H_exec.
    simpl in *.
    destruct(send_or_call (sender cstate) (sender cstate) caddr 0
    (Some (serialize ClaimTimeout))
    (add_new_block_to_env (get_valid_header miner s) s)) eqn : H_send_or_call_ClaimTimeout;try congruence.
    unfold send_or_call in  H_send_or_call_ClaimTimeout.
    simpl in H_send_or_call_ClaimTimeout.
    destruct_address_eq;try congruence.
    (* 
      e: sender cstate = miner
      n: caddr <> sender cstate
      e0: caddr = caddr
      n0: caddr <> miner 
    *)
    eapply address_not_contract_negb in H_miner.
    destruct(0 >? miner_reward + env_account_balances s (sender cstate))%Z;try congruence.
    rewrite Hec_s in H_send_or_call_ClaimTimeout.
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
          ctx_origin := sender cstate;
          ctx_from := sender cstate;
          ctx_contract_address := caddr;
          ctx_contract_balance := 0 + env_account_balances s caddr;
          ctx_amount := 0
        |} s1 (Some (serialize ClaimTimeout)))) eqn : H_wc_receive_s1;try congruence.
    unfold weak_error_to_error_receive in H_wc_receive_s1.
    unfold bind_error in H_wc_receive_s1.
    destruct (wc_receive contract
    (s <| chain_height := S (chain_height s) |> <| current_slot :=
      (current_slot s + 1)%nat |> <| finalized_height :=
      finalized_height s |>)
    {|
      ctx_origin := sender cstate;
      ctx_from := sender cstate;
      ctx_contract_address := caddr;
      ctx_contract_balance := 0 + env_account_balances s caddr;
      ctx_amount := 0
    |} s1 (Some (serialize ClaimTimeout)))
      eqn : H_wc_receive_s1';try congruence.
    
    set (cchain := s <| chain_height := S (chain_height s) |> <| current_slot :=
    (current_slot s + 1)%nat |> <| finalized_height :=
    finalized_height s |>) in H_wc_receive_s1'.
    set (cctx := {|
    ctx_origin := sender cstate;
    ctx_from := sender cstate;
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
    destruct ((ctx_amount cctx =? 0)%Z &&
    address_not_contract (ctx_from cctx)) eqn : requirements_check;try congruence.
    reduce_claim_timeout.
    inversion receive_some.
    subst.
    inversion H_wc_receive_s1;subst.
    inversion H_send_or_call_ClaimTimeout;subst.
    simpl in H_exec.
    destruct (  send_or_call (sender cstate) caddr (sender prev_state_strong)
    (balance prev_state_strong) None
    (set_contract_state caddr
        (serialize (freeze_contract prev_state_strong))
        (transfer_balance (sender cstate) caddr 0
          (add_new_block_to_env (get_valid_header (sender cstate) s) s)))) eqn : H_send_or_call_None;try congruence.
    unfold send_or_call in H_send_or_call_None.
    destruct_match in H_send_or_call_None;try congruence.
    destruct_match in H_send_or_call_None;try congruence.
    destruct (
        env_contracts
        (set_contract_state caddr
          (serialize (freeze_contract prev_state_strong))
          (transfer_balance (sender cstate) caddr 0
              (add_new_block_to_env (get_valid_header (sender cstate) s) s)))
        (sender prev_state_strong) ) 
    eqn : H_none_wc.
    set (
        mid_env:=(set_contract_state caddr
          (serialize (freeze_contract prev_state_strong))
          (transfer_balance (sender cstate) caddr 0
              (add_new_block_to_env (get_valid_header (sender cstate) s) s)))) 
    in H_none_wc.
    set (
      mid_mid_end_state := {|
      chain_state_env :=
        set_contract_state caddr
          (serialize (freeze_contract prev_state_strong))
          (transfer_balance (sender cstate) caddr 0
              (add_new_block_to_env
                (get_valid_header (sender cstate) s) s));
      chain_state_queue :=
        [{|
            act_origin := sender cstate;
            act_from := caddr;
            act_body :=
              act_transfer (sender prev_state_strong)
                (balance prev_state_strong)
          |}]
      |}
    ).
    assert(Hreachable_through_s'_mid_mid_end_state : reachable_through s mid_mid_end_state).
    {
      assert(step_s'_mid : ChainStep s mid_state).
      {
        eapply (step_block s mid_state  (get_valid_header (sender cstate) s));eauto.
        unfold get_valid_header.
        eapply build_is_valid_next_block;simpl;intuition;eauto.
        unfold miner_reward.
        lia.
        eapply Forall_forall.
        intros.
        simpl in H0.
        destruct H0.
        rewrite <- H0.
        unfold act_is_from_account.
        simpl.
        eauto.
        inversion H0.
        eapply Forall_forall;eauto.
        intros.
        simpl in H0.
        destruct H;eauto;intuition.
        rewrite <- H2.
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
        eapply (step_action mid_state mid_mid_end_state (anyone_ClaimTimeout cstate (sender cstate)) [] 
        [{|
          act_origin := sender cstate;
          act_from := caddr;
          act_body :=
            act_transfer (sender prev_state_strong)
              (balance prev_state_strong)
        |}] )
        ;eauto.
        eapply (eval_call (sender cstate) (sender cstate) caddr 0 
          (contract:WeakContract) (Some (serialize ClaimTimeout))
          ( s1) (serialize (freeze_contract prev_state_strong)) 
          [act_transfer (sender prev_state_strong) (balance prev_state_strong)]);eauto;intuition.
        eapply reachable_through_reachable in H0.
        eapply (account_balance_nonnegative mid_state (sender cstate)) in H0.
        lia.
        eauto.
        eapply build_env_equiv;eauto.
      }
      assert(reachable mid_state).
      {
        eapply reachable_through_reachable;eauto.
      }
      eapply reachable_through_step in H1;eauto.
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
    eapply (address_not_contract_not_wc (sender prev_state_strong)) in Hreachable_mid_mid.
    intuition.
    intuition.
    inversion  Hcstate_s_t0.
    rewrite H1 in H_send_or_call_None.
    rewrite H_sender_EOA in H_send_or_call_None.
    inversion H_send_or_call_None;subst.
    simpl in H_exec.
    inversion H_exec;subst.
    inversion Htrans.
    subst.
    inversion Hcs_s'.
    unfold contract_state in H1.
    simpl in H1.
    destruct_address_eq;eauto.
    setoid_rewrite deserialize_serialize in H1.
    inversion H1.
    unfold freeze_contract.
    simpl.
    eauto.
    eapply address_not_contract_negb in H_miner.
    rewrite e0 in *.
    intuition.
    (* 
      n: sender cstate <> miner
      n0: caddr <> sender cstate
      e: caddr = caddr
      n1: caddr <> miner
    *)
    eapply address_not_contract_negb in H_miner.
    destruct(0 >? env_account_balances s (sender cstate))%Z;try congruence.
    rewrite Hec_s in H_send_or_call_ClaimTimeout.
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
          ctx_origin := sender cstate;
          ctx_from := sender cstate;
          ctx_contract_address := caddr;
          ctx_contract_balance := 0 + env_account_balances s caddr;
          ctx_amount := 0
        |} s1 (Some (serialize ClaimTimeout)))) eqn : H_wc_receive_s1;try congruence.
    unfold weak_error_to_error_receive in H_wc_receive_s1.
    unfold bind_error in H_wc_receive_s1.
    destruct (wc_receive contract
    (s <| chain_height := S (chain_height s) |> <| current_slot :=
      (current_slot s + 1)%nat |> <| finalized_height :=
      finalized_height s |>)
    {|
      ctx_origin := sender cstate;
      ctx_from := sender cstate;
      ctx_contract_address := caddr;
      ctx_contract_balance := 0 + env_account_balances s caddr;
      ctx_amount := 0
    |} s1 (Some (serialize ClaimTimeout)))
      eqn : H_wc_receive_s1';try congruence.
    
    set (cchain := s <| chain_height := S (chain_height s) |> <| current_slot :=
    (current_slot s + 1)%nat |> <| finalized_height :=
    finalized_height s |>) in H_wc_receive_s1'.
    set (cctx := {|
    ctx_origin := sender cstate;
    ctx_from := sender cstate;
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
    destruct ((ctx_amount cctx =? 0)%Z &&
    address_not_contract (ctx_from cctx)) eqn : requirements_check;try congruence.
    reduce_claim_timeout.
    inversion receive_some.
    subst.
    inversion H_wc_receive_s1;subst.
    inversion H_send_or_call_ClaimTimeout;subst.
    simpl in H_exec.
    destruct (  send_or_call (sender cstate) caddr (sender prev_state_strong)
    (balance prev_state_strong) None
    (set_contract_state caddr
        (serialize (freeze_contract prev_state_strong))
        (transfer_balance (sender cstate) caddr 0
          (add_new_block_to_env (get_valid_header miner s) s)))) eqn : H_send_or_call_None;try congruence.
    unfold send_or_call in H_send_or_call_None.
    destruct_match in H_send_or_call_None;try congruence.
    destruct_match in H_send_or_call_None;try congruence.
    destruct (
        env_contracts
        (set_contract_state caddr
          (serialize (freeze_contract prev_state_strong))
          (transfer_balance (sender cstate) caddr 0
              (add_new_block_to_env (get_valid_header miner s) s)))
        (sender prev_state_strong) ) 
    eqn : H_none_wc.
    set (
        mid_env:=(set_contract_state caddr
          (serialize (freeze_contract prev_state_strong))
          (transfer_balance (sender cstate) caddr 0
              (add_new_block_to_env (get_valid_header miner s) s)))) 
    in H_none_wc.
    set (
      mid_mid_end_state := {|
      chain_state_env :=
        set_contract_state caddr
          (serialize (freeze_contract prev_state_strong))
          (transfer_balance (sender cstate) caddr 0
              (add_new_block_to_env
                (get_valid_header miner s) s));
      chain_state_queue :=
        [{|
            act_origin := sender cstate;
            act_from := caddr;
            act_body :=
              act_transfer (sender prev_state_strong)
                (balance prev_state_strong)
          |}]
      |}
    ).
    assert(Hreachable_through_s'_mid_mid_end_state : reachable_through s mid_mid_end_state).
    {
      assert(step_s'_mid : ChainStep s mid_state).
      {
        eapply (step_block s mid_state (get_valid_header miner s));eauto.
        unfold get_valid_header.
        eapply build_is_valid_next_block;simpl;intuition;eauto.
        unfold miner_reward.
        lia.
        eapply Forall_forall.
        intros.
        simpl in H0.
        destruct H0.
        rewrite <- H0.
        unfold act_is_from_account.
        simpl.
        eauto.
        inversion H0.
        eapply Forall_forall;eauto.
        intros.
        simpl in H0.
        destruct H0;eauto;intuition.
        rewrite <- H0.
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
        eapply (step_action mid_state mid_mid_end_state (anyone_ClaimTimeout cstate (sender cstate)) [] 
        [{|
          act_origin := sender cstate;
          act_from := caddr;
          act_body :=
            act_transfer (sender prev_state_strong)
              (balance prev_state_strong)
        |}] )
        ;eauto.
        eapply (eval_call (sender cstate) (sender cstate) caddr 0 
          (contract:WeakContract) (Some (serialize ClaimTimeout))
          ( s1) (serialize (freeze_contract prev_state_strong)) 
          [act_transfer (sender prev_state_strong) (balance prev_state_strong)]);eauto;intuition.
        eapply reachable_through_reachable in H0.
        eapply (account_balance_nonnegative mid_state (sender cstate)) in H0.
        lia.
        eauto.
        eapply build_env_equiv;eauto.
      }
      assert(reachable mid_state).
      {
        eapply reachable_through_reachable;eauto.
      }
      eapply reachable_through_step in H1;eauto.
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
    eapply (address_not_contract_not_wc (sender prev_state_strong)) in Hreachable_mid_mid.
    intuition.
    intuition.
    inversion  Hcstate_s_t0.
    rewrite H1 in H_send_or_call_None.
    rewrite H_sender_EOA in H_send_or_call_None.
    inversion H_send_or_call_None;subst.
    simpl in H_exec.
    inversion H_exec;subst.
    inversion Htrans.
    subst.
    inversion Hcs_s'.
    unfold contract_state in H1.
    simpl in H1.
    destruct_address_eq;eauto.
    setoid_rewrite deserialize_serialize in H1.
    inversion H1.
    unfold freeze_contract.
    simpl.
    eauto.
  Qed.

  Local Open Scope nat.

  Lemma wait_to_expiration_state_correct:
    forall (s s':ChainState) cstate,
      contract_state s caddr = Some cstate ->
      frozen cstate = false ->
      (expiration cstate <=? current_slot s)%nat = false ->
      transition_reachable miner contract caddr s0 s ->
      transition miner s (wait_to_expiration (current_slot s) (expiration cstate)) = Ok s' ->
      exists state,
        contract_state s' caddr = Some state /\
        (s'.(current_slot) > state.(expiration))%nat /\
        state = cstate.
  Proof.
    intros * Hcs_s Hfrozen Htime Htrc_s Htrans.
    pose proof Htrc_s.
    eapply transition_reachable_queue_is_empty in Htrc_s as Hqueue_s;eauto.
    assert (Hact_normal : is_normal_wait_act (wait_to_expiration (current_slot s) (expiration cstate)) = true).
    {
      eapply wait_to_expiration_is_normal_wait.
      propify.
      lia.
    }
    assert(ttrace_s_s : TransitionTrace miner s s) by eapply clnil.
    assert(ttrace_s_s' : TransitionTrace miner s s').
    {
      econstructor;eauto.
      eapply step_time;eauto.
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
    assert(H_EOA: address_is_contract (sender cstate) = false /\ address_is_contract (recipient cstate) = false).
    {
      eapply transition_reachable_impl_reachable in Htrc_s.
      eapply sender_and_recipient_is_EOA_forall in Hcs_s;eauto.
      intuition.
      eapply address_not_contract_negb;eauto.
      eapply address_not_contract_negb;eauto.
      eauto.
    }
    destruct H_EOA as [H_sender_EOA H_recipient_EOA].
    assert( H_caddr_not_EOA : address_is_contract caddr = true).
    {
      eapply contract_addr_format in Hec_s.
      eauto.
      eapply transition_reachable_impl_reachable in Htrc_s;eauto.
    }
    eapply deployed_contract_state_typed in Hec_s';eauto.
    destruct Hec_s' as [cstate_s' Hcs_s'].
    exists cstate_s'.
    split.
    eauto.
    unfold transition in Htrans.
    unfold queue_isb_empty in Htrans.
    rewrite Hqueue_s in Htrans.
    rewrite Hact_normal in Htrans.
    destruct (evaluate_action true s
    (get_valid_header_forward_time miner s
       (get_wait_time
          (wait_to_expiration (current_slot s) (expiration cstate)))) []) eqn : H_exec;try congruence.
    unfold evaluate_action in H_exec.
    destruct (validate_header
    (get_valid_header_forward_time miner s
       (get_wait_time
          (wait_to_expiration (current_slot s) (expiration cstate)))) s) ; try congruence.
    simpl in H_exec. 
    inversion H_exec.
    subst.
    inversion Htrans.
    simpl.
    assert (get_wait_time (wait_to_expiration (current_slot s) (expiration cstate)) > 0)%nat.
    {
      eapply is_normal_act_forward_time_gt_zero.
      eauto.
    } 
    unfold get_wait_time.
    unfold get_wait_time in H0.
    destruct (is_normal_wait_act
    (wait_to_expiration (current_slot s) (expiration cstate)));try congruence.
    unfold wait_to_expiration .
    unfold act_amount.
    simpl.
    assert (expiration cstate = expiration cstate_s').
    {

      assert (transition_reachable miner contract caddr s0 s').
      {
        eapply transition_reachable_trans in H.
        eauto.
        eauto.
      }
      eapply transition_reachable_impl_reachable_through in H2 as Htt1;eauto.
      eapply contract_constants_reachable_through in Htt1.
      eapply transition_reachable_impl_reachable_through in H as Htt2;eauto.
      eapply contract_constants_reachable_through in Htt2.
      destruct Htt1 as [cstate1 [Hc1 [_ [_ He1]]]].
      destruct Htt2 as [cstate2 [Hc2 [_ [_ He2]]]].
      rewrite Hcs_s' in Hc1.
      inversion Hc1.
      rewrite <- H4.
      rewrite Hcs_s in Hc2.
      inversion Hc2.
      rewrite <- H5.
      intuition.
    }
    rewrite <- H2.
    propify.
    assert (expiration cstate + 1 - current_slot s > 0) as Hpos by lia.
    unfold safe_Z_to_nat.
    assert (0 <= Z.of_nat (expiration cstate + 1 - current_slot s))%Z by lia.
    assert ((0 <=? Z.of_nat (expiration cstate + 1 - current_slot s))%Z = true).
    {
      propify.
      lia.
    }
    rewrite H4.
    rewrite Nat2Z.id.
    split.
    lia.
    inversion Htrans.
    subst.
    assert (Some cstate_s' = Some cstate).
    {
      rewrite <- Hcs_s'.
      rewrite <- Hcs_s.
      simpl.
      unfold contract_state.
      simpl.
      eauto.
    }
    inversion H1.
    eauto.
  Qed.

  Lemma contract_satisfies_base_liquidity:
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
    rename Hready into Htrc_s.
    eapply transition_reachable_queue_is_empty in Htrc_s as Hqueue_s;eauto.
    assert(Hrct_s0_s : reachable_through s0 s).
    {
      eapply transition_reachable_impl_reachable_through in Htrc_s;eauto.
    }
    assert(Hcs_s :exists cstate, contract_state s caddr = Some cstate).
    {
      eapply reachable_through_contract_deployed in Hrct_s0_s;eauto.
      eapply deployed_contract_state_typed in Hrct_s0_s;eauto.
      eapply transition_reachable_impl_reachable in Htrc_s;eauto.
    }
    
    destruct Hcs_s as [cstate Hcs_s].
    assert(H_EOA: address_is_contract (sender cstate) = false /\ address_is_contract (recipient cstate) = false).
    {
      eapply transition_reachable_impl_reachable in Htrc_s.
      eapply sender_and_recipient_is_EOA_forall in Hcs_s;eauto.
      intuition.
      eapply address_not_contract_negb;eauto.
      eapply address_not_contract_negb;eauto.
      eapply reachable_through_contract_deployed;eauto.
      eauto.
    }
    assert(Hdeployed : env_contracts s caddr = Some (contract: WeakContract)).
    {
      eapply reachable_through_contract_deployed;eauto.
    }

    destruct H_EOA as [H_sender_EOA H_recipient_EOA].
    assert( H_caddr_not_EOA : address_is_contract caddr = true).
    {
      eapply contract_addr_format in Hdeployed;eauto.
    }
    destruct (cstate.(frozen)) eqn : Hfrozen.
    - assert(Hbal:env_account_balances s caddr = cstate.(balance)).
      {
        eapply balance_on_chain_forall;eauto.
        unfold outgoing_acts.
        rewrite Hqueue_s.
        simpl.
        eauto.
      }
      eapply frozen_impl_bal_forall in Hcs_s;eauto.
      rewrite Hcs_s in Hbal.
      exists s.
      econstructor;eauto.
      econstructor;eauto.
      eapply clnil.
    - destruct (cstate.(expiration) <=? s.(current_slot))%nat eqn : Htime_s.
      + pose proof Htime_s.
        eapply anyone_ClaimTimeout_transition_correct in H as Htrans;eauto.
        destruct Htrans as [s' Htrans].
        pose proof Htrans as Hfrozen_s'.
        eapply anyone_ClaimTimeout_state_correct in Hfrozen_s';eauto.
        destruct Hfrozen_s' as [cstate' [Hcs_s' Hfrozen_s']].
        assert (Hact_call : is_call_act (anyone_ClaimTimeout cstate (sender cstate)) = true).
        {
          eapply anyone_ClaimTimeout_is_call_act.
        }
        pose proof Htrc_s as Htrc_st.
        exists s'.
        split.
        assert (inhabited (TransitionTrace miner s s')).
        {
          econstructor;eauto.
          assert (TransitionTrace miner s s) by eapply clnil.
          econstructor;eauto.
          econstructor;eauto.
        }
        eauto.
        assert (inhabited (TransitionTrace miner s s')).
        {
          econstructor;eauto.
          assert (TransitionTrace miner s s) by eapply clnil.
          econstructor;eauto.
          econstructor;eauto.
        }
        eauto.
        destruct H0 as [ttrace_s_s'].
        eapply transition_reachable_transition_transition_reachable in Htrc_s;eauto.
        assert (Hec_s' : env_contracts s' caddr = Some ((contract : WeakContract))).
        {
          pose proof H_init.
          decompose_is_init_state H2.
          eapply reachable_through_contract_deployed in H_env_contracts.
          eauto.
          eapply transition_reachable_impl_reachable_through in Htrc_s.
          eauto.
          eauto.
        }
        assert (transition_reachable miner contract caddr s0 s' ).
        eapply transition_reachable_trans;eauto.
        econstructor;eauto.
        eapply transition_reachable_impl_reachable in H2;eauto.
        pose proof Hcs_s' as Hcs_s'_t.
        eapply frozen_impl_bal_forall in Hcs_s';eauto.
        assert (reachable_via miner contract caddr s0 s s' ).
        {
          econstructor;eauto.
        }
        assert(Hbal:env_account_balances s' caddr = cstate'.(balance)).
        {
          eapply balance_on_chain_forall;eauto.
          unfold outgoing_acts.
          eapply transition_reachable_queue_is_empty in Htrc_s.
          rewrite Htrc_s.
          simpl.
          eauto.
          eauto.
        }
        rewrite Hcs_s' in Hbal.
        intuition.
      + eapply wait_to_expiration_transition_correct in Htime_s as Htrans;eauto.
        destruct Htrans as [s' Htrans].
        eapply wait_to_expiration_state_correct in Htrans as Ht;eauto.
        destruct Ht as [cstate' [Hcs' Htimes']].
        specialize wait_to_expiration_is_normal_wait as Hwait.
        propify.
        specialize (Hwait (current_slot s) (expiration cstate) Htime_s).
        assert (Hstep := step_time miner (wait_to_expiration (current_slot s) (expiration cstate)) 
        Hwait Htrans).
        assert (TransitionTrace miner s s').
        {
          assert (TransitionTrace miner s s).
          eapply clnil.
          eapply (snoc X Hstep).
        }
        assert (Htrc_s' : transition_reachable miner contract caddr s0 s').
        {
        eapply transition_reachable_trans in Htrc_s.
        eauto.
        eauto.
        }
        pose proof Htimes'.
        destruct H as [Htime_s' Heqstate].
        eapply anyone_ClaimTimeout_transition_correct in Hcs' as Htrans'.
        destruct Htrans' as [s'' Htrans''].
        pose proof Htrans'' as Hfrozen_s'.
        eapply anyone_ClaimTimeout_state_correct in Hfrozen_s'.
        destruct Hfrozen_s' as [cstate'' [Hcs_s'' Hfrozen_s'']].
        assert (Hact_call : is_call_act (anyone_ClaimTimeout cstate' (sender cstate')) = true).
        {
          eapply anyone_ClaimTimeout_is_call_act.
        }
        pose proof Htrc_s as Htrc_st.
        exists s''.
        split.
        assert (inhabited (TransitionTrace miner s s'')).
        {
          econstructor;eauto.
          assert (TransitionTrace miner s' s'').
          econstructor;eauto.
          econstructor;eauto.
          econstructor;eauto.
          eapply (clist_app X X0).
        }
        eauto.
        
        eapply transition_reachable_transition_transition_reachable in Htrc_s' as Htrc_s'';eauto.
        assert (Hec_s'' : env_contracts s'' caddr = Some ((contract : WeakContract))).
        {
          pose proof H_init.
          decompose_is_init_state H.
          eapply reachable_through_contract_deployed in H_env_contracts.
          eauto.
          eapply transition_reachable_impl_reachable_through in Htrc_s''.
          eauto.
          eauto.
        }
        pose proof Htrc_s''.
        eapply transition_reachable_impl_reachable in H;eauto.
        pose proof Hcs_s'' as Hcs_s''_t.
        eapply frozen_impl_bal_forall in Hcs_s'';eauto.
        assert (reachable_via miner contract caddr s0 s s'' ).
        {
          econstructor;eauto.
          assert (inhabited (TransitionTrace miner s s'')).
          {
            econstructor;eauto.
            assert (TransitionTrace miner s' s'').
            econstructor;eauto.
            econstructor;eauto.
            econstructor;eauto.
            eapply (clist_app X X0).
          }
          eauto.
        }
        assert(Hbal:env_account_balances s'' caddr = cstate''.(balance)).
        {
          eapply balance_on_chain_forall;eauto.
          unfold outgoing_acts.
          eapply transition_reachable_queue_is_empty in Htrc_s''.
          rewrite Htrc_s''.
          simpl.
          eauto.
          eauto.
        }
        rewrite Hcs_s'' in Hbal.
        intuition.
        eauto.
        intuition.
        propify.
        lia.
        eauto.
        intuition.
        propify.
        lia.
        eauto.
  Qed.

  Lemma recipient_multi_n_zero:
    forall s tr s' tr' n,
      multiStratDrive miner [u_recipient] recipient_strategy s0 s tr s' tr' n ->
      n = 0.
  Proof.
    intros.
    induction H.
    lia.
    unfold stratDrive in H0.
    decompose_exists.
    destruct_and_split.
    unfold recipient_strategy in H0.
    simpl in H0.
    destruct H0.
    pose proof x0.
    rewrite <- H0 in H2.
    specialize (wait_forever_action_instance_is_wait_act).
    intros.
    specialize (H3 miner).
    eapply is_wait_act_true_is_call_act_false in H3.
    congruence.
    inversion H0.
  Qed.

  Lemma contract_satisfies_bounded_liquidity :
      strat_liquidity miner
        [u_sender]
        sender_strategy
        [u_recipient]
        recipient_strategy
        contract
        caddr
        s0.
  Proof.
    unfold strat_liquidity.
    intros.
    rename H into Hwell_sys.
    assert(H_init_t: is_init_state contract caddr s0) by eauto.
    decompose_is_init_state H_init_t.
    assert(Hrct_s0_s : reachable_through s0 s').
    {
      eapply transition_reachable_impl_reachable_through in H_init;eauto.
      econstructor;eauto.
    }
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
      eapply transition_reachable_init_state in Hwell_sys;eauto.
      eapply transition_reachable_interleavedExecution_transition_reachable in Hwell_sys;eauto.
      eapply transition_reachable_queue_is_empty in Hwell_sys;eauto.
    }
    eapply (reachable_through_contract_deployed s0 s' caddr contract) in Hrct_s0_s as Hec_s;eauto.
    pose proof Hec_s.
    eapply deployed_contract_state_typed in H;eauto.
    destruct H as [cstate Hcs].
    rename s' into s.
    rename tr into tr0.
    rename tr' into tr.
    assert(Htc_s : transition_reachable miner contract caddr  s0 s).
    {
      econstructor;eauto.
    }
    (* destruct Hrc_state as [cstate H_cstate]. *)
    assert(H_EOA: address_is_contract (sender cstate) = false /\ address_is_contract (recipient cstate) = false).
    {
      eapply sender_and_recipient_is_EOA_forall in Hrc_s;eauto.
      destruct_and_split.
      eapply address_not_contract_negb;eauto.
      eapply address_not_contract_negb;eauto.
    }
    destruct H_EOA as [H_sender_EOA H_recipient_EOA].
    assert(H_bal : reachable s) by eauto.
    eapply balance_on_chain_forall in H_bal;eauto.
    destruct(cstate.(frozen)) eqn : H_frozen.
    - eapply frozen_impl_bal_forall in H_frozen;eauto.
      eapply ULM_Base.
      unfold funds.
      lia.
    - destruct (cstate.(expiration) <=? s.(current_slot))%nat eqn : Htime_s.
      + pose proof Htime_s.
        eapply anyone_ClaimTimeout_transition_correct in H as Htrans;eauto.
        destruct Htrans as [s' Htrans].
        pose proof Htrans as Hfrozen_s'.
        eapply anyone_ClaimTimeout_state_correct in Hfrozen_s';eauto.
        destruct Hfrozen_s' as [cstate' [Hcs_s' Hfrozen_s']].
        assert (Hact_call : is_call_act (anyone_ClaimTimeout cstate (sender cstate)) = true).
        {
          eapply anyone_ClaimTimeout_is_call_act.
        }
        assert (inhabited (TransitionTrace miner s s')).
        {
          econstructor;eauto.
          assert (TransitionTrace miner s s) by eapply clnil.
          econstructor;eauto.
          econstructor;eauto.
        }
        eauto.
        destruct H1 as [ttrace_s_s'].
        eapply transition_reachable_transition_transition_reachable in Htc_s as Htc_s';eauto.
        assert (Hec_s' : env_contracts s' caddr = Some ((contract : WeakContract))).
        {
          pose proof H_init.
          decompose_is_init_state H1.
          eapply reachable_through_contract_deployed in H_env_contracts.
          eauto.
          eapply transition_reachable_impl_reachable_through in Htc_s'.
          eauto.
          eauto.
        }
        
        eapply transition_reachable_impl_reachable in Htc_s' as Hrc_s';eauto.
        pose proof Hcs_s' as Hcs_s'_t.
        eapply frozen_impl_bal_forall in Hcs_s';eauto.
        assert (reachable_via miner contract caddr s0 s s' ).
        {
          econstructor;eauto.
        }
        assert(Hbal:env_account_balances s' caddr = cstate'.(balance)).
        {
          eapply balance_on_chain_forall;eauto.
          unfold outgoing_acts.
          eapply transition_reachable_queue_is_empty in Htc_s'.
          rewrite Htc_s'.
          simpl.
          eauto.
          eauto.
        }
        rewrite Hcs_s' in Hbal.
        set (tr' := (snoc tr (step_trans miner (anyone_ClaimTimeout cstate (sender cstate)) Hact_call Htrans))).
        assert(Hdrive: (stratDrive miner [u_sender] sender_strategy s0 s tr s' tr' )).
        {
          unfold stratDrive.
          exists 
          (anyone_ClaimTimeout cstate (sender cstate)) ,Hact_call,Htrans .
          split.
          unfold sender_strategy .
          unfold get_contract_state.
          unfold contract_state  in Hcs.
          simpl in Hcs.
          rewrite Hcs.
          rewrite H_frozen.
          rewrite H.
          simpl.
          intuition.
          eauto.
        }
        eapply ULM_Step;eauto.
        eapply EPM_Base;eauto.
      +  eapply wait_to_expiration_transition_correct in Htime_s as Htrans;eauto.
        destruct Htrans as [s' Htrans].
        eapply wait_to_expiration_state_correct in Htrans as Ht;eauto.
        destruct Ht as [cstate' [Hcs' Htimes']].
        specialize wait_to_expiration_is_normal_wait as Hwait.
        propify.
        specialize (Hwait (current_slot s) (expiration cstate) Htime_s).
        assert (Hstep := step_time miner (wait_to_expiration (current_slot s) (expiration cstate)) 
        Hwait Htrans).
        assert (TransitionTrace miner s s').
        {
          assert (TransitionTrace miner s s).
          eapply clnil.
          eapply (snoc X Hstep).
        }
        assert (Htrc_s' : transition_reachable miner contract caddr s0 s').
        {
        eapply transition_reachable_trans in Htc_s.
        eauto.
        eauto.
        }
        pose proof Htimes'.
        destruct H as [Htime_s' Heqstate].
        eapply anyone_ClaimTimeout_transition_correct in Hcs' as Htrans'.
        destruct Htrans' as [s'' Htrans''].
        pose proof Htrans'' as Hfrozen_s'.
        eapply anyone_ClaimTimeout_state_correct in Hfrozen_s'.
        destruct Hfrozen_s' as [cstate'' [Hcs_s'' Hfrozen_s'']].
        assert (Hact_call : is_call_act (anyone_ClaimTimeout cstate' (sender cstate')) = true).
        {
          eapply anyone_ClaimTimeout_is_call_act.
        }
        pose proof Htc_s as Htrc_st.
        
        set (tr' := snoc tr (step_time miner (wait_to_expiration (current_slot s) (expiration cstate)) Hwait  Htrans)).
        set (tr'' := snoc tr' (step_trans miner (anyone_ClaimTimeout cstate' (sender cstate')) Hact_call Htrans'' )).
        assert(Htimedrive: (timeDrive miner s0 s tr (wait_to_expiration (current_slot s) (expiration cstate)) s' tr' )).
        {
          unfold timeDrive.
          exists 
          Hwait ,Htrans .
          eauto.
        }
        assert(Hcalldrive': (stratDrive miner [u_sender] sender_strategy s0 s' tr' s'' tr'' )).
        {
          unfold stratDrive.
          exists 
          (anyone_ClaimTimeout cstate' (sender cstate')) ,Hact_call,Htrans'' .
          split.
          unfold sender_strategy .
          unfold get_contract_state.
          unfold contract_state  in Hcs'.
          simpl in Hcs'.
          rewrite Hcs'.
          rewrite <- Heqstate in H_frozen.
          rewrite H_frozen.
          assert (expiration cstate' <=? current_slot s' = true).
          {
            propify.
            lia.
          }
          rewrite H.
          simpl.
          intuition.
          eauto.
        }
        eapply (ULM_Time miner [u_sender] sender_strategy [u_recipient]
        recipient_strategy caddr s0 s tr s' tr' (wait_to_expiration (current_slot s) (expiration cstate)) (wait_forever_action miner)).
        specialize wait_to_expiration_is_normal_wait as H.
        specialize(H (current_slot s) (expiration cstate) Htime_s).
        eapply normal_wait_action_is_wait_act in H.
        eauto.
        unfold sender_strategy.
        unfold get_contract_state.
        unfold contract_state in Hcs.
        simpl in Hcs.
        rewrite Hcs.
        rewrite H_frozen.
        assert (expiration cstate <=? current_slot s = false).
        {
          propify.
          lia.
        }
        rewrite H.
        simpl.
        intuition.
        eapply wait_forever_action_instance_is_wait_act.
        unfold recipient_strategy.
        simpl.
        eauto.
        assert(is_forever_wait_act (wait_forever_action miner) = true).
        {
          eapply wait_forever_action_is_wait_forever_act.
        }
        specialize (generate_new_wait_act_forever_normal miner(wait_to_expiration (current_slot s) (expiration cstate)) (wait_forever_action miner) Hwait H) as H1.
        rewrite H1.
        eauto.
        assert(is_forever_wait_act (wait_forever_action miner) = true).
        {
          eapply wait_forever_action_is_wait_forever_act.
        }
        specialize (generate_new_wait_act_forever_normal miner(wait_to_expiration (current_slot s) (expiration cstate)) (wait_forever_action miner) Hwait H) as H1.
        rewrite H1.
        eauto.
        eapply (EPM_Turn miner [u_sender] sender_strategy [u_recipient]
        recipient_strategy caddr s0 s' tr' (wait_forever_action miner)).
        eapply wait_forever_action_instance_is_wait_act.
        unfold recipient_strategy.
        simpl.
        eauto.
        eapply ULM_Step.
        eauto.
        eapply EPM_Base.
        eauto.
        eapply transition_reachable_transition_transition_reachable in Htrc_s' as Htrc_s'';eauto.
        assert (Hec_s'' : env_contracts s'' caddr = Some ((contract : WeakContract))).
        {
          pose proof H_init.
          decompose_is_init_state H.
          eapply reachable_through_contract_deployed in H_env_contracts.
          eauto.
          eapply transition_reachable_impl_reachable_through in Htrc_s''.
          eauto.
          eauto.
        }
        pose proof Htrc_s''.
        eapply transition_reachable_impl_reachable in H;eauto.
        pose proof Hcs_s'' as Hcs_s''_t.
        eapply frozen_impl_bal_forall in Hcs_s'';eauto.
        assert (reachable_via miner contract caddr s0 s s'' ).
        {
          econstructor;eauto.
          assert (inhabited (TransitionTrace miner s s'')).
          {
            econstructor;eauto.
            assert (TransitionTrace miner s' s'').
            econstructor;eauto.
            econstructor;eauto.
            econstructor;eauto.
            eapply (clist_app X X0).
          }
          eauto.
        }
        assert(Hbal:env_account_balances s'' caddr = cstate''.(balance)).
        {
          eapply balance_on_chain_forall;eauto.
          unfold outgoing_acts.
          eapply transition_reachable_queue_is_empty in Htrc_s''.
          rewrite Htrc_s''.
          simpl.
          eauto.
          eauto.
        }
        rewrite Hcs_s'' in Hbal.
        intuition.
        eauto.
        intuition.
        propify.
        lia.
        eauto.
        intuition.
        propify.
        lia.
        eauto.
    - unfold outgoing_acts.
      rewrite Hqueue_s.
      simpl.
      eauto.
  Qed.

End PaymentChannel. 
   