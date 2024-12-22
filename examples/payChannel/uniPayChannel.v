(* https://docs.soliditylang.org/en/latest/solidity-by-example.html#id3

  1、部署合约： Alice 使用 Ether 为智能合约提供资金。这“打开”了支付渠道。

  2、签署消息（链下过程）： Alice 签署消息，指定应向收款人支付多少以太币。每次付款都会重复此步骤。

  3、Bob“关闭”了支付渠道，取出了他那部分以太币，并将剩余部分发回给发送者

  3.5、延长渠道生命期：Alice可以选择是否延长渠道时间

  4、渠道到期： 任何人都可以关闭渠道

   问题1：close中的授权金额未验证；
   问题2：extend方法无限可能的延长
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
Require Import Strat.
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
            false                                 (* frozen *)
            msg_sender                            (* sender *)
            setup.(setup_recipient)               (* recipient *)
            (chain.(current_slot) + setup.(setup_duration))%nat(* expiration *)
            msg_value                             (* balance *)
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

  (* 修改前关闭支付通道
     未对amount进行验证。可能导致关闭失败 
  Definition close_channel
             (chain : Chain)
             (ctx : ContractCallContext)
             (state : State)
             (amount : Amount)
             (signature : bytes)
    : result (State * list ActionBody) Error :=
    if (is_not_frozen state)
    then
      if (ctx_from ctx =? state.(recipient))%nat
      then
        if isValidSignature state.(sender) amount signature
        then
          let actions := [act_transfer state.(recipient) amount] in
          let remaining := state.(balance) - amount in
          let new_actions := actions ++ [act_transfer state.(sender) remaining] in
          let new_state := freeze_contract state in
          Ok (new_state, new_actions)
        else
          Err default_error
      else
        Err default_error
    else
      Err default_error.
  *)


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

  (* 
      (* 发送方延长到期时间 *)
    Definition extend (chain : Chain)
                      (ctx : ContractCallContext)
                      (state : State)
                      (new_expiration : nat) : result (State * list ActionBody) Error :=
      if (is_not_frozen state)
      then
        if (ctx_from ctx =? state.(sender))%address && (new_expiration >? state.(expiration))%nat
        then
          let new_state := state <| expiration := new_expiration |> in
          Ok (new_state, [])
        else
          Err default_error (* 错误：调用者不是发送者或新到期时间小于原到期时间 *)
      else
        Err default_error. (* 错误：合约已被冻结 *)
  *)

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


  (* 玩家 B 超时后取回余额
  Definition a_ClaimPrimeB (state : State) (caddr : Address) : Action :=
    build_call state.(player_b) caddr 0 ClaimPrimeB. *)

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
            (caddr : Address) 
            (amount : Amount) 
            (signature : bytes) 
            : Action :=
    build_call state.(recipient) caddr 0 (Close amount signature).

  Definition anyone_ClaimTimeout 
            (state : State) 
            (addr: Address) 
            (caddr : Address) 
            : Action :=
    build_call addr caddr 0 ClaimTimeout.

  Definition sender_no_extend_strategy : (strat miner caddr) :=
    fun s0 s tr addrs =>
      let time := current_slot s in
      match get_contract_state s caddr with
      | Some state =>
          if state.(frozen) then
            []
          else
            if (state.(expiration) <=? time)%nat then
              [anyone_ClaimTimeout state state.(sender) caddr]
            else
              []
      | None => []
      end.

  Definition snes_addrs := [u_sender].
  
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

  (* Ltac reduce_extend :=
    match goal with
    | H : extend ?chain ?ctx ?state ?new_expiration = _ |- _ =>
        unfold extend in H;
        destruct (is_not_frozen state) eqn:EFreeze in H; try discriminate;
        destruct ((ctx_from ctx =? state.(sender))%address && (new_expiration >? state.(expiration))%nat) eqn:EExtend in H; try discriminate
    end. *)

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
      (* + reduce_extend. 
        inversion receive_some; destruct head; cbn in *; lia. *)
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
      (* + reduce_extend.
        inversion receive_some;subst;cbn in *.
        intuition. *)
      + reduce_claim_timeout.
        inversion receive_some;subst;cbn in *.
        lia.
    - reduce_receive_some.
      + reduce_close_channel. 
        inversion receive_some; destruct head; cbn in *; lia.
      (* + reduce_extend.
        inversion receive_some; destruct head; cbn in *; try lia.
        eapply IH.
        unfold is_not_frozen in EFreeze.
        intuition.
        intuition. *)
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
  Qed.

  Lemma contract_constants_transition_via :forall s,
    transition_reachable miner caddr contract caddr s0 s ->
    exists cstate, 
      contract_state s caddr = Some cstate /\
      cstate.(sender) = init_cstate.(sender) /\
      cstate.(recipient) = init_cstate.(recipient) /\
      cstate.(expiration) = init_cstate.(expiration).
  Proof.
    intros.
    assert(ttrace : transition_reachable miner caddr contract caddr s0 s) by eauto.
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

  Lemma anyone_ClaimTimeout_transition_correct:
    forall (s:ChainState) cstate,
      contract_state s caddr = Some cstate ->
      frozen cstate = false ->
      (expiration cstate <=? current_slot s)%nat = true ->
      readyToStepState miner caddr contract caddr s0 s ->
      exists s', transition miner caddr s (anyone_ClaimTimeout cstate (sender cstate) caddr) = Ok s' .
  Proof.
    intros * Hcs_s Hfrozen_cstate Hexpir_s Hready_state_s.
    eexists.
    unfold transition.
    unfold queue_isb_empty.
    pose proof Hready_state_s.
    unfold readyToStepState in H.
    destruct H as [Htrc_s Hqueue_s].
    rewrite Hqueue_s.
    unfold is_terminate_action.
    simpl.
    unfold add_block_exec.
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
      readyToStepState miner caddr contract caddr s0 s ->
      transition miner caddr s (anyone_ClaimTimeout cstate (sender cstate) caddr) = Ok s' ->
      exists state,
        contract_state s' caddr = Some state /\
        state.(frozen) = true.
  Proof.
    intros * Hcs_s Hfrozen Htime Hready Htrans.
    pose proof Hready.
    destruct H as [Htrc_s Hqueue_s].
    assert (Hact_call : is_call_to_caddr_bool caddr (anyone_ClaimTimeout cstate (sender cstate) caddr) = true).
    {
      unfold is_call_to_caddr_bool.
      unfold anyone_ClaimTimeout.
      unfold build_call.
      destruct_address_eq;eauto.
    }
    assert(ttrace_s_s : TransitionTrace miner caddr s s) by eapply clnil.
    assert(ttrace_s_s' : TransitionTrace miner caddr s s').
    {
      econstructor;eauto.
      eapply step_trans;eauto.
    }
    assert(Htrct_s_s' : reachable_via miner caddr contract caddr s0 s s').
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
    destruct (is_wait_action (anyone_ClaimTimeout cstate (sender cstate) caddr)) eqn : Hb_wait.
    unfold is_wait_action in Hb_wait.
    
    intuition.
    rewrite Hact_call in Htrans.
    intuition.
    destruct (add_block_exec true s (get_valid_header miner s) [anyone_ClaimTimeout cstate  (sender cstate) caddr]) eqn : H_exec;try congruence.
    unfold add_block_exec in H_exec.
    destruct (validate_header (get_valid_header miner s) s) ; try congruence.
    destruct (find_origin_neq_from [anyone_ClaimTimeout cstate (sender cstate) caddr]) ;try congruence.
    destruct (find_invalid_root_action
    [anyone_ClaimTimeout cstate  (sender cstate) caddr]) ; try congruence.
    set (mid_state := {|
      chain_state_env := add_new_block_to_env (get_valid_header miner s) s;
      chain_state_queue := [anyone_ClaimTimeout cstate  (sender cstate) caddr]
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
        simpl in H.
        destruct H.
        rewrite <- H.
        unfold act_is_from_account.
        simpl.
        eauto.
        inversion H.
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
        eapply (step_action mid_state mid_mid_end_state (anyone_ClaimTimeout cstate (sender cstate) caddr) [] 
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
        eapply reachable_through_reachable in H.
        eapply (account_balance_nonnegative mid_state (sender cstate)) in H.
        lia.
        eauto.
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
    eapply (address_not_contract_not_wc (sender prev_state_strong)) in Hreachable_mid_mid.
    intuition.
    intuition.
    inversion  Hcstate_s_t0.
    rewrite H0 in H_send_or_call_None.
    rewrite H_sender_EOA in H_send_or_call_None.
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
        simpl in H.
        destruct H.
        rewrite <- H.
        unfold act_is_from_account.
        simpl.
        eauto.
        inversion H.
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
        eapply (step_action mid_state mid_mid_end_state (anyone_ClaimTimeout cstate (sender cstate) caddr) [] 
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
        eapply reachable_through_reachable in H.
        eapply (account_balance_nonnegative mid_state (sender cstate)) in H.
        lia.
        eauto.
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
    eapply (address_not_contract_not_wc (sender prev_state_strong)) in Hreachable_mid_mid.
    intuition.
    intuition.
    inversion  Hcstate_s_t0.
    rewrite H0 in H_send_or_call_None.
    rewrite H_sender_EOA in H_send_or_call_None.
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
    unfold freeze_contract.
    simpl.
    eauto.
  Qed.

  Lemma sender_no_extend_strategy_wellStrat:
    forall s ,
      readyToStepState miner caddr contract caddr s0 s ->
      wellStrat miner caddr sender_no_extend_strategy snes_addrs contract s0.
  Proof.
    intros.
    unfold readyToStepState in H.
    destruct H as [Hrc_s Hqueue].
    unfold wellStrat.
    intros.
    split.
    - intros.
      unfold sender_no_extend_strategy.
      destruct (get_contract_state s1 caddr) as [cstate|] eqn:Hcstate; try discriminate.
      unfold get_contract_state in Hcstate.
      destruct (env_contract_states s1 caddr) eqn:Henv; try discriminate.
      assert (exists cstate' ,contract_state s1 caddr = Some cstate').
      {
        unfold contract_state.
        simpl.
        rewrite Henv.
        exists cstate.
        eauto.
      }
      destruct H0 as [cstate' Hcs_s2].
      assert (cstate' = cstate).
      {
        unfold contract_state in Hcs_s2.
        simpl in Hcs_s2.
        rewrite Henv in Hcs_s2.
        rewrite Hcs_s2 in Hcstate.
        inversion Hcstate.
        eauto.
      }
      subst.
      destruct (cstate.(frozen)) eqn:Hfrozen; try discriminate.
      + eapply Forall_forall.
        intros.
        inversion H0;subst.
      + destruct (cstate.(expiration) <=? current_slot s1)%nat eqn:Hexpir; try discriminate.
        * eapply Forall_forall.
          simpl.
          intros.
          destruct H0;subst.
          unfold is_valid_action.
          destruct ( transition miner caddr s1 (anyone_ClaimTimeout cstate (sender cstate) caddr)) eqn : Htrans; try congruence.
          -- unfold is_call_to_caddr_bool.
             unfold anyone_ClaimTimeout.
             simpl.
             destruct_address_eq; try discriminate;eauto. 
          -- assert (exists s', transition miner caddr s1 (anyone_ClaimTimeout cstate (sender cstate) caddr) = Ok s').
              {
                eapply anyone_ClaimTimeout_transition_correct;eauto.
              }
              destruct H0 as [s' Htrans'].
              congruence.
          -- inversion H0.
        * eapply Forall_forall.
          intros.
          inversion H0;subst.
      + eapply Forall_forall.
        intros.
        inversion H0;subst.
    - intros.
      unfold sender_no_extend_strategy.
      destruct (get_contract_state s1 caddr) as [cstate|] eqn:Hcstate; try discriminate.
      unfold get_contract_state in Hcstate.
      destruct (env_contract_states s1 caddr) eqn:Henv; try discriminate.
      assert (exists cstate' ,contract_state s1 caddr = Some cstate').
      {
        unfold contract_state.
        simpl.
        rewrite Henv.
        exists cstate.
        eauto.
      }
      destruct H as [cstate' Hcs_s2].
      assert (cstate' = cstate).
      {
        unfold contract_state in Hcs_s2.
        simpl in Hcs_s2.
        rewrite Henv in Hcs_s2.
        rewrite Hcs_s2 in Hcstate.
        inversion Hcstate.
        eauto.
      }
      subst.
      destruct (cstate.(frozen)) eqn:Hfrozen; try discriminate.
      + eapply Forall_forall.
        intros.
        inversion H;subst.
      + destruct (cstate.(expiration) <=? current_slot s1)%nat eqn:Hexpir; try discriminate.
        * eapply Forall_forall.
          simpl.
          intros.
          destruct H;subst.
          left.
          unfold get_act_origin.
          unfold act_origin.
          unfold anyone_ClaimTimeout.
          unfold build_call.
          unfold u_sender.
          assert(transition_reachable miner caddr contract caddr s0 s1).
          {
            econstructor;eauto.
          }
          eapply transition_reachable_impl_reachable_through in H;eauto.
          eapply contract_constants_reachable_through in H;eauto.

          destruct H as [cstate'' H].
          destruct_and_split.
          rewrite H in Hcs_s2.
          inversion Hcs_s2.
          subst.
          eauto.
          inversion H.
        * eapply Forall_forall.
          intros.
          inversion H;subst.
      + eapply Forall_forall.
        intros.
        inversion H;subst.
  Qed. 

  Lemma env_contract_states_to_contract_state :forall bstate caddr cstate,
    env_contract_states bstate caddr = Some (serializeState cstate) ->
    contract_state bstate caddr = Some cstate.
  Proof.
    intros.
    unfold contract_state.
    setoid_rewrite H. simpl.
    setoid_rewrite deserialize_serialize.
    reflexivity.
  Qed.

  Definition time_bound := 100%nat.

  Local Open Scope nat.

  Lemma plus_assoc : forall n m p : nat, 
  (m - p) > 0 ->
  n + (m - p) = n + m - p.
  Proof.
    intros n m p H.
    lia.
  Qed.




  (* 是否可达？ *)
  Definition Expiration :=
    fun s =>
      transition_reachable miner caddr contract caddr s0 s /\
      exists cstate,
        contract_state s caddr = Some cstate /\
        (s.(current_slot) >= cstate.(expiration))%nat. 


  Lemma interleavedExecution_implies_Expiration_with_SNES:
    forall delta_env addrs_env tr,
      ~ incl snes_addrs addrs_env ->
      wellDefinedSystem miner caddr sender_no_extend_strategy [u_sender] delta_env
      addrs_env caddr contract s0 ->
      exists s' tr',
        isReachableUnderInterleavedExecution miner caddr sender_no_extend_strategy delta_env snes_addrs addrs_env s0 tr s' tr' /\ Expiration s'.
  Proof.
    intros.
    pose proof H0 as Hwell_sys.
    unfold wellDefinedSystem in H0.
    clear H_init.
    destruct H0 as [Hwell_usr [Hwell_env [Hfinite_env H_init]]].
    unfold Expiration.
    assert(H_init_t: is_init_state contract caddr s0) by eauto.
    decompose_is_init_state H_init_t.
    assert(Htrc_s0 : transition_reachable miner caddr contract caddr s0 s0).
    {
      econstructor;eauto.
    }
    assert(Hcs_s0 : exists (cstate : State),
                      contract_state s0 caddr = Some cstate).
    {
      eapply transition_reachable_impl_reachable in Htrc_s0;eauto.
    }
    assert(tr0 : TransitionTrace miner caddr s0 s0) by eapply clnil.
    destruct Hcs_s0 as [cstate Hcs_s0].
    assert (Heq_state : state = cstate).
    {
      unfold contract_state in Hcs_s0.
      simpl in Hcs_s0.
      rewrite H_env_states in Hcs_s0.
      rewrite deserialize_serialize in Hcs_s0.
      intuition.
    }
    pose proof H_miner as H_miner'.
    eapply address_not_contract_negb in H_miner'.
    eapply (forward_time_interleavedExecution miner H_miner' caddr (cstate.(expiration)-current_slot s0)  contract s0 s0 tr ) in Hwell_sys;eauto.
    destruct Hwell_sys as [s' [tr'[flag [Hile_s'  Hexpir]]]].
    destruct flag eqn : Hflag.
    + exists s'.
      exists tr'.
      split.
      unfold isReachableUnderInterleavedExecution.
      unfold snes_addrs.
      eauto.
      assert (init_cstate = cstate).
      {
        unfold get_contract_state in H_state.
        destruct (env_contract_states s0 caddr) eqn : H_ecst; try congruence.
        unfold contract_state in Hcs_s0.
        simpl in Hcs_s0.
        rewrite H_ecst in Hcs_s0.
        rewrite H_state in Hcs_s0.
        inversion Hcs_s0.
        eauto.
      }
      simpl in H_init0.
      reduce_init.
      assert (current_slot s0 + (expiration cstate - current_slot s0) = expiration cstate)%nat.
      {
        simpl.
        assert (current_slot s0 + (expiration cstate - current_slot s0) = current_slot s0 + expiration cstate - current_slot s0)%nat.
        {
          assert ((expiration cstate - current_slot s0) > 0).
          {
            propify.
            rewrite <- Heq_state.
            rewrite <- H_init0.
            simpl.
            lia.
          }
          eapply plus_assoc;eauto.
        }
        lia.  
      }
      clear Heq_state.
      assert(Hexpir' : current_slot s' >= current_slot s0).
      {
        rewrite H1 in Hexpir.
        eapply ttrace_time_gt.
        eauto.
      }
      split.
      econstructor;eauto.
      assert (exists cstate , contract_state s' caddr = Some cstate).
      {
        assert (transition_reachable miner caddr contract caddr s0 s').
        {
          econstructor;eauto.
        }
        pose proof H2 as H2'.
        eapply transition_reachable_impl_reachable_through in H2;eauto.
        eapply reachable_through_contract_deployed in H2;eauto.
        eapply deployed_contract_state_typed in H2;eauto.
        eapply transition_reachable_impl_reachable in H2';eauto.
      }
      destruct H2 as [cstate' Hcs_s'].
      exists cstate'.
      split.
      eauto.
      assert (transition_reachable miner caddr contract caddr s0 s').
      {
        econstructor;eauto.
      }
      eapply transition_reachable_impl_reachable_through in H2;eauto.
      eapply contract_constants_reachable_through in H2;eauto.
      destruct_and_split.
      rewrite H2 in Hcs_s'.
      inversion Hcs_s'.
      subst.
      lia.
    + destruct (delta_env s0 s' tr' addrs_env) eqn : Hdelta_env.
      * eapply ISE_Turn_Step in Hile_s';eauto.
        simpl in H_init0.
        reduce_init.
        assert (current_slot s0 + (expiration cstate - current_slot s0) = expiration cstate)%nat.
        {
          simpl.
          assert (current_slot s0 + (expiration cstate - current_slot s0) = current_slot s0 + expiration cstate - current_slot s0)%nat.
          {
            assert ((expiration cstate - current_slot s0) > 0).
            {
              propify.
              rewrite <- Heq_state.
              rewrite <- H_init0.
              simpl.
              lia.
            }
            eapply plus_assoc;eauto.
          }
          lia.  
        }
        clear Heq_state.
        rewrite H0 in Hexpir.

        exists s' , tr'.
        split.
        eauto.
        split.
        econstructor;eauto.
        assert (exists cstate , contract_state s' caddr = Some cstate).
        {
          assert (transition_reachable miner caddr contract caddr s0 s').
          {
            econstructor;eauto.
          }
          rename H1 into H2.
          pose proof H2 as H2'.
          eapply transition_reachable_impl_reachable_through in H2;eauto.
          eapply reachable_through_contract_deployed in H2;eauto.
          eapply deployed_contract_state_typed in H2;eauto.
          eapply transition_reachable_impl_reachable in H2';eauto.
        }
        destruct H1 as [cstate' Hcs_s'].
        exists cstate'.
        split.
        eauto.
        assert (transition_reachable miner caddr contract caddr s0 s').
        {
          econstructor;eauto.
        }
        eapply transition_reachable_impl_reachable_through in H1;eauto.
        eapply contract_constants_reachable_through in H1;eauto.
        destruct_and_split.
        rewrite H1 in Hcs_s'.
        inversion Hcs_s'.
        assert (init_cstate = cstate).
        {
          unfold get_contract_state in H_state.
          destruct (env_contract_states s0 caddr) eqn : H_ecst; try congruence.
          unfold contract_state in Hcs_s0.
          simpl in Hcs_s0.
          rewrite H_ecst in Hcs_s0.
          rewrite H_state in Hcs_s0.
          inversion Hcs_s0.
          eauto.
        }
        subst.
        lia.
      *  assert(Hmulti : exists s'' tr'', multiStratDrive miner caddr delta_env addrs_env s0 s' tr' s'' tr'' 1).
        {
          assert(exists s'' tr'',stratDrive miner caddr s0 delta_env addrs_env s' tr' s'' tr'').
          {
            assert(is_valid_action miner caddr s' a = true).
            {
              assert (readyToStepState miner caddr contract caddr s0 s').
              {
                eapply transition_reachable_readyToStepState;eauto.
                econstructor;eauto.
              }
              unfold wellStrat in Hwell_env.
              specialize (Hwell_env s' tr').
              destruct Hwell_env as [H5 _].
              eapply H5 in H0.
              rewrite Hdelta_env in H0.
              assert (is_valid_action miner caddr s' a = true).
              inversion H0.
              eauto.
              eauto.
            }
            unfold is_valid_action in H0.
            destruct (transition miner caddr s' a) eqn:Htrans;try congruence.
            unfold stratDrive.
            set (tr'' := snoc tr' (step_trans miner caddr a H0 Htrans)).
            exists t, tr'', a,H0,Htrans.
            split.
            eapply call_act_not_wait_act;eauto.
            split.
            rewrite Hdelta_env.
            intuition.
            eauto.
          }
          destruct H0 as [s'' [tr'' Hstrat_refines]].
          exists s'', tr''.
          assert (multiStratDrive miner caddr delta_env addrs_env s0 s' tr' s' tr' 0).
          {
            eapply MS_Refl;eauto.
          }
          eapply MS_Step in H0;eauto.
        }
        destruct Hmulti as [s'' [tr'' Hmulti]].
        exists s'', tr''.
        split.
        eapply ISE_Step;eauto.
        rewrite Hdelta_env.
        intuition.
        assert(Hstime: current_slot s'' - current_slot s' >= 1).
        {
          eapply (multiStratDrive_time_n miner caddr s0 s' s'' tr' tr'' delta_env addrs_env 1);eauto.
        }
        
        econstructor;eauto.
        econstructor;eauto.
        assert (exists cstate , contract_state s'' caddr = Some cstate).
        {
          assert (transition_reachable miner caddr contract caddr s0 s'').
          {
            econstructor;eauto.
          }
          rename H0 into H2.
          pose proof H2 as H2'.
          eapply transition_reachable_impl_reachable_through in H2;eauto.
          eapply reachable_through_contract_deployed in H2;eauto.
          eapply deployed_contract_state_typed in H2;eauto.
          eapply transition_reachable_impl_reachable in H2';eauto.
        }
        
        rename H0 into H1.
        destruct H1 as [cstate' Hcs_s'].
        exists cstate'.
        split.
        eauto.
        assert (transition_reachable miner caddr contract caddr s0 s'').
        {
          econstructor;eauto.
        }
        eapply transition_reachable_impl_reachable_through in H0;eauto.
        eapply contract_constants_reachable_through in H0;eauto.
        destruct_and_split.
        rewrite H0 in Hcs_s'.
        inversion Hcs_s'.
        assert (init_cstate = cstate).
        {
          unfold get_contract_state in H_state.
          destruct (env_contract_states s0 caddr) eqn : H_ecst; try congruence.
          unfold contract_state in Hcs_s0.
          simpl in Hcs_s0.
          rewrite H_ecst in Hcs_s0.
          rewrite H_state in Hcs_s0.
          inversion Hcs_s0.
          eauto.
        }
        subst.
        lia.
        Unshelve.
  Qed.

  Lemma contract_satisfies_bounded_liquidity :
    forall (delta_env : strat miner caddr) (addrs_env : list Address),
      ~ incl snes_addrs addrs_env ->
      wellDefinedSystem miner caddr sender_no_extend_strategy snes_addrs delta_env addrs_env caddr contract s0 ->
      bounded_strat_liquidity miner caddr
        sender_no_extend_strategy
        snes_addrs
        delta_env
        addrs_env
        caddr
        contract
        Expiration
        s0
        100.
  Proof.
    unfold bounded_strat_liquidity. 
    unfold time_bound in *.
    intros.
    clear H0.
    rename H1 into Hwell_sys.
    rename H2 into Hirc_s'.
    rename H3 into P.
    unfold Expiration in P.
    destruct P as [Htrc_s' [cstate [Hcs_s' Hexpir]]].
    assert(H_init_t: is_init_state contract caddr s0) by eauto.
    decompose_is_init_state H_init_t.
    assert(Hrct_s0_s' : reachable_through s0 s').
    {
      unfold isReachableUnderInterleavedExecution in Hirc_s'.
      eapply transition_reachable_impl_reachable_through in H_init;eauto.
      (* econstructor;eauto.     *)
    }
    assert( H_caddr_not_EOA : address_is_contract caddr = true).
    {
      eapply contract_addr_format in H_reachable;eauto.  
    }
    eapply (reachable_through_contract_deployed s0 s' caddr contract) in Hrct_s0_s' as Hec_s';eauto.
    assert(Hrc_s' : reachable s').
    {
      assert(transition_reachable miner caddr contract caddr  s0 s').
      {
        econstructor;eauto.
      }
      eapply transition_reachable_impl_reachable in H0;eauto.
    }
    assert(Hqueue_s':chain_state_queue s' = []).
    {
      unfold isReachableUnderInterleavedExecution in Hirc_s'.
      eapply init_ready in H_init.
      eapply readyToStepState_interleavedExecution_readyToStepState in H_init;eauto.
      unfold readyToStepState in H_init.
      intuition.
    }

    (* destruct Hrc_state as [cstate H_cstate]. *)
    assert(H_EOA: address_is_contract (sender cstate) = false /\ address_is_contract (recipient cstate) = false).
    {
      eapply sender_and_recipient_is_EOA_forall in Hrc_s';eauto.
      destruct_and_split.
      eapply address_not_contract_negb;eauto.
      eapply address_not_contract_negb;eauto.
    }
    destruct H_EOA as [H_sender_EOA H_recipient_EOA].
    assert(H_bal : reachable s') by eauto.
    eapply balance_on_chain_forall in H_bal;eauto.
    destruct(cstate.(frozen)) eqn : H_frozen.
    - eapply frozen_impl_bal_forall in H_frozen;eauto.
      exists 1%nat.
      exists s'.
      exists tr'.

      split.
      unfold time_bound.
      lia.

      eapply ULM_Base.
      unfold funds.
      lia.
    - destruct (cstate.(expiration) <=? s'.(current_slot))%nat eqn : Htime_s'.
      + exists 2%nat.
        assert(Hdrive: exists s'' tr'' , (stratDrive miner caddr s0 sender_no_extend_strategy [u_sender] s' tr' s'' tr'' )).
        {
          assert(exists s'', transition miner caddr s' (anyone_ClaimTimeout cstate (sender cstate) caddr) = Ok s'').
          {
            assert(sender init_cstate = sender cstate).
            {
              eapply contract_constants_reachable_through in Hrct_s0_s'.
              destruct Hrct_s0_s'.
              destruct_and_split.
              rewrite H0 in Hcs_s'.
              inversion Hcs_s'.
              eauto.
              subst.
              eauto.
            }
            clear H_init0.
            clear H_env_states.
            
            eapply anyone_ClaimTimeout_transition_correct;eauto.
            econstructor;eauto.
          }
          rename H0 into H2.
          destruct H2.
          exists x.
          rename x into s''.
          assert (is_call_to_caddr_bool caddr (anyone_ClaimTimeout cstate (sender cstate) caddr) = true).
          {
            unfold is_call_to_caddr_bool.
            unfold anyone_ClaimTimeout.
            unfold build_call.
            destruct_address_eq;eauto.
          }
          set(tr'' := snoc tr' (step_trans miner caddr (anyone_ClaimTimeout cstate (sender cstate) caddr) H1 H0)).
          exists tr''.
          unfold stratDrive.
          exists (anyone_ClaimTimeout cstate (sender cstate) caddr).
          exists H1 , H0.
          split.
          eapply call_act_not_wait_act;eauto.
          unfold u_sender.
          intuition.
          assert(sender init_cstate = sender cstate).
          {
            
            eapply contract_constants_reachable_through in Hrct_s0_s'.

            destruct Hrct_s0_s'.
            destruct_and_split.
            rewrite H2 in Hcs_s'.
            inversion Hcs_s'.
            subst.
            eauto.
          }
          rewrite H2.
          unfold sender_no_extend_strategy.
          unfold get_contract_state.
          unfold contract_state in Hcs_s'.
          simpl in Hcs_s'.
          destruct (env_contract_states s' caddr) ;try congruence.
          rewrite Hcs_s'.
          rewrite H_frozen.
          rewrite Htime_s'.
          intuition.
        }

        assert(exists s'', transition miner caddr s' (anyone_ClaimTimeout cstate (sender cstate) caddr) = Ok s'').
        {
          assert(sender init_cstate = sender cstate).
          {
            eapply contract_constants_reachable_through in Hrct_s0_s'.
            destruct Hrct_s0_s'.
            destruct_and_split.
            rewrite H0 in Hcs_s'.
            inversion Hcs_s'.
            eauto.
            subst.
            eauto.
          }
          clear H_init0.
          clear H_env_states.
          
          eapply anyone_ClaimTimeout_transition_correct;eauto.
          econstructor;eauto.
        }

        destruct H0 as [s'' Htrans].
        assert(Hcstate_frozen: exists cstate, contract_state s'' caddr = Some cstate /\ cstate.(frozen) = true).
        {
          assert(ttrace_s'_s' : TransitionTrace miner caddr s' s') by eapply clnil.
          assert(ttrace_s'_s'' : TransitionTrace miner caddr s' s'').
          {
            econstructor;eauto.
            eapply step_trans;eauto.
            unfold is_call_to_caddr_bool.
            unfold anyone_ClaimTimeout.
            simpl.
            destruct_address_eq;eauto.
          }
          assert(H_t: reachable s') by eauto.
          destruct H_t as [trace].
          assert(Hreachable_s_s'' : reachable_through s' s'').
          {
            eapply ttrace_with_trace in ttrace_s'_s'';eauto.
            econstructor;eauto.
          }
          assert(Hcstate_s' : contract_state s' caddr = Some cstate) by eauto.
          unfold contract_state in Hcs_s'.
          simpl in Hcs_s'.
          destruct (env_contract_states s' caddr) eqn : Hcstate ;try congruence.
          eapply reachable_through_contract_state in Hcstate;eauto.
          destruct Hcstate as [ser_cstate Hecs_s''].

          assert(Hec_s'' : env_contracts s'' caddr = Some (contract : WeakContract)).
          {
            eapply reachable_through_contract_deployed in Hreachable_s_s'';eauto.
          }
          eapply deployed_contract_state_typed in Hec_s'';eauto.
          destruct Hec_s'' as [cstate_s'' Hcs_s''].
          exists cstate_s''.
          split.
          eauto.
          rename cstate_s'' into cstate_s''.
          unfold transition in Htrans.
          unfold queue_isb_empty in Htrans.
          rewrite Hqueue_s' in Htrans.
          destruct (is_terminate_action (anyone_ClaimTimeout cstate (sender cstate) caddr)) eqn : Hb_termin;try congruence.
          unfold is_terminate_action in Hb_termin.
          intuition.
          destruct (is_wait_action (anyone_ClaimTimeout cstate (sender cstate) caddr)) eqn : Hb_wait.
          unfold is_wait_action in Hb_wait.
          intuition.
          destruct (add_block_exec true s' (get_valid_header miner s') [anyone_ClaimTimeout cstate  (sender cstate) caddr]) eqn : H_exec;try congruence.
          unfold add_block_exec in H_exec.
          destruct (validate_header (get_valid_header miner s') s') ; try congruence.
          destruct (find_origin_neq_from [anyone_ClaimTimeout cstate (sender cstate) caddr]) ;try congruence.
          destruct (find_invalid_root_action
          [anyone_ClaimTimeout cstate  (sender cstate) caddr]) ; try congruence.
          set (mid_state := {|
            chain_state_env := add_new_block_to_env (get_valid_header miner s') s';
            chain_state_queue := [anyone_ClaimTimeout cstate  (sender cstate) caddr]
          |}) in H_exec.
          simpl in *.
          destruct(send_or_call (sender cstate) (sender cstate) caddr 0
          (Some (serialize ClaimTimeout))
          (add_new_block_to_env (get_valid_header miner s') s')) eqn : H_send_or_call_ClaimTimeout;try congruence.
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
          destruct(0 >? miner_reward + env_account_balances s' (sender cstate))%Z;try congruence.
          rewrite Hec_s' in H_send_or_call_ClaimTimeout.
          assert(Hcstate_s'_t0:contract_state s' caddr = Some cstate) by eauto.
          unfold contract_state in Hcstate_s'_t0.
          simpl in Hcstate_s'_t0.
          destruct (env_contract_states s' caddr) eqn : Hcstate_s'_t0';try congruence.
          destruct (weak_error_to_error_receive
          (wc_receive contract
              (s' <| chain_height := S (chain_height s') |> <|
              current_slot := (current_slot s' + 1)%nat |> <|
              finalized_height := finalized_height s' |>)
              {|
                ctx_origin := sender cstate;
                ctx_from := sender cstate;
                ctx_contract_address := caddr;
                ctx_contract_balance := 0 + env_account_balances s' caddr;
                ctx_amount := 0
              |} s1 (Some (serialize ClaimTimeout)))) eqn : H_wc_receive_s1;try congruence.
          unfold weak_error_to_error_receive in H_wc_receive_s1.
          unfold bind_error in H_wc_receive_s1.
          destruct (wc_receive contract
          (s' <| chain_height := S (chain_height s') |> <| current_slot :=
           (current_slot s' + 1)%nat |> <| finalized_height :=
           finalized_height s' |>)
          {|
            ctx_origin := sender cstate;
            ctx_from := sender cstate;
            ctx_contract_address := caddr;
            ctx_contract_balance := 0 + env_account_balances s' caddr;
            ctx_amount := 0
          |} s1 (Some (serialize ClaimTimeout)))
           eqn : H_wc_receive_s1';try congruence.
          
          set (cchain := s' <| chain_height := S (chain_height s') |> <| current_slot :=
          (current_slot s' + 1)%nat |> <| finalized_height :=
          finalized_height s' |>) in H_wc_receive_s1'.
          set (cctx := {|
          ctx_origin := sender cstate;
          ctx_from := sender cstate;
          ctx_contract_address := caddr;
          ctx_contract_balance := 0 + env_account_balances s' caddr;
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
          rewrite deser_state in Hcstate_s'_t0.
          simpl in receive.
          rename receive into receive_some.
          unfold receive in receive_some.
          destruct ((ctx_amount cctx =? 0)%Z &&
          address_not_contract (ctx_from cctx)) eqn : requirements_check;try congruence.
          reduce_claim_timeout.
          inversion receive_some ;subst.
          inversion H_wc_receive_s1;subst.
          inversion H_send_or_call_ClaimTimeout;subst.
          simpl in H_exec.
          destruct (  send_or_call (sender cstate) caddr (sender prev_state_strong)
          (balance prev_state_strong) None
          (set_contract_state caddr
             (serialize (freeze_contract prev_state_strong))
             (transfer_balance (sender cstate) caddr 0
                (add_new_block_to_env (get_valid_header miner s') s')))) eqn : H_send_or_call_None;try congruence.
          unfold send_or_call in H_send_or_call_None.
          destruct_match in H_send_or_call_None;try congruence.
          destruct_match in H_send_or_call_None;try congruence.
          destruct (
              env_contracts
              (set_contract_state caddr
                (serialize (freeze_contract prev_state_strong))
                (transfer_balance (sender cstate) caddr 0
                    (add_new_block_to_env (get_valid_header miner s') s')))
              (sender prev_state_strong) ) 
          eqn : H_none_wc.
          set (
              mid_env:=(set_contract_state caddr
                (serialize (freeze_contract prev_state_strong))
                (transfer_balance (sender cstate) caddr 0
                    (add_new_block_to_env (get_valid_header miner s') s')))) 
          in H_none_wc.
          set (
            mid_mid_end_state := {|
            chain_state_env :=
              set_contract_state caddr
                (serialize (freeze_contract prev_state_strong))
                (transfer_balance (sender cstate) caddr 0
                   (add_new_block_to_env
                      (get_valid_header miner s') s'));
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
          assert(Hreachable_through_s'_mid_mid_end_state : reachable_through s' mid_mid_end_state).
          {
            assert(step_s'_mid : ChainStep s' mid_state).
            {
              eapply (step_block s' mid_state  (get_valid_header miner s'));eauto.
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
            assert(reachable_through s' mid_state).
            {
              assert(tt:ChainTrace s' s') by eapply clnil.
              assert(tt' : ChainTrace s' mid_state).
              {
                eapply snoc;eauto.
              }
              econstructor;eauto.
            }
            assert(step_mid_end : ChainStep mid_state mid_mid_end_state).
            {
              eapply (step_action mid_state mid_mid_end_state (anyone_ClaimTimeout state (sender cstate) caddr) [] 
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
          inversion  Hcstate_s'_t0.
          rewrite H1 in H_send_or_call_None.
          rewrite H_sender_EOA in H_send_or_call_None.
          inversion H_send_or_call_None;subst.
          simpl in H_exec.
          inversion H_exec;subst.
          inversion Htrans.
          subst.
          inversion Hcs_s''.
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
          destruct(0 >? env_account_balances s' (sender cstate))%Z;try congruence.
          rewrite Hec_s' in H_send_or_call_ClaimTimeout.
          assert(Hcstate_s'_t0:contract_state s' caddr = Some cstate) by eauto.
          unfold contract_state in Hcstate_s'_t0.
          simpl in Hcstate_s'_t0.
          destruct (env_contract_states s' caddr) eqn : Hcstate_s'_t0';try congruence.
          destruct (weak_error_to_error_receive
          (wc_receive contract
              (s' <| chain_height := S (chain_height s') |> <|
              current_slot := (current_slot s' + 1)%nat |> <|
              finalized_height := finalized_height s' |>)
              {|
                ctx_origin := sender cstate;
                ctx_from := sender cstate;
                ctx_contract_address := caddr;
                ctx_contract_balance := 0 + env_account_balances s' caddr;
                ctx_amount := 0
              |} s1 (Some (serialize ClaimTimeout)))) eqn : H_wc_receive_s1;try congruence.
          unfold weak_error_to_error_receive in H_wc_receive_s1.
          unfold bind_error in H_wc_receive_s1.
          destruct (wc_receive contract
          (s' <| chain_height := S (chain_height s') |> <| current_slot :=
           (current_slot s' + 1)%nat |> <| finalized_height :=
           finalized_height s' |>)
          {|
            ctx_origin := sender cstate;
            ctx_from := sender cstate;
            ctx_contract_address := caddr;
            ctx_contract_balance := 0 + env_account_balances s' caddr;
            ctx_amount := 0
          |} s1 (Some (serialize ClaimTimeout)))
           eqn : H_wc_receive_s1';try congruence.
          
          set (cchain := s' <| chain_height := S (chain_height s') |> <| current_slot :=
          (current_slot s' + 1)%nat |> <| finalized_height :=
          finalized_height s' |>) in H_wc_receive_s1'.
          set (cctx := {|
          ctx_origin := sender cstate;
          ctx_from := sender cstate;
          ctx_contract_address := caddr;
          ctx_contract_balance := 0 + env_account_balances s' caddr;
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
          rewrite deser_state in Hcstate_s'_t0.
          simpl in receive.
          rename receive into receive_some.
          unfold receive in receive_some.
          destruct ((ctx_amount cctx =? 0)%Z &&
          address_not_contract (ctx_from cctx)) eqn : requirements_check;try congruence.
          reduce_claim_timeout.
          inversion receive_some ;subst.
          inversion H_wc_receive_s1;subst.
          inversion H_send_or_call_ClaimTimeout;subst.
          simpl in H_exec.
          destruct (  send_or_call (sender cstate) caddr (sender prev_state_strong)
          (balance prev_state_strong) None
          (set_contract_state caddr
             (serialize (freeze_contract prev_state_strong))
             (transfer_balance (sender cstate) caddr 0
                (add_new_block_to_env (get_valid_header miner s') s')))) eqn : H_send_or_call_None;try congruence.
          unfold send_or_call in H_send_or_call_None.
          destruct_match in H_send_or_call_None;try congruence.
          destruct_match in H_send_or_call_None;try congruence.
          destruct (
              env_contracts
              (set_contract_state caddr
                (serialize (freeze_contract prev_state_strong))
                (transfer_balance (sender cstate) caddr 0
                    (add_new_block_to_env (get_valid_header miner s') s')))
              (sender prev_state_strong) ) 
          eqn : H_none_wc.
          set (
              mid_env:=(set_contract_state caddr
                (serialize (freeze_contract prev_state_strong))
                (transfer_balance (sender cstate) caddr 0
                    (add_new_block_to_env (get_valid_header miner s') s')))) 
          in H_none_wc.
          set (
            mid_mid_end_state := {|
            chain_state_env :=
              set_contract_state caddr
                (serialize (freeze_contract prev_state_strong))
                (transfer_balance (sender cstate) caddr 0
                   (add_new_block_to_env
                      (get_valid_header miner s') s'));
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
          assert(Hreachable_through_s'_mid_mid_end_state : reachable_through s' mid_mid_end_state).
          {
            assert(step_s'_mid : ChainStep s' mid_state).
            {
              eapply (step_block s' mid_state  (get_valid_header miner s'));eauto.
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
            assert(reachable_through s' mid_state).
            {
              assert(tt:ChainTrace s' s') by eapply clnil.
              assert(tt' : ChainTrace s' mid_state).
              {
                eapply snoc;eauto.
              }
              econstructor;eauto.
            }
            assert(step_mid_end : ChainStep mid_state mid_mid_end_state).
            {
              eapply (step_action mid_state mid_mid_end_state (anyone_ClaimTimeout state (sender cstate) caddr) [] 
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
          simpl in H_send_or_call_None.
          inversion  Hcstate_s'_t0.
          rewrite H1 in H_send_or_call_None.
          rewrite H_sender_EOA in H_send_or_call_None.
          inversion H_send_or_call_None;subst.
          simpl in H_exec.
          inversion H_exec;subst.
          inversion Htrans.
          subst.
          inversion Hcs_s''.
          unfold contract_state in H1.
          simpl in H1.
          destruct_address_eq;try congruence.
          setoid_rewrite deserialize_serialize in H1.
          inversion H1.
          unfold freeze_contract.
          simpl.
          eauto.
          unfold is_call_to_caddr_bool in Htrans.
          simpl in Htrans.
          destruct_address_eq;try congruence.
        }
        destruct Hcstate_frozen as [state_s'' [Hsc_s'' Hcstate_frozen]].
        exists s''.
        set(a := (anyone_ClaimTimeout cstate (sender cstate) caddr)) in Htrans.
        assert(step_s'_s'' :TransitionStep miner caddr s' s'').
        {
          eapply step_trans;eauto.
          unfold is_call_to_caddr_bool.
          simpl.
          destruct_address_eq;eauto.
        }
        assert (is_call_to_caddr_bool caddr a = true).
        {
          unfold is_call_to_caddr_bool.
          simpl.
          destruct_address_eq;eauto.
        }
        set (ttrace_s'_s'' := snoc tr' (step_trans miner caddr a H0 Htrans)) .
        exists ttrace_s'_s''.
        split.
        lia.
        eapply ULM_Step;eauto.
        unfold stratDrive.
        exists a , H0,Htrans.
        split.
        eapply call_act_not_wait_act;eauto.
        unfold sender_no_extend_strategy.
        unfold get_contract_state.
        unfold contract_state in Hcs_s'.
        simpl in Hcs_s'.
        destruct (env_contract_states s' caddr) ;try congruence.
        rewrite Hcs_s'.
        rewrite H_frozen.
        rewrite Htime_s'.
        intuition.
        eauto.
        eapply EPM_Base.
        assert(ttrace_s0_s'' : TransitionTrace miner caddr s0 s'').
        {
          eapply (snoc tr' step_s'_s'').
        }
        assert(transition_reachable miner caddr contract caddr s0 s'').
        {
          econstructor;eauto.
        }
        assert(reachable s'').
        {
          eapply transition_reachable_impl_reachable in H1;eauto.
        }
        assert(readyToStepState miner caddr contract caddr s0 s'').
        {
          assert (transition miner caddr s' a = Ok s'') by eauto.
          eapply (readyToStepState_transition_readyToStepState miner caddr s0 s' s'' a contract) in H3;eauto.
          unfold readyToStepState.
          split.
          econstructor;eauto.
          eauto.
        }
        unfold readyToStepState in H3.
        destruct_and_split.
        assert(reachable_through s0 s'').
        {
          econstructor;eauto.
          assert(reachable s0) by eauto.
          destruct H6 as [trace].
          eapply ttrace_with_trace in ttrace_s0_s'';eauto.
        }
        eapply balance_on_chain_forall in H2;eauto.
        eapply frozen_impl_bal_forall in Hsc_s'';eauto.
        unfold funds.
        lia.
        eapply reachable_through_contract_deployed in H6;eauto.
        eapply reachable_through_contract_deployed in H6;eauto.
        unfold outgoing_acts.
        rewrite H4.
        simpl.
        eauto.
      + propify.
        lia.
    - unfold outgoing_acts.
      rewrite Hqueue_s'.
      intuition.
  Qed.

  Lemma contract_satisfies_base_liquidity:
    base_liquidity miner caddr contract caddr s0.
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
        assert (Hact_call : is_call_to_caddr_bool caddr (anyone_ClaimTimeout cstate (sender cstate) caddr) = true).
        {
          unfold is_call_to_caddr_bool.
          unfold anyone_ClaimTimeout.
          unfold build_call.
          destruct_address_eq;eauto.
        }
        exists s'.
        
        split.
        assert (inhabited (TransitionTrace miner caddr s s')).
        {
          econstructor;eauto.
          assert (TransitionTrace miner caddr s s) by eapply clnil.
          econstructor;eauto.
          econstructor;eauto.
        }
        eauto.
        assert (inhabited (TransitionTrace miner caddr s s')).
        {
          econstructor;eauto.
          assert (TransitionTrace miner caddr s s) by eapply clnil.
          econstructor;eauto.
          econstructor;eauto.
        }
        eauto.
        destruct H0 as [ttrace_s_s'].
        eapply readyToStepState_transition_readyToStepState in Hready;eauto.
        assert (Hec_s' : env_contracts s' caddr = Some ((contract : WeakContract))).
        {
          pose proof H_init.
          decompose_is_init_state H0.
          eapply reachable_through_contract_deployed in H_env_contracts.
          eauto.
          eapply transition_reachable_impl_reachable_through in Htrc_s.
          unfold readyToStepState  in Hready.
          destruct Hready.
          eapply transition_reachable_impl_reachable_through in H0;eauto.
          eauto.
        }
        assert (transition_reachable miner caddr contract caddr s0 s' ).
        eapply transition_reachable_trans;eauto.
        eapply transition_reachable_impl_reachable in H0;eauto.
        pose proof Hcs_s' as Hcs_s'_t.
        eapply frozen_impl_bal_forall in Hcs_s';eauto.
        assert (reachable_via miner caddr contract caddr s0 s s' ).
        {
          econstructor;eauto.
        }
        unfold readyToStepState  in Hready.
        destruct Hready.
        assert(Hbal:env_account_balances s' caddr = cstate'.(balance)).
        {
          eapply balance_on_chain_forall;eauto.
          unfold outgoing_acts.
          rewrite H3.
          simpl.
          eauto.
        }
        rewrite Hcs_s' in Hbal.
        intuition.
      + assert ( exists s', reachable_via miner caddr contract caddr s0 s s' /\s'.(current_slot) >= (expiration cstate)).
        {
          eapply forward_time_ttrace_des;eauto.
          eapply address_not_contract_negb in H_miner.
          eauto.
        }
        destruct H as [s' [Htrv_s_s' Htime]].
        assert (Htrc_s' : transition_reachable miner caddr contract caddr s0 s').
        {
          eapply transition_reachable_through_reachable in Htrv_s_s'.
          eauto.
        }
        assert(Hrct_s0_s' : reachable_through s0 s').
        {
          eapply transition_reachable_impl_reachable_through in Htrc_s';eauto.
        }
        assert(Hcs_s' :exists cstate, contract_state s' caddr = Some cstate).
        {
          eapply reachable_through_contract_deployed in Hrct_s0_s';eauto.
          eapply deployed_contract_state_typed in Hrct_s0_s';eauto.
          eapply transition_reachable_impl_reachable in Htrc_s';eauto.
        }
        
        destruct Hcs_s' as [cstate' Hcs_s'].
        assert(H_EOA: address_is_contract (sender cstate') = false /\ address_is_contract (recipient cstate') = false).
        {
          eapply transition_reachable_impl_reachable in Htrc_s'.
          eapply sender_and_recipient_is_EOA_forall in Hcs_s';eauto.
          intuition.
          eapply address_not_contract_negb;eauto.
          eapply address_not_contract_negb;eauto.
          eapply reachable_through_contract_deployed;eauto.
          eauto.
        }
        assert(Hdeployed' : env_contracts s' caddr = Some (contract: WeakContract)).
        {
          eapply reachable_through_contract_deployed;eauto.
        }
        clear H_sender_EOA H_recipient_EOA.
        destruct H_EOA as [H_sender_EOA H_recipient_EOA].
        assert(Hready' : readyToStepState miner caddr contract caddr s0 s').
        {
          decompose_transition_reachable Htrc_s'.
          eapply readyToStepState_ttrace_readyToStepState in init_bstate;eauto.
        }
        clear Hfrozen.
        destruct (cstate'.(frozen)) eqn : Hfrozen.
        * assert(Hbal:env_account_balances s' caddr = cstate'.(balance)).
          {
            eapply balance_on_chain_forall;eauto.
            unfold outgoing_acts.
            unfold readyToStepState  in Hready' .
            destruct_and_split.
            rewrite H0.
            simpl.
            eauto.
          }
          eapply frozen_impl_bal_forall in Hcs_s';eauto.
          rewrite Hcs_s' in Hbal.
          exists s'.
          econstructor;eauto.
          unfold reachable_via in Htrv_s_s'.
          destruct_and_split.
          eauto.
        * eapply contract_constants_transition_via in Htrc_s'.
          destruct_and_split.
          eapply contract_constants_transition_via in Htrc_s.
          destruct_and_split.
          rewrite Hcs_s in H3.
          inversion H3.
          rewrite <- H8 in *.
          rewrite Hcs_s' in H.
          inversion H.
          rewrite <- H9 in *.
          clear H3 H H8 H9.
          rename H0 into Heq_sender_cstate'.
          rename H1 into Heq_recipient_cstate'.
          rename H2 into Heq_expiration_cstate'.
          rename H4 into Heq_sender_cstate.
          rename H5 into Heq_recipient_cstate.
          rename H6 into Heq_expiration_cstate.
          assert (expiration cstate' <=? current_slot s' = true).
          {
            propify.
            eauto.
            lia.
          }
          eapply anyone_ClaimTimeout_transition_correct in H as Htrans;eauto.
          destruct Htrans as [s'' Htrans].
          pose proof Htrans as Hfrozen_s'.
          eapply anyone_ClaimTimeout_state_correct in Hfrozen_s';eauto.
          destruct Hfrozen_s' as [cstate'' [Hcs_s'' Hfrozen_s']].
          assert (Hact_call : is_call_to_caddr_bool caddr (anyone_ClaimTimeout cstate' (sender cstate') caddr) = true).
          {
            unfold is_call_to_caddr_bool.
            unfold anyone_ClaimTimeout.
            unfold build_call.
            destruct_address_eq;eauto.
          }
          exists s''.
          split.
          assert (inhabited (TransitionTrace miner caddr s s'')).
          {
            unfold reachable_via in Htrv_s_s'.
            destruct Htrv_s_s' as [_ [tr]].
            assert (TransitionTrace miner caddr s' s') by eapply clnil.
            econstructor;eauto.
            econstructor;eauto.
            econstructor;eauto.
          }
          eauto.
          assert (inhabited (TransitionTrace miner caddr s s'')).
          {
            unfold reachable_via in Htrv_s_s'.
            destruct Htrv_s_s' as [_ [tr]].
            assert (TransitionTrace miner caddr s' s') by eapply clnil.
            econstructor;eauto.
            econstructor;eauto.
            econstructor;eauto.
          }
          eauto.
          destruct H0 as [ttrace_s_s''].
          eapply readyToStepState_transition_readyToStepState in Hready';eauto.
          assert (Htrc_s'' : transition_reachable miner caddr contract caddr s0 s'').
          {
            unfold readyToStepState in Hready'.
            destruct_and_split.
            eauto.
          }
          assert (Hec_s'' : env_contracts s'' caddr = Some ((contract : WeakContract))).
          {
            pose proof H_init.
            decompose_is_init_state H0.
            eapply reachable_through_contract_deployed in H_env_contracts.
            eauto.
            eapply transition_reachable_impl_reachable_through in Htrc_s''.
            unfold readyToStepState  in Hready.
            destruct Hready.
            eapply transition_reachable_impl_reachable_through in H0;eauto.
            eauto.
          }
          assert (transition_reachable miner caddr contract caddr s0 s'' ) by eauto.
          eapply transition_reachable_impl_reachable in H0;eauto.
          pose proof Hcs_s'' as Hcs_s''_t.
          eapply frozen_impl_bal_forall in Hcs_s'';eauto.
          unfold readyToStepState  in Hready'.
          destruct Hready'.
          assert(Hbal:env_account_balances s'' caddr = cstate''.(balance)).
          {
            eapply balance_on_chain_forall;eauto.
            unfold outgoing_acts.
            rewrite H2.
            simpl.
            eauto.
          }
          rewrite Hcs_s'' in Hbal.
          intuition.
  Qed.
  

End PaymentChannel.

