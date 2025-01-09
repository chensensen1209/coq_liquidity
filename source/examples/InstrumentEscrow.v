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

Section InstrumentEscrow.

  (** 环境依赖：区块、上下文、地址类型等由外部框架提供。 *)
  Context {BaseTypes : ChainBase}.
  Set Primitive Projections.
  Set Nonrecursive Elimination Schemes.
  Context {AddrSize : N}.

  Local Open Scope Z.

  (***********************************************************)
  (** * 1. 定义合约内部用到的类型与状态                     *)
  (***********************************************************)

  (** Solidity 中的 State { AWAITING_SHIPMENT, AWAITING_ACCEPTANCE,
      COMPLETED, DISPUTED }，在 Coq 中可用 [Inductive] 表示。 *)
  Inductive EscrowPhase :=
  | AWAITING_SHIPMENT
  | AWAITING_ACCEPTANCE
  | COMPLETED
  | DISPUTED.

  (** 合约状态记录 [State]，对应 Solidity 里的存储变量。 *)
  Record State := build_state {
    buyer         : Address;         (* 买家地址 *)
    seller        : Address;         (* 卖家地址 *)
    itemShipped   : bool;            (* 是否已发货 *)
    itemAccepted  : bool;            (* 是否买家验收通过 *)
    arbitrator    : Address;         (* 仲裁人地址（可选） *)
    currentPhase  : EscrowPhase;     (* 当前状态机阶段 *)
    depositAmount       : Amount           (* 合约里剩余的资金余额 *)
  }.

  (** 若需要在合约初始化时接受一些 Setup 参数，可定义 [Setup]。
      这里的逻辑与原 Solidity 略有不同：Solidity 由构造函数指定 seller、arbitrator，
      并由 [msg.value] 得到初始押金。我们可以在 Setup 中传入 seller、arbitrator，
      但实际的 deposit 还需要通过 [ctx_amount] 获取。 *)
  Record Setup := build_setup {
    setup_seller     : Address;
    setup_arbitrator : Address
  }.

  (***********************************************************)
  (** * 2. 为 Record 添加 Settable/Serializable 实例        *)
  (***********************************************************)

  (* 仅演示结构，无实际序列化逻辑。实际可用框架提供的 Derive 语法。 *)
  Instance state_settable : Settable State :=
    settable! build_state
      <buyer; seller; itemShipped; itemAccepted; arbitrator; currentPhase; depositAmount>.

  Instance setup_settable : Settable Setup :=
    settable! build_setup
      <setup_seller; setup_arbitrator>.

  (** 若框架需要消息、状态、设置参数的序列化，可用类似方式声明。示例仅示意。 *)
  Section Serialization.
    Global Instance EscrowPhase_serializable : Serializable EscrowPhase :=
      (* 示例化处理，可根据框架的 Derive 机制来生成。 *)
      Derive Serializable
             (* 仅做演示，对应 AWAITING_SHIPMENT, AWAITING_ACCEPTANCE, COMPLETED, DISPUTED *)
             EscrowPhase_rect<AWAITING_SHIPMENT, AWAITING_ACCEPTANCE, COMPLETED, DISPUTED>.

    Global Instance State_serializable : Serializable State :=
      Derive Serializable State_rect<build_state>.

    Global Instance Setup_serializable : Serializable Setup :=
      Derive Serializable Setup_rect<build_setup>.
  End Serialization.

  (***********************************************************)
  (** * 3. 定义消息类型                                     *)
  (***********************************************************)

  (** Solidity 中对应的函数调用：
      - markAsShipped()
      - acceptItem()
      - rejectItem()
      - arbitrate(bool _buyerWins)
  *)
  Inductive Msg :=
  | MarkAsShipped
  | AcceptItem
  | RejectItem
  | Arbitrate (buyerWins : bool).

  Global Instance Msg_serializable : Serializable Msg :=
    Derive Serializable Msg_rect<MarkAsShipped, AcceptItem, RejectItem, Arbitrate>.

  (***********************************************************)
  (** * 4. 定义错误类型及常量                               *)
  (***********************************************************)

  Definition Error : Type := nat.
  Definition default_error : Error := 1%nat.


  (***********************************************************)
  (** * 5. 合约初始化函数 (init)                             *)
  (***********************************************************)

  (** 对应 Solidity 构造函数:
         constructor(address _seller, address _arbitrator) payable
           - buyer = msg.seller
           - seller = _seller
           - depositAmount = msg.value
           - arbitrator = _arbitrator
           - currentState = AWAITING_SHIPMENT
      在 Coq 中，我们通过 [init] 来模拟此逻辑。
   *)
  Definition init
             (chain : Chain)
             (ctx : ContractCallContext)
             (setup : Setup)
    : result State Error :=
    let msg_sender := ctx_from ctx in
    let msg_value  := ctx_amount ctx in
    (* 合约要求必须带押金，否则无意义 *)
    if (msg_value >? 0)%Z &&
        (address_not_contract msg_sender) &&
        (address_not_contract setup.(setup_seller)) &&
        (address_not_contract setup.(setup_arbitrator) &&
        (address_neqb setup.(setup_seller) setup.(setup_arbitrator)) &&
        (address_neqb (msg_sender) setup.(setup_arbitrator)) &&
        (address_neqb (msg_sender) setup.(setup_seller))) then
      let st := build_state
                  msg_sender            (* buyer = msg.seller *)
                  setup.(setup_seller)  (* seller = _seller *)
                  false                 (* itemShipped = false *)
                  false                 (* itemAccepted = false *)
                  setup.(setup_arbitrator) (* arbitrator = _arbitrator *)
                  AWAITING_SHIPMENT   (* currentPhase = AWAITING_SHIPMENT *)
                  msg_value             (* depositAmount = msg.value *)
      in Ok st
    else
     Err default_error.


  (***********************************************************)
  (** * 6. 具体操作函数（和 Crowdfund 中 donate 等类似）      *)
  (***********************************************************)

  (** 检查当前状态与调用者是否合法的辅助函数。 *)
  Definition require_phase (st : State) (ph : EscrowPhase) : bool :=
    match st.(currentPhase), ph with
    | AWAITING_SHIPMENT, AWAITING_SHIPMENT => true
    | AWAITING_ACCEPTANCE, AWAITING_ACCEPTANCE => true
    | COMPLETED, COMPLETED => true
    | DISPUTED, DISPUTED => true
    | _, _ => false
    end.

  Definition require_sender (ctx : ContractCallContext) (addr : Address) : bool :=
    address_eqb (ctx_from ctx) addr.

  Definition require_zero (ctx : ContractCallContext) : bool :=
    (ctx_amount ctx =? 0) .

  Definition require_no_self_call (ctx : ContractCallContext) : bool :=
    (address_neqb (ctx.(ctx_from))  (ctx.(ctx_contract_address))).
  (***********************************************************)
  (** ** 卖家标记已发货 (markAsShipped)                     *)
  (***********************************************************)
  Definition markAsShipped
             (chain : Chain)
             (ctx : ContractCallContext)
             (st : State)
    : result (State * list ActionBody) Error :=
    if (require_phase st AWAITING_SHIPMENT) && (require_sender ctx st.(seller))
    then
      let new_st := st <| itemShipped := true |>
                       <| currentPhase := AWAITING_ACCEPTANCE |> in
      Ok (new_st, [])
    else
      Err default_error.

  (***********************************************************)
  (** ** 买家验收通过 (acceptItem)                           *)
  (***********************************************************)
  Definition acceptItem
             (chain : Chain)
             (ctx : ContractCallContext)
             (st : State)
    : result (State * list ActionBody) Error :=
    if (require_phase st AWAITING_ACCEPTANCE) && (require_sender ctx st.(buyer))
    then
      (** itemAccepted = true; currentPhase = COMPLETED;
          资金释放给卖家 -> [act_transfer st.(seller) st.(balance)] *)
      let actions := [ act_transfer st.(seller) st.(depositAmount) ] in
      let new_st := st <| itemAccepted := true |>
                       <| currentPhase := COMPLETED |>
                       <| depositAmount := 0 |>
      in
      Ok (new_st, actions)
    else
      Err default_error.

  (***********************************************************)
  (** ** 触发纠纷 (rejectItem)             *)
  (***********************************************************)
  Definition rejectItem
             (chain : Chain)
             (ctx : ContractCallContext)
             (st : State)
    : result (State * list ActionBody) Error :=
    if (require_phase st AWAITING_ACCEPTANCE || require_phase st AWAITING_SHIPMENT )
    then
      (** currentPhase = DISPUTED; *)
      let new_st := st <| currentPhase := DISPUTED |> in
      Ok (new_st, [])
    else
      Err default_error.

  (***********************************************************)
  (** ** 仲裁处理 (arbitrate)                                *)
  (***********************************************************)
  Definition arbitrate
             (chain : Chain)
             (ctx : ContractCallContext)
             (st : State)
             (buyerWins : bool)
    : result (State * list ActionBody) Error :=
    if (require_phase st DISPUTED) && (require_sender ctx st.(arbitrator))
    then
      (** if buyerWins then transfer to buyer; else transfer to seller. *)
      let to_addr :=
        if buyerWins then st.(buyer) else st.(seller) in
      let actions := [ act_transfer to_addr st.(depositAmount) ] in
      let new_st := st <| currentPhase := COMPLETED |>
                       <| depositAmount := 0 |> in
      Ok (new_st, actions)
    else
      Err default_error.

  (***********************************************************)
  (** * 7. 合约主接收函数 (receive)                           *)
  (***********************************************************)
  Definition receive
             (chain : Chain)
             (ctx : ContractCallContext)
             (st : State)
             (msg : option Msg)
    : result (State * list ActionBody) Error :=
    if require_zero ctx && require_no_self_call ctx then
      match msg with
      | Some MarkAsShipped       => markAsShipped chain ctx st
      | Some AcceptItem          => acceptItem chain ctx st
      | Some RejectItem          => rejectItem chain ctx st
      | Some (Arbitrate bWins)   => arbitrate chain ctx st bWins
      | None                     => Err default_error
      end
    else
      Err default_error. 


  (***********************************************************)
  (** * 8. 最终合约定义                                       *)
  (***********************************************************)
  Definition contract : Contract Setup Msg State Error :=
    build_contract init receive.

End InstrumentEscrow.

Section Lqiuidity.

Context {BaseTypes : ChainBase}.
Set Primitive Projections.
Set Nonrecursive Elimination Schemes.
Context {AddrSize : N}.
Context {DepthFirst : bool}.

  
Ltac reduce_init_escrow :=
  match goal with
  | H : init ?chain ?ctx ?setup = Ok ?state |- _ =>
      (* 1. 展开 init 函数 *)
      unfold init in H;
      (* 2. 分解联合条件: (msg_value <=? 0)%Z && address_not_contract ... && address_not_contract ... *)
      destruct ((ctx_amount ctx >? 0)%Z &&
              address_not_contract (ctx_from ctx) &&
              address_not_contract (setup_seller setup) &&
              (address_not_contract (setup_arbitrator setup) &&
               address_neqb (setup_seller setup) (setup_arbitrator setup) &&
               address_neqb (ctx_from ctx) (setup_arbitrator setup) &&
               address_neqb (ctx_from ctx) (setup_seller setup))) eqn:Einit in H;
        try discriminate; (* 若此分支不成立则结束 *)
      (* 3. 进入 Ok 分支时可以做进一步简化（若需要），否则只保留 eqn:Einit 供后续推理。 *)
      simpl in H
  end.

Ltac reduce_receive_escrow :=
  match goal with
  | H : receive ?chain ?ctx ?st ?msg = Ok (?new_st, ?acts) |- _ =>
      (* 1. 展开 receive 函数 *)
      unfold receive in H;
      (* 2. 分解 require_zero ctx *)
      destruct (require_zero ctx && require_no_self_call ctx) eqn:Ezero in H; try discriminate;
      (* 3. 若 require_zero ctx = true，则进入 match msg *)
      destruct msg eqn:Emsg in H; try discriminate;
      (* 如果需要进一步分解各种消息对应的子函数，可在此继续:
         例如 unfold markAsShipped in H; destruct if-conditions ... *)
      simpl in H
  end.

  Ltac reduce_markAsShipped :=
  match goal with
  | H : markAsShipped ?chain ?ctx ?st = Ok (?new_st, ?acts) |- _ =>
      (* 1. 展开函数体 *)
      unfold markAsShipped in H;
      (* 2. 分解布尔条件 (require_phase && require_sender) *)
      destruct ((require_phase st AWAITING_SHIPMENT) &&
                (require_sender ctx st.(seller))) eqn:Emark in H;
      try discriminate;
      simpl in H
  end.

  Ltac reduce_acceptItem :=
    match goal with
    | H : acceptItem ?chain ?ctx ?st = Ok (?new_st, ?acts) |- _ =>
        unfold acceptItem in H;
        destruct ((require_phase st AWAITING_ACCEPTANCE) &&
                  (require_sender ctx st.(buyer))) eqn:Eaccept in H;
        try discriminate;
        simpl in H
    end.

  Ltac reduce_rejectItem :=
    match goal with
    | H : rejectItem ?chain ?ctx ?st = Ok (?new_st, ?acts) |- _ =>
        unfold rejectItem in H;
        destruct ((require_phase st AWAITING_ACCEPTANCE || require_phase st AWAITING_SHIPMENT)) eqn:Ereject in H;
        try discriminate;
        simpl in H
    end.

  Ltac reduce_arbitrate :=
    match goal with
    | H : arbitrate ?chain ?ctx ?st ?buyerWins = Ok (?new_st, ?acts) |- _ =>
        unfold arbitrate in H;
        destruct ((require_phase st DISPUTED) &&
                  (require_sender ctx st.(arbitrator))) eqn:Earb in H;
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

  Definition ubuyer := (init_cstate.(buyer)).
  Definition useller := (init_cstate.(seller)).
  Definition uarbitrator := (init_cstate.(arbitrator)).
  

  Definition seller_call_MarkAsShipped (state : State) : Action :=
    build_call useller caddr 0 MarkAsShipped.

  Definition seller_call_RejectItem 
    (state : State) 
    : Action :=
  build_call useller caddr 0 RejectItem.

  Definition buyer_call_AcceptItem (state : State) : Action :=
  build_call ubuyer caddr 0 AcceptItem.

  Definition buyer_call_RejectItem 
            (state : State) 
            : Action :=
    build_call ubuyer caddr 0 RejectItem.

  Definition arbitrator_call_Arbitrate 
            (state : State) 
            (bWins: bool) 
            : Action :=
    build_call uarbitrator caddr 0 (Arbitrate bWins).

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
      effective_balance = cstate.(depositAmount).
Proof.
  intros.
  unfold effective_balance.
  contract_induction; intros; auto; cbn in *;try congruence;try lia;eauto.
  - reduce_init_escrow.
    inversion init_some.
    simpl.
    lia.
  - reduce_receive_escrow.
    destruct_message;try congruence.
    + reduce_markAsShipped. cbn in *.
      inversion receive_some. simpl.
      unfold require_zero in Ezero.
      propify.
      lia.
    + reduce_acceptItem . cbn in *.
      inversion receive_some. simpl.
      unfold require_zero in Ezero.
      propify.
      lia.
    + reduce_rejectItem  . cbn in *.
      inversion receive_some. simpl.
      unfold require_zero in Ezero.
      propify.
      lia.
    + reduce_arbitrate  . cbn in *.
      inversion receive_some. simpl.
      unfold require_zero in Ezero.
      propify.
      lia.
  - reduce_receive_escrow.
    destruct_message;try congruence.
    + reduce_markAsShipped. cbn in *.
      inversion receive_some. simpl.
      unfold require_zero in Ezero.
      propify.
      inversion receive_some; destruct head; cbn in *; lia.
    + reduce_acceptItem . cbn in *.
      inversion receive_some. simpl.
      unfold require_zero in Ezero.
      propify.
      inversion receive_some; destruct head; cbn in *; lia.
    + reduce_rejectItem  . cbn in *.
      inversion receive_some. simpl.
      unfold require_zero in Ezero.
      propify.
      inversion receive_some; destruct head; cbn in *; lia.
    + reduce_arbitrate  . cbn in *.
      inversion receive_some. simpl.
      unfold require_zero in Ezero.
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
      env_account_balances bstate caddr = cstate.(depositAmount).
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
    env_account_balances bstate caddr = cstate.(depositAmount).
Proof.
  intros.
  eapply balance_on_chain in H;eauto.
  destruct H;
  destruct_and_split.
  rewrite H2 in H.
  inversion H; subst;
  eauto.
Qed.

  Lemma COMPLETED_impl_bal bstate:
    reachable bstate ->
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    exists cstate, 
      contract_state bstate caddr = Some cstate /\
      (cstate.(currentPhase) = COMPLETED -> (cstate.(depositAmount) = 0)%Z).
  Proof.
    contract_induction;intros;cbn in *;eauto;try congruence;try lia.
    - reduce_init_escrow.
      inversion init_some.
      subst.
      cbn in *.
      congruence.
    - reduce_receive_escrow.
      destruct_message;try congruence.
      + reduce_markAsShipped. cbn in *.
        inversion receive_some;subst;cbn in *.
        congruence.
      + reduce_acceptItem . cbn in *.
        inversion receive_some;subst;cbn in *.
        congruence.
      + reduce_rejectItem  . cbn in *.
        inversion receive_some;subst;cbn in *.
        congruence.
      + reduce_arbitrate  . cbn in *.
        inversion receive_some;subst;cbn in *.
        congruence.
    - reduce_receive_escrow.
      destruct_message;try congruence.
      + reduce_markAsShipped. cbn in *.
        inversion receive_some;subst;cbn in *;destruct head; cbn in *;try congruence.
      + reduce_acceptItem . cbn in *.
      inversion receive_some;subst;cbn in *;destruct head; cbn in *;try congruence.
      + reduce_rejectItem  . cbn in *.
      inversion receive_some;subst;cbn in *;destruct head; cbn in *;try congruence.
      + reduce_arbitrate  . cbn in *.
      inversion receive_some;subst;cbn in *;destruct head; cbn in *;try congruence.
    - solve_facts.
  Qed.

  Lemma COMPLETED_impl_bal_forall bstate cstate:
    reachable bstate ->
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    contract_state bstate caddr = Some cstate ->
    cstate.(currentPhase) = COMPLETED -> 
    (cstate.(depositAmount) = 0)%Z.
  Proof.
    intros.
    eapply COMPLETED_impl_bal in H;eauto.
    destruct H.
    destruct_and_split.
    rewrite H in H1;
    inversion H1; subst;
    destruct_and_split.
    eauto.
  Qed.


  Lemma contract_constants_receive :forall prev_state new_state chain ctx msg new_acts,
  receive chain ctx prev_state msg = Ok (new_state, new_acts) ->
    prev_state.(seller) = new_state.(seller)
    /\ prev_state.(buyer) = new_state.(buyer)
    /\ prev_state.(arbitrator) = new_state.(arbitrator).
  Proof.
    intros.
    reduce_receive_escrow.
    destruct_message;try congruence.
    - reduce_markAsShipped .
      inversion H.
      split.
      simpl.
      eauto.
      simpl.
      eauto.
    - reduce_acceptItem.
      inversion H.
      split.
      simpl.
      eauto.
      simpl.
      eauto.
    - reduce_rejectItem .
      inversion H.
      split.
      simpl.
      eauto.
      simpl.
      eauto.
    -  reduce_arbitrate  .
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
      cstate.(seller) = init_cstate.(seller) /\
      cstate.(buyer) = init_cstate.(buyer) /\
      cstate.(arbitrator) = init_cstate.(arbitrator) .
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
      cstate.(seller) = init_cstate.(seller) /\
      cstate.(buyer) = init_cstate.(buyer) /\
      cstate.(arbitrator) = init_cstate.(arbitrator) .
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

  Lemma seller_and_recipient_is_EOA bstate:
    reachable bstate ->
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    exists cstate,
      contract_state bstate caddr = Some cstate
      /\ address_not_contract cstate.(seller) = true
      /\ address_not_contract cstate.(buyer) = true
      /\ address_not_contract cstate.(arbitrator) = true
      /\ address_neqb (cstate.(seller)) (cstate.(arbitrator)) = true
      /\ address_neqb (cstate.(buyer)) (cstate.(arbitrator))= true
      /\ address_neqb (cstate.(buyer)) (cstate.(seller))= true .
  Proof.
    contract_induction;intros;cbn in *;eauto;try congruence;try lia.
    - reduce_init_escrow.
      propify.
      destruct_and_split.
      destruct_and_split.
      inversion init_some.
      subst.
      simpl.
      eauto.
      intuition.
      propify.
      destruct_and_split.
      eauto.
      inversion init_some.
      subst.
      simpl.
      eauto.
      inversion init_some.
      subst.
      simpl.
      eauto.
      inversion init_some.
      subst.
      simpl.
      eauto.
      inversion init_some.
      subst.
      simpl.
      eauto.
      inversion init_some.
      subst.
      simpl.
      eauto.
    - reduce_receive_escrow.
      destruct_message;try congruence.
      + reduce_markAsShipped. cbn in *.
        inversion receive_some;subst;cbn in *.
        congruence.
      + reduce_acceptItem . cbn in *.
        inversion receive_some;subst;cbn in *.
        congruence.
      + reduce_rejectItem  . cbn in *.
        inversion receive_some;subst;cbn in *.
        congruence.
      + reduce_arbitrate  . cbn in *.
        inversion receive_some;subst;cbn in *.
        congruence.
    - reduce_receive_escrow.
      destruct_message;try congruence.
      + reduce_markAsShipped. cbn in *.
        inversion receive_some;subst;cbn in *;destruct head; cbn in *;try congruence.
      + reduce_acceptItem . cbn in *.
      inversion receive_some;subst;cbn in *;destruct head; cbn in *;try congruence.
      + reduce_rejectItem  . cbn in *.
      inversion receive_some;subst;cbn in *;destruct head; cbn in *;try congruence.
      + reduce_arbitrate  . cbn in *.
      inversion receive_some;subst;cbn in *;destruct head; cbn in *;try congruence.
    - solve_facts.
  Qed.

  Lemma constant_addr_properties_forll bstate cstate:
    reachable bstate ->
    env_contracts bstate caddr = Some (contract : WeakContract) ->
    contract_state bstate caddr = Some cstate ->
    (address_not_contract cstate.(seller) = true 
    /\  address_not_contract cstate.(buyer) = true 
    /\ address_not_contract cstate.(arbitrator) = true
      /\ address_neqb (cstate.(seller)) (cstate.(arbitrator)) = true
      /\ address_neqb (cstate.(buyer)) (cstate.(arbitrator))= true
      /\ address_neqb (cstate.(buyer)) (cstate.(seller))= true ).
  Proof.
    intros.
    eapply seller_and_recipient_is_EOA in H;eauto.
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
    destruct_and_split.
    eauto.
    rewrite H in H1;
    inversion H1; subst;
    destruct_and_split.
    eauto.
    rewrite H in H1;
    inversion H1; subst;
    destruct_and_split.
    eauto.
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

  Lemma seller_call_MarkAsShipped_is_call_act cstate:
    is_call_act (seller_call_MarkAsShipped cstate) = true .
  Proof.
    unfold is_call_act.
    unfold seller_call_MarkAsShipped.
    simpl.
    destruct_address_eq;eauto.
  Qed.

  Lemma buyer_call_AcceptItem_is_call_act cstate:
    is_call_act (buyer_call_AcceptItem  cstate) = true .
  Proof.
    unfold is_call_act.
    unfold buyer_call_AcceptItem  .
    simpl.
    destruct_address_eq;eauto.
  Qed.

  Lemma buyer_call_RejectItem_is_call_act cstate:
    is_call_act (buyer_call_RejectItem  cstate) = true .
  Proof.
    unfold is_call_act.
    unfold buyer_call_RejectItem  .
    simpl.
    destruct_address_eq;eauto.
  Qed.

  Lemma seller_call_RejectItem_is_call_act cstate:
    is_call_act (seller_call_RejectItem  cstate) = true .
  Proof.
    unfold is_call_act.
    unfold seller_call_RejectItem  .
    simpl.
    destruct_address_eq;eauto.
  Qed.

  Lemma arbitrator_call_Arbitrate_is_call_act cstate win:
    is_call_act (arbitrator_call_Arbitrate win  cstate) = true .
  Proof.
    unfold is_call_act.
    unfold arbitrator_call_Arbitrate.
    simpl.
    destruct_address_eq;eauto.
  Qed.
  

  Lemma seller_call_MarkAsShipped_transition_correct:
    forall (s:ChainState) cstate,
      contract_state s caddr = Some cstate ->
      require_phase cstate AWAITING_SHIPMENT = true ->
      transition_reachable miner contract caddr s0 s ->
      exists s', 
        transition miner s (seller_call_MarkAsShipped cstate) = Ok s'.
  Proof.
    intros * Hcs_s Hphase_state Htrc_s.
    eexists.
    unfold transition.
    unfold queue_isb_empty.
    eapply transition_reachable_queue_is_empty in Htrc_s as Hqueue_s.
    rewrite seller_call_MarkAsShipped_is_call_act.
    unfold evaluate_action.
    rewrite get_valid_header_is_valid_header.
    unfold seller_call_MarkAsShipped .
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
    unfold useller.
    assert(H_constans:cstate.(seller) = init_cstate.(seller) /\
                      cstate.(buyer) = init_cstate.(buyer) /\
                      cstate.(arbitrator) = init_cstate.(arbitrator)).
    {
      eapply transition_reachable_impl_reachable in Htrc_s as Hrc_s.
      destruct_and_split.
      eapply transition_reachable_impl_reachable_through in Htrc_s as Htrt.
      eapply contract_constants_reachable_through in Htrt;eauto.
      destruct_and_split.
      rewrite H in Hcs_s.
      inversion Hcs_s.
      subst.
      intuition.
      eauto.
      eauto.
      eapply transition_reachable_impl_reachable_through in Htrc_s.
      eapply contract_constants_reachable_through in Htrc_s;eauto.
      destruct_and_split.
      rewrite H in Hcs_s.
      inversion Hcs_s.
      subst.
      intuition.
      eauto.
      eauto.
      eapply transition_reachable_impl_reachable_through in Htrc_s.
      eapply contract_constants_reachable_through in Htrc_s;eauto.
      destruct_and_split.
      rewrite H in Hcs_s.
      inversion Hcs_s.
      subst.
      intuition.
      eauto.
      eauto.
    }
    destruct  H_constans as [H_seller_cons [H_buyer_cons H_arbitrator_cons]].
    assert(H_EOA: address_is_contract (seller cstate) = false /\ address_is_contract (buyer cstate) = false).
    {
      eapply transition_reachable_impl_reachable in Htrc_s.
      eapply constant_addr_properties_forll in Hcs_s;eauto.
      destruct_and_split.
      eapply address_not_contract_negb in H0.
      eapply address_not_contract_negb in H.
      eauto.
      eapply address_not_contract_negb in H0.
      eapply address_not_contract_negb in H.
      eauto.
      eauto.
    }

    destruct H_EOA as [H_seller_eoa H_buyer_eoa].
    destruct_address_eq;try congruence.
    simpl.
    rewrite <- H_seller_cons.
    intuition.
    rewrite H_seller_eoa.
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
    assert(Hbal:env_account_balances s caddr = cstate.(depositAmount)).
    {
      eapply balance_on_chain_forall;eauto.
      unfold outgoing_acts.
      rewrite Hqueue_s.
      simpl.
      eauto.
    }
    destruct_address_eq;try congruence.
    + assert ((0 >? miner_reward + env_account_balances s (seller cstate))%Z 
                = false).
      {
        unfold miner_reward.
        eapply (account_balance_nonnegative s (seller cstate)) in Hrc_s.
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
      destruct_address_eq;try congruence.
      simpl.
      cbn .
      unfold markAsShipped.
      simpl.
      rewrite Hphase_state.
      unfold require_sender.
      simpl.
      rewrite Hqueue_s.
      destruct_address_eq;try congruence;cbn;eauto.
      
    + eapply address_not_contract_negb in H_miner.
      congruence.
    + assert ((0 >? env_account_balances s (seller cstate))%Z = false).
      {
        unfold miner_reward.
        eapply (account_balance_nonnegative s (seller cstate)) in Hrc_s.
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
      unfold require_no_self_call.
      simpl.
      destruct_address_eq;try congruence.
      simpl.
      cbn .
      unfold markAsShipped.
      simpl.
      rewrite Hphase_state.
      unfold require_sender.
      simpl.
      rewrite Hqueue_s.
      destruct_address_eq;try congruence;cbn;eauto.
    + eauto.
  Qed.
  
  Local Open Scope Z.

  Lemma buyer_call_AcceptItem_transition_correct:
    forall (s:ChainState) cstate,
    contract_state s caddr = Some cstate ->
    require_phase cstate AWAITING_ACCEPTANCE = true ->
    transition_reachable miner contract caddr s0 s ->
    exists s', 
      transition miner s (buyer_call_AcceptItem cstate) = Ok s'.
  Proof.
    intros * Hcs_s Hphase_state Htrc_s.
    eexists.
    unfold transition.
    unfold queue_isb_empty.
    pose proof Htrc_s.
    eapply transition_reachable_queue_is_empty in H as Hqueue_s.
    rewrite Hqueue_s.
    rewrite buyer_call_AcceptItem_is_call_act.
    unfold evaluate_action.
    rewrite get_valid_header_is_valid_header.
    unfold buyer_call_AcceptItem .
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
    unfold ubuyer.
    assert(H_constans:cstate.(seller) = init_cstate.(seller) /\
                      cstate.(buyer) = init_cstate.(buyer) /\
                      cstate.(arbitrator) = init_cstate.(arbitrator)).
    {
      eapply transition_reachable_impl_reachable in Htrc_s.
      unfold transition_reachable in Htrc_s.
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
      eapply transition_reachable_impl_reachable_through in H.
      eapply contract_constants_reachable_through in H;eauto.
      destruct_and_split.
      rewrite H in Hcs_s.
      inversion Hcs_s.
      subst.
      intuition.
      eauto.
      eauto.
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
    destruct  H_constans as [H_seller_cons [H_buyer_cons H_arbitrator_cons]].
    assert(H_EOA: address_is_contract (seller cstate) = false /\ address_is_contract (buyer cstate) = false).
    {
      eapply transition_reachable_impl_reachable in Htrc_s.
      eapply constant_addr_properties_forll in Hcs_s;eauto.
      destruct_and_split.
      eapply address_not_contract_negb in H0.
      eapply address_not_contract_negb in H1.
      eauto.
      eapply address_not_contract_negb in H0.
      eapply address_not_contract_negb in H1.
      eauto.
      eauto.
    }
    destruct H_EOA as [H_seller_eoa H_buyer_eoa].
    destruct_address_eq;try congruence.
    simpl.
    rewrite <- H_buyer_cons.
    intuition.
    rewrite H_buyer_eoa.
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
    assert(Hbal:env_account_balances s caddr = cstate.(depositAmount)).
    {
      eapply balance_on_chain_forall;eauto.
      unfold outgoing_acts.
      rewrite Hqueue_s.
      simpl.
      eauto.
    }
    clear H.
    destruct_address_eq;try congruence.
      + assert ((0 >? miner_reward + env_account_balances s (buyer cstate))%Z 
                  = false).
        {
          unfold miner_reward.
          eapply (account_balance_nonnegative s (buyer cstate)) in Hrc_s.
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
        destruct_address_eq;try congruence.
        simpl.
        cbn .
        unfold acceptItem.
        simpl.
        rewrite Hphase_state.
        unfold require_sender.
        simpl.
        destruct_address_eq;try congruence;cbn;eauto.
        unfold send_or_call.
        assert(depositAmount cstate <? 0 = false).
        {
          eapply (account_balance_nonnegative s caddr) in Hrc_s.
          propify.
          lia.
        }
        rewrite H0.
        simpl.
        destruct_address_eq;try congruence.
        (* 1 *)
        assert(depositAmount cstate >? 0 + (env_account_balances s caddr) = false)%Z.
        {
          propify.
          lia.
        }
        rewrite H1.
        assert (H_sender_none: env_contracts s (seller  cstate) = None).
        { 
          destruct (env_contracts s (seller  cstate)) eqn:H_env.
          - exfalso.
            apply (contract_addr_format (seller  cstate) w) in H_env; eauto.
            congruence.
          - reflexivity.
        }
        rewrite H_sender_none.
        rewrite H_seller_eoa.
        simpl.
        eauto.
        (* 2 *)
        assert(depositAmount cstate >? 0 + (env_account_balances s caddr) = false)%Z.
        {
          propify.
          lia.
        }
        rewrite H1.
        assert (H_sender_none: env_contracts s (seller  cstate) = None).
        { 
          destruct (env_contracts s (seller  cstate)) eqn:H_env.
          - exfalso.
            apply (contract_addr_format (seller  cstate) w) in H_env; eauto.
            congruence.
          - reflexivity.
        }
        rewrite H_sender_none.
        rewrite H_seller_eoa.
        simpl.
        eauto.
    + eapply address_not_contract_negb in H_miner.
      congruence.
    + assert ((0 >? env_account_balances s (buyer cstate))%Z = false).
      {
        unfold miner_reward.
        eapply (account_balance_nonnegative s (buyer cstate)) in Hrc_s.
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
      unfold require_no_self_call.
      simpl.
      destruct_address_eq;try congruence.
      simpl.
      cbn .
      unfold acceptItem.
      simpl.
      rewrite Hphase_state.
      unfold require_sender.
      simpl.
      destruct_address_eq;try congruence;cbn;eauto.
      unfold send_or_call.
        assert(depositAmount cstate <? 0 = false).
        {
          eapply (account_balance_nonnegative s caddr) in Hrc_s.
          propify.
          lia.
        }
        rewrite H0.
        simpl.
        destruct_address_eq;try congruence.
        (* 1 *)
        assert(depositAmount cstate >? 0 + (env_account_balances s caddr) = false)%Z.
        {
          propify.
          lia.
        }
        rewrite H1.
        assert (H_sender_none: env_contracts s (seller  cstate) = None).
        { 
          destruct (env_contracts s (seller  cstate)) eqn:H_env.
          - exfalso.
            apply (contract_addr_format (seller  cstate) w) in H_env; eauto.
            congruence.
          - reflexivity.
        }
        rewrite H_sender_none.
        rewrite H_seller_eoa.
        simpl.
        eauto.
        (* 2 *)
        assert(depositAmount cstate >? 0 + (env_account_balances s caddr) = false)%Z.
        {
          propify.
          lia.
        }
        rewrite H1.
        assert (H_sender_none: env_contracts s (seller  cstate) = None).
        { 
          destruct (env_contracts s (seller  cstate)) eqn:H_env.
          - exfalso.
            apply (contract_addr_format (seller  cstate) w) in H_env; eauto.
            congruence.
          - reflexivity.
        }
        rewrite H_sender_none.
        rewrite H_seller_eoa.
        simpl.
        eauto.
        (* 3 *)
        assert(depositAmount cstate >? 0 + (env_account_balances s caddr) = false)%Z.
        {
          propify.
          lia.
        }
        rewrite H1.
        assert (H_sender_none: env_contracts s (seller  cstate) = None).
        { 
          destruct (env_contracts s (seller  cstate)) eqn:H_env.
          - exfalso.
            apply (contract_addr_format (seller  cstate) w) in H_env; eauto.
            congruence.
          - reflexivity.
        }
        rewrite H_sender_none.
        rewrite H_seller_eoa.
        simpl.
        eauto.
      + eauto.
  Qed.
  

  Lemma buyer_call_RejectItem_transition_correct:
    forall (s:ChainState) cstate,
      contract_state s caddr = Some cstate ->
      (require_phase cstate AWAITING_ACCEPTANCE = true \/ 
      require_phase cstate AWAITING_SHIPMENT = true) ->
      transition_reachable miner contract caddr s0 s ->
      exists s', 
        transition miner s (buyer_call_RejectItem cstate) = Ok s'.
  Proof.

    intros * Hcs_s Hphase_state Htrc_s.
    eexists.
    unfold transition.
    unfold queue_isb_empty.
    pose proof Htrc_s.
    eapply transition_reachable_queue_is_empty in H as Hqueue_s.
    rewrite Hqueue_s.
    destruct Hphase_state as [Hphase_state | Hphase_state].
    (*  *)
    -
    rewrite buyer_call_RejectItem_is_call_act.
    unfold evaluate_action.
    rewrite get_valid_header_is_valid_header.
    unfold buyer_call_RejectItem .
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
    unfold ubuyer.
    assert(H_constans:cstate.(seller) = init_cstate.(seller) /\
                      cstate.(buyer) = init_cstate.(buyer) /\
                      cstate.(arbitrator) = init_cstate.(arbitrator)).
    {
      eapply transition_reachable_impl_reachable in Htrc_s.
      unfold transition_reachable in Htrc_s.
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
      eapply transition_reachable_impl_reachable_through in H.
      eapply contract_constants_reachable_through in H;eauto.
      destruct_and_split.
      rewrite H in Hcs_s.
      inversion Hcs_s.
      subst.
      intuition.
      eauto.
      eauto.
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
    destruct  H_constans as [H_seller_cons [H_buyer_cons H_arbitrator_cons]].
    assert(H_EOA: address_is_contract (seller cstate) = false /\ address_is_contract (buyer cstate) = false).
    {
      eapply transition_reachable_impl_reachable in Htrc_s.
      eapply constant_addr_properties_forll in Hcs_s;eauto.
      destruct_and_split.
      eapply address_not_contract_negb in H0.
      eapply address_not_contract_negb in H1.
      eauto.
      eapply address_not_contract_negb in H0.
      eapply address_not_contract_negb in H1.
      eauto.
      eauto.
    }
    destruct H_EOA as [H_seller_eoa H_buyer_eoa].
    destruct_address_eq;try congruence.
    simpl.
    rewrite <- H_buyer_cons.
    intuition.
    rewrite H_buyer_eoa.
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
    assert(Hbal:env_account_balances s caddr = cstate.(depositAmount)).
    {
      eapply balance_on_chain_forall;eauto.
      unfold outgoing_acts.
      rewrite Hqueue_s.
      simpl.
      eauto.
    }
    clear H.
    destruct_address_eq;try congruence.
    + assert ((0 >? miner_reward + env_account_balances s (buyer  cstate))%Z 
                = false).
      {
        unfold miner_reward.
        eapply (account_balance_nonnegative s (buyer  cstate)) in Hrc_s.
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
      destruct_address_eq;try congruence.
      simpl.
      cbn .
      unfold rejectItem.
      simpl.
      rewrite Hphase_state.
      unfold require_sender.
      simpl.
      destruct_address_eq;try congruence;cbn;eauto.
    + eapply address_not_contract_negb in H_miner.
      congruence.
    + assert ((0 >? env_account_balances s (buyer  cstate))%Z = false).
      {
        unfold miner_reward.
        eapply (account_balance_nonnegative s (buyer  cstate)) in Hrc_s.
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
      unfold require_no_self_call.
      simpl.
      destruct_address_eq;try congruence.
      simpl.
      cbn .
      unfold rejectItem.
      simpl.
      rewrite Hphase_state.
      unfold require_sender.
      simpl.
      destruct_address_eq;try congruence;cbn;eauto.
    - 
    rewrite buyer_call_RejectItem_is_call_act.
    unfold evaluate_action.
    rewrite get_valid_header_is_valid_header.
    unfold buyer_call_RejectItem .
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
    unfold ubuyer.
    assert(H_constans:cstate.(seller) = init_cstate.(seller) /\
                      cstate.(buyer) = init_cstate.(buyer) /\
                      cstate.(arbitrator) = init_cstate.(arbitrator)).
    {
      eapply transition_reachable_impl_reachable in Htrc_s.
      unfold transition_reachable in Htrc_s.
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
      eapply transition_reachable_impl_reachable_through in H.
      eapply contract_constants_reachable_through in H;eauto.
      destruct_and_split.
      rewrite H in Hcs_s.
      inversion Hcs_s.
      subst.
      intuition.
      eauto.
      eauto.
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
    destruct  H_constans as [H_seller_cons [H_buyer_cons H_arbitrator_cons]].
    assert(H_EOA: address_is_contract (seller cstate) = false /\ address_is_contract (buyer cstate) = false).
    {
      eapply transition_reachable_impl_reachable in Htrc_s.
      eapply constant_addr_properties_forll in Hcs_s;eauto.
      destruct_and_split.
      eapply address_not_contract_negb in H0.
      eapply address_not_contract_negb in H1.
      eauto.
      eapply address_not_contract_negb in H0.
      eapply address_not_contract_negb in H1.
      eauto.
      eauto.
    }
    destruct H_EOA as [H_seller_eoa H_buyer_eoa].
    destruct_address_eq;try congruence.
    simpl.
    rewrite <- H_buyer_cons.
    intuition.
    rewrite H_buyer_eoa.
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
    assert(Hbal:env_account_balances s caddr = cstate.(depositAmount)).
    {
      eapply balance_on_chain_forall;eauto.
      unfold outgoing_acts.
      rewrite Hqueue_s.
      simpl.
      eauto.
    }
    clear H.
    destruct_address_eq;try congruence.
    + assert ((0 >? miner_reward + env_account_balances s (buyer  cstate))%Z 
                = false).
      {
        unfold miner_reward.
        eapply (account_balance_nonnegative s (buyer  cstate)) in Hrc_s.
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
      destruct_address_eq;try congruence.
      simpl.
      cbn .
      unfold rejectItem.
      simpl.
      simpl.
      rewrite Hphase_state.
      simpl.
      assert (Hphase_state_true:require_phase cstate AWAITING_ACCEPTANCE || true = true).
      {
        intuition.
      }
      rewrite Hphase_state_true.
      unfold require_sender.
      simpl.
      simpl.
      destruct_address_eq;try congruence;cbn;eauto.
    + eapply address_not_contract_negb in H_miner.
      congruence.
    + assert ((0 >? env_account_balances s (buyer  cstate))%Z = false).
      {
        unfold miner_reward.
        eapply (account_balance_nonnegative s (buyer  cstate)) in Hrc_s.
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
      unfold require_no_self_call.
      simpl.
      destruct_address_eq;try congruence.
      simpl.
      cbn .
      unfold rejectItem.
      simpl.
      rewrite Hphase_state.
      unfold require_sender.
      simpl.
      destruct_address_eq;try congruence;cbn;eauto.
      assert (Hphase_state_true:require_phase cstate AWAITING_ACCEPTANCE || true = true).
      {
        intuition.
      }
      rewrite Hphase_state_true.
      unfold require_sender.
      simpl.
      simpl.
      destruct_address_eq;try congruence;cbn;eauto.
    - eauto.
  Qed.

  Lemma seller_call_RejectItem_transition_correct:
    forall (s:ChainState) cstate,
      contract_state s caddr = Some cstate ->
      (require_phase cstate AWAITING_ACCEPTANCE = true \/ 
      require_phase cstate AWAITING_SHIPMENT = true) ->
      transition_reachable miner contract caddr s0 s ->
      exists s', 
        transition miner s (seller_call_RejectItem cstate) = Ok s'.
  Proof.
    intros * Hcs_s Hphase_state Htrc_s.
    eexists.
    unfold transition.
    unfold queue_isb_empty.
    pose proof Htrc_s.
    eapply transition_reachable_queue_is_empty in H as Hqueue_s.
    rewrite Hqueue_s.
    destruct Hphase_state as [Hphase_state | Hphase_state].
    (*  *)
    -
    rewrite seller_call_RejectItem_is_call_act.
    unfold evaluate_action.
    rewrite get_valid_header_is_valid_header.
    unfold seller_call_RejectItem .
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
    unfold useller.
    assert(H_constans:cstate.(seller) = init_cstate.(seller) /\
                      cstate.(buyer) = init_cstate.(buyer) /\
                      cstate.(arbitrator) = init_cstate.(arbitrator)).
    {
      eapply transition_reachable_impl_reachable in Htrc_s.
      unfold transition_reachable in Htrc_s.
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
      eapply transition_reachable_impl_reachable_through in H.
      eapply contract_constants_reachable_through in H;eauto.
      destruct_and_split.
      rewrite H in Hcs_s.
      inversion Hcs_s.
      subst.
      intuition.
      eauto.
      eauto.
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
    destruct  H_constans as [H_seller_cons [H_buyer_cons H_arbitrator_cons]].
    assert(H_EOA: address_is_contract (seller cstate) = false /\ address_is_contract (buyer cstate) = false).
    {
      eapply transition_reachable_impl_reachable in Htrc_s.
      eapply constant_addr_properties_forll in Hcs_s;eauto.
      destruct_and_split.
      eapply address_not_contract_negb in H0.
      eapply address_not_contract_negb in H1.
      eauto.
      eapply address_not_contract_negb in H0.
      eapply address_not_contract_negb in H1.
      eauto.
      eauto.
    }
    destruct H_EOA as [H_seller_eoa H_buyer_eoa].
    destruct_address_eq;try congruence.
    simpl.
    rewrite <- H_seller_cons.
    intuition.
    rewrite H_seller_eoa.
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
    assert(Hbal:env_account_balances s caddr = cstate.(depositAmount)).
    {
      eapply balance_on_chain_forall;eauto.
      unfold outgoing_acts.
      rewrite Hqueue_s.
      simpl.
      eauto.
    }
    clear H.
    destruct_address_eq;try congruence.
    + assert ((0 >? miner_reward + env_account_balances s (seller  cstate))%Z 
                = false).
      {
        unfold miner_reward.
        eapply (account_balance_nonnegative s (seller  cstate)) in Hrc_s.
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
      destruct_address_eq;try congruence.
      simpl.
      cbn .
      unfold rejectItem.
      simpl.
      rewrite Hphase_state.
      unfold require_sender.
      simpl.
      destruct_address_eq;try congruence;cbn;eauto.
    + eapply address_not_contract_negb in H_miner.
      congruence.
    + assert ((0 >? env_account_balances s (seller  cstate))%Z = false).
      {
        unfold miner_reward.
        eapply (account_balance_nonnegative s (seller  cstate)) in Hrc_s.
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
      unfold require_no_self_call.
      simpl.
      destruct_address_eq;try congruence.
      simpl.
      cbn .
      unfold rejectItem.
      simpl.
      rewrite Hphase_state.
      unfold require_sender.
      simpl.
      destruct_address_eq;try congruence;cbn;eauto.
    - 

    rewrite seller_call_RejectItem_is_call_act.
    unfold evaluate_action.
    rewrite get_valid_header_is_valid_header.
    unfold seller_call_RejectItem .
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
    unfold useller.
    assert(H_constans:cstate.(seller) = init_cstate.(seller) /\
                      cstate.(buyer) = init_cstate.(buyer) /\
                      cstate.(arbitrator) = init_cstate.(arbitrator)).
    {
      eapply transition_reachable_impl_reachable in Htrc_s.
      unfold transition_reachable in Htrc_s.
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
      eapply transition_reachable_impl_reachable_through in H.
      eapply contract_constants_reachable_through in H;eauto.
      destruct_and_split.
      rewrite H in Hcs_s.
      inversion Hcs_s.
      subst.
      intuition.
      eauto.
      eauto.
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
    destruct  H_constans as [H_seller_cons [H_buyer_cons H_arbitrator_cons]].
    assert(H_EOA: address_is_contract (seller cstate) = false /\ address_is_contract (buyer cstate) = false).
    {
      eapply transition_reachable_impl_reachable in Htrc_s.
      eapply constant_addr_properties_forll in Hcs_s;eauto.
      destruct_and_split.
      eapply address_not_contract_negb in H0.
      eapply address_not_contract_negb in H1.
      eauto.
      eapply address_not_contract_negb in H0.
      eapply address_not_contract_negb in H1.
      eauto.
      eauto.
    }
    destruct H_EOA as [H_seller_eoa H_buyer_eoa].
    destruct_address_eq;try congruence.
    simpl.
    rewrite <- H_seller_cons.
    intuition.
    rewrite H_seller_eoa.
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
    assert(Hbal:env_account_balances s caddr = cstate.(depositAmount)).
    {
      eapply balance_on_chain_forall;eauto.
      unfold outgoing_acts.
      rewrite Hqueue_s.
      simpl.
      eauto.
    }
    clear H.
    destruct_address_eq;try congruence.
    + assert ((0 >? miner_reward + env_account_balances s (seller  cstate))%Z 
                = false).
      {
        unfold miner_reward.
        eapply (account_balance_nonnegative s (seller  cstate)) in Hrc_s.
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
      destruct_address_eq;try congruence.
      simpl.
      cbn .
      unfold rejectItem.
      simpl.
      simpl.
      rewrite Hphase_state.
      simpl.
      assert (Hphase_state_true:require_phase cstate AWAITING_ACCEPTANCE || true = true).
      {
        intuition.
      }
      rewrite Hphase_state_true.
      unfold require_sender.
      simpl.
      simpl.
      destruct_address_eq;try congruence;cbn;eauto.
    + eapply address_not_contract_negb in H_miner.
      congruence.
    + assert ((0 >? env_account_balances s (seller  cstate))%Z = false).
      {
        unfold miner_reward.
        eapply (account_balance_nonnegative s (seller  cstate)) in Hrc_s.
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
      unfold require_no_self_call.
      simpl.
      destruct_address_eq;try congruence.
      simpl.
      cbn .
      unfold rejectItem.
      simpl.
      rewrite Hphase_state.
      unfold require_sender.
      simpl.
      destruct_address_eq;try congruence;cbn;eauto.
      assert (Hphase_state_true:require_phase cstate AWAITING_ACCEPTANCE || true = true).
      {
        intuition.
      }
      rewrite Hphase_state_true.
      unfold require_sender.
      simpl.
      simpl.
      destruct_address_eq;try congruence;cbn;eauto.
    - eauto.
  Qed.


  Lemma arbitrator_call_Arbitrate_transition_correct
  :
    forall (s:ChainState) cstate buyerWins,
      contract_state s caddr = Some cstate ->
      require_phase cstate DISPUTED = true ->
      transition_reachable miner contract caddr s0 s ->
      exists s', 
        transition miner s (arbitrator_call_Arbitrate cstate buyerWins) = Ok s'.
  Proof.
    intros * Hcs_s Hphase_state Htrc_s.
    unfold transition.
    unfold queue_isb_empty.
    pose proof Htrc_s.
    eapply transition_reachable_queue_is_empty in H as Hqueue_s.
    rewrite Hqueue_s.
    rewrite arbitrator_call_Arbitrate_is_call_act.
    unfold evaluate_action.
    rewrite get_valid_header_is_valid_header.
    unfold arbitrator_call_Arbitrate .
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
    unfold uarbitrator.
    assert(H_constans:cstate.(seller) = init_cstate.(seller) /\
                      cstate.(buyer) = init_cstate.(buyer) /\
                      cstate.(arbitrator) = init_cstate.(arbitrator)).
    {
      eapply transition_reachable_impl_reachable in Htrc_s.
      unfold transition_reachable in Htrc_s.
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
      eapply transition_reachable_impl_reachable_through in H.
      eapply contract_constants_reachable_through in H;eauto.
      destruct_and_split.
      rewrite H in Hcs_s.
      inversion Hcs_s.
      subst.
      intuition.
      eauto.
      eauto.
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
    clear H.
    destruct  H_constans as [H_seller_cons [H_buyer_cons H_arbitrator_cons]].
    assert(H_EOA: address_is_contract (seller cstate) = false /\
                  address_is_contract (buyer cstate) = false /\
                  address_is_contract (arbitrator cstate) = false).
    {
      eapply transition_reachable_impl_reachable in Htrc_s.
      eapply constant_addr_properties_forll in Hcs_s;eauto.
      destruct_and_split.
      eapply address_not_contract_negb in H0.
      eapply address_not_contract_negb in H.
      eauto.
      eapply address_not_contract_negb in H0.
      eapply address_not_contract_negb in H.
      eauto.
      eapply address_not_contract_negb in H1.
      eauto.
      eauto.
    }
    assert(H_addr_neq: address_neqb (cstate.(seller)) (cstate.(arbitrator)) = true
                    /\ address_neqb (cstate.(buyer)) (cstate.(arbitrator))= true
                    /\ address_neqb (cstate.(buyer)) (cstate.(seller))= true).
    {
      eapply transition_reachable_impl_reachable in Htrc_s.
      eapply constant_addr_properties_forll in Hcs_s;eauto.
      destruct_and_split.
      destruct_address_eq;eauto.
      destruct_address_eq;eauto.
      destruct_address_eq;eauto.
      eauto.
    }
    destruct H_EOA as [H_seller_eoa [H_buyer_eoa H_arbitrator_eoa]].
    destruct_address_eq;try congruence;cbn in *;simpl;eauto;destruct_and_split;try congruence.
    simpl.
    rewrite <- H_arbitrator_cons.
    intuition.
    rewrite H_arbitrator_eoa.
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
    assert(Hbal:env_account_balances s caddr = cstate.(depositAmount)).
    {
      eapply balance_on_chain_forall;eauto.
      unfold outgoing_acts.
      rewrite Hqueue_s.
      simpl.
      eauto.
    }
    clear H.
    destruct_address_eq;try congruence.
      + assert ((0 >? miner_reward + env_account_balances s (arbitrator  cstate))%Z = false).
        {
          unfold miner_reward.
          eapply (account_balance_nonnegative s (arbitrator  cstate)) in Hrc_s.
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
        destruct_address_eq;try congruence.
        simpl.
        cbn .
        unfold arbitrate.
        simpl.
        rewrite Hphase_state.
        unfold require_sender.
        simpl.
        destruct_address_eq;try congruence;cbn;eauto.
        unfold send_or_call.
        assert(depositAmount cstate <? 0 = false).
        {
          eapply (account_balance_nonnegative s caddr) in Hrc_s.
          propify.
          lia.
        }
        rewrite H2.
        simpl.
        destruct buyerWins eqn : H_eq;destruct_address_eq;try congruence.
        destruct_address_eq;try congruence;eauto.
        (* 1 *)
        assert(depositAmount cstate >? 0 + (env_account_balances s caddr) = false)%Z.
        {
          propify.
          lia.
        }
        rewrite H3.
        assert (H_sender_none: env_contracts s (buyer   cstate) = None).
        { 
          destruct (env_contracts s (buyer   cstate)) eqn:H_env.
          - exfalso.
            apply (contract_addr_format (buyer   cstate) w) in H_env; eauto.
            congruence.
          - reflexivity.
        }
        rewrite H_sender_none.
        rewrite H_buyer_eoa.
        simpl.
        eauto.
        (* 2 *)
        assert(depositAmount cstate >? 0 + (env_account_balances s caddr) = false)%Z.
        {
          propify.
          lia.
        }
        rewrite H3.
        assert (H_sender_none: env_contracts s (seller  cstate) = None).
        { 
          destruct (env_contracts s (seller  cstate)) eqn:H_env.
          - exfalso.
            apply (contract_addr_format (seller  cstate) w) in H_env; eauto.
            congruence.
          - reflexivity.
        }
        rewrite H_sender_none.
        rewrite H_seller_eoa.
        simpl.
        eauto.
      + assert ((0 >? env_account_balances s (arbitrator  cstate))%Z = false).
      {
        unfold miner_reward.
        eapply (account_balance_nonnegative s (arbitrator  cstate)) in Hrc_s.
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
      destruct_address_eq;try congruence.
      simpl.
      cbn .
      unfold arbitrate.
      simpl.
      rewrite Hphase_state.
      unfold require_sender.
      simpl.
      destruct_address_eq;try congruence;cbn;eauto.
      unfold send_or_call.
      assert(depositAmount cstate <? 0 = false).
      {
        eapply (account_balance_nonnegative s caddr) in Hrc_s.
        propify.
        lia.
      }
      rewrite H2.
      simpl.
      destruct buyerWins eqn : H_eq;destruct_address_eq;try congruence.
      destruct_address_eq;try congruence;eauto.
      (* 1 *)
      assert(depositAmount cstate >? 0 + ( miner_reward  + env_account_balances s caddr) = false)%Z.
      {
        propify.
        rewrite Hbal.
        unfold miner_reward .
        lia.
      }
      rewrite H3.
      assert (H_sender_none: env_contracts s (buyer   cstate) = None).
      { 
        destruct (env_contracts s (buyer   cstate)) eqn:H_env.
        - exfalso.
          apply (contract_addr_format (buyer   cstate) w) in H_env; eauto.
          congruence.
        - reflexivity.
      }
      rewrite H_sender_none.
      rewrite H_buyer_eoa.
      simpl.
      eauto.
      (* 2 *)
      assert(depositAmount cstate >? 0 + (miner_reward + env_account_balances s caddr) = false)%Z.
      {
      propify.
      rewrite Hbal.
      unfold miner_reward .
      lia.
      }
      rewrite H3.
      assert (H_sender_none: env_contracts s (seller  cstate) = None).
      { 
        destruct (env_contracts s (seller  cstate)) eqn:H_env.
        - exfalso.
          apply (contract_addr_format (seller  cstate) w) in H_env; eauto.
          congruence.
        - reflexivity.
      }
      rewrite H_sender_none.
      rewrite H_seller_eoa.
      simpl.
      eauto.
    + assert ((0 >? env_account_balances s (arbitrator  cstate))%Z = false).
    {
      unfold miner_reward.
      eapply (account_balance_nonnegative s (arbitrator  cstate)) in Hrc_s.
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
    destruct_address_eq;try congruence.
    simpl.
    cbn .
    unfold arbitrate.
    simpl.
    rewrite Hphase_state.
    unfold require_sender.
    simpl.
    destruct_address_eq;try congruence;cbn;eauto.
    unfold send_or_call.
    assert(depositAmount cstate <? 0 = false).
    {
      eapply (account_balance_nonnegative s caddr) in Hrc_s.
      propify.
      lia.
    }
    rewrite H2.
    simpl.
    destruct buyerWins eqn : H_eq;destruct_address_eq;try congruence.
    destruct_address_eq;try congruence;eauto.
    (* 1 *)
    assert(depositAmount cstate >? 0 + (   env_account_balances s caddr) = false)%Z.
    {
      propify.
      rewrite Hbal.
      unfold miner_reward .
      lia.
    }
    rewrite H3.
    assert (H_sender_none: env_contracts s (buyer   cstate) = None).
    { 
      destruct (env_contracts s (buyer   cstate)) eqn:H_env.
      - exfalso.
        apply (contract_addr_format (buyer   cstate) w) in H_env; eauto.
        congruence.
      - reflexivity.
    }
    rewrite H_sender_none.
    rewrite H_buyer_eoa.
    simpl.
    eauto.
    (* 2 *)
    assert(depositAmount cstate >? 0 + ( env_account_balances s caddr) = false)%Z.
    {
    propify.
    rewrite Hbal.
    unfold miner_reward .
    lia.
    }
    rewrite H3.
    assert (H_sender_none: env_contracts s (buyer   cstate) = None).
    { 
      destruct (env_contracts s (buyer   cstate)) eqn:H_env.
      - exfalso.
        apply (contract_addr_format (buyer   cstate) w) in H_env; eauto.
        congruence.
      - reflexivity.
    }
    rewrite H_sender_none.
    rewrite H_buyer_eoa.
    simpl.
    eauto.
    assert(depositAmount cstate >? 0 + ( env_account_balances s caddr) = false)%Z.
    {
    propify.
    rewrite Hbal.
    unfold miner_reward .
    lia.
    }
    rewrite H3.
    assert (H_sender_none: env_contracts s (seller    cstate) = None).
    { 
      destruct (env_contracts s (seller    cstate)) eqn:H_env.
      - exfalso.
        apply (contract_addr_format (seller    cstate) w) in H_env; eauto.
        congruence.
      - reflexivity.
    }
    rewrite H_sender_none.
    rewrite H_seller_eoa.
    simpl.
    eauto.
    assert(depositAmount cstate >? 0 + ( env_account_balances s caddr) = false)%Z.
    {
    propify.
    rewrite Hbal.
    unfold miner_reward .
    lia.
    }
    rewrite H3.
    assert (H_sender_none: env_contracts s (seller    cstate) = None).
    { 
      destruct (env_contracts s (seller    cstate)) eqn:H_env.
      - exfalso.
        apply (contract_addr_format (seller    cstate) w) in H_env; eauto.
        congruence.
      - reflexivity.
    }
    rewrite H_sender_none.
    rewrite H_seller_eoa.
    simpl.
    eauto.
  + eauto. 
  Qed.

  Lemma seller_call_MarkAsShipped_state_correct:
    forall (s s':ChainState) cstate,
      contract_state s caddr = Some cstate ->
      require_phase cstate AWAITING_SHIPMENT = true ->
      transition_reachable miner  contract caddr s0 s ->
      transition miner  s (seller_call_MarkAsShipped cstate) = Ok s' ->
      exists cstate',
        contract_state s' caddr = Some cstate' /\
        cstate'.(currentPhase) = AWAITING_ACCEPTANCE /\
        cstate'.(itemShipped) = true.
  Proof.
    intros * Hcs_s Hphase Htrc_s Htrans.
    eapply transition_reachable_queue_is_empty in Htrc_s as Hqueue_s.
    assert (Hact_call : is_call_act ((seller_call_MarkAsShipped cstate)) = true).
    {
      unfold is_call_act.
      unfold seller_call_MarkAsShipped.
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
    unfold uarbitrator.
    assert(H_constans:cstate.(seller) = init_cstate.(seller) /\
                      cstate.(buyer) = init_cstate.(buyer) /\
                      cstate.(arbitrator) = init_cstate.(arbitrator)).
    {
      eapply transition_reachable_impl_reachable in Htrc_s as Hrc_s.
      destruct_and_split.
      eapply transition_reachable_impl_reachable_through in Htrc_s as Hrrc_s;eauto.
      eapply contract_constants_reachable_through in Hrrc_s;eauto.
      destruct_and_split.
      rewrite H in Hcs_s.
      inversion Hcs_s.
      subst.
      intuition.
      eauto.
      eauto.
      eapply transition_reachable_impl_reachable_through in Htrc_s as Hrrc_s;eauto.
      eapply contract_constants_reachable_through in Hrrc_s;eauto.
      destruct_and_split.
      rewrite H in Hcs_s.
      inversion Hcs_s.
      subst.
      intuition.
      eauto.
      eauto.
      eapply transition_reachable_impl_reachable_through in Htrc_s as Hrrc_s;eauto.
      eapply contract_constants_reachable_through in Hrrc_s;eauto.
      destruct_and_split.
      rewrite H in Hcs_s.
      inversion Hcs_s.
      subst.
      intuition.
      eauto.
    }
    destruct  H_constans as [H_seller_cons [H_buyer_cons H_arbitrator_cons]].
    assert(H_EOA: address_is_contract (seller cstate) = false /\
                  address_is_contract (buyer cstate) = false /\
                  address_is_contract (arbitrator cstate) = false).
    {
      eapply transition_reachable_impl_reachable in Htrc_s.
      eapply constant_addr_properties_forll in Hcs_s;eauto.
      destruct_and_split.
      eapply address_not_contract_negb in H0.
      eapply address_not_contract_negb in H.
      eauto.
      eapply address_not_contract_negb in H0.
      eapply address_not_contract_negb in H.
      eauto.
      eapply address_not_contract_negb in H1.
      eauto.
      eauto.
    }
    assert(H_addr_neq: address_neqb (cstate.(seller)) (cstate.(arbitrator)) = true
                    /\ address_neqb (cstate.(buyer)) (cstate.(arbitrator))= true
                    /\ address_neqb (cstate.(buyer)) (cstate.(seller))= true).
    {
      eapply transition_reachable_impl_reachable in Htrc_s.
      eapply constant_addr_properties_forll in Hcs_s;eauto.
      destruct_and_split.
      destruct_address_eq;eauto.
      destruct_address_eq;eauto.
      destruct_address_eq;eauto.
      eauto.
    }
    destruct H_EOA as [H_seller_eoa [H_buyer_eoa H_arbitrator_eoa]].
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
    rewrite Hact_call in Htrans.
    destruct (evaluate_action true s (get_valid_header miner s)
    [seller_call_MarkAsShipped cstate]) eqn : H_exec;try congruence.
    unfold evaluate_action in H_exec.
    rewrite get_valid_header_is_valid_header in H_exec.
    destruct (find_origin_neq_from [seller_call_MarkAsShipped cstate]) ; try congruence.
    destruct (find_invalid_root_action [seller_call_MarkAsShipped cstate]);try congruence.
    set (mid_state := {|
      chain_state_env := add_new_block_to_env (get_valid_header miner s) s;
      chain_state_queue := [seller_call_MarkAsShipped cstate]
    |}) in H_exec.
    simpl in *.
    unfold useller in *.
    rewrite <- H_seller_cons in *.
    destruct(send_or_call (seller cstate) (seller cstate) caddr 0
    (Some (serialize MarkAsShipped))
    (add_new_block_to_env (get_valid_header miner s) s)) eqn : H_send_or_call_MarkAsShipped;try congruence.
    unfold send_or_call in  H_send_or_call_MarkAsShipped.
    simpl in H_send_or_call_MarkAsShipped.
    destruct_address_eq;simpl in *;try congruence;inversion H_addr_neq;simpl;inversion H;inversion H0;inversion H1;inversion H2.
    (* 
      e: sender cstate = miner
      n: caddr <> sender cstate
      e0: caddr = caddr
      n0: caddr <> miner 
    *)
    eapply address_not_contract_negb in H_miner.
    destruct(0 >? miner_reward + env_account_balances s (seller  cstate))%Z;try congruence.
    rewrite Hec_s in H_send_or_call_MarkAsShipped.
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
          ctx_origin := seller  cstate;
          ctx_from := seller  cstate;
          ctx_contract_address := caddr;
          ctx_contract_balance := 0 + env_account_balances s caddr;
          ctx_amount := 0
        |} s1 (Some (serialize MarkAsShipped)))) eqn : H_wc_receive_s1;try congruence.
    unfold weak_error_to_error_receive in H_wc_receive_s1.
    unfold bind_error in H_wc_receive_s1.
    destruct (wc_receive contract
    (s <| chain_height := S (chain_height s) |> <| current_slot :=
      (current_slot s + 1)%nat |> <| finalized_height :=
      finalized_height s |>)
    {|
      ctx_origin := seller  cstate;
      ctx_from := seller  cstate;
      ctx_contract_address := caddr;
      ctx_contract_balance := 0 + env_account_balances s caddr;
      ctx_amount := 0
    |} s1 (Some (serialize MarkAsShipped)))
      eqn : H_wc_receive_s1';try congruence.
    
    set (cchain := s <| chain_height := S (chain_height s) |> <| current_slot :=
    (current_slot s + 1)%nat |> <| finalized_height :=
    finalized_height s |>) in H_wc_receive_s1'.
    set (cctx := {|
    ctx_origin := seller  cstate;
    ctx_from := seller  cstate;
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
    destruct (require_zero cctx && require_no_self_call cctx) eqn : requirements_check;try congruence.
    reduce_markAsShipped.
    inversion receive_some.
    subst.
    inversion H_wc_receive_s1;subst.
    inversion H_send_or_call_MarkAsShipped;subst.
    simpl in H_exec.
    inversion H_exec.

    assert(Hreachable_through_s'_mid_mid_end_state : reachable_through s t).
    {
      assert(step_s'_mid : ChainStep s mid_state).
      {
        eapply (step_block s mid_state  (get_valid_header (seller cstate) s));eauto.
        unfold get_valid_header.
        eapply build_is_valid_next_block;simpl;intuition;eauto.
        unfold miner_reward.
        lia.
        eapply Forall_forall.
        intros.
        clear H.
        rename H0 into H.
        simpl in H3.
        destruct H3.
        rewrite <- H0.
        unfold act_is_from_account.
        simpl.
        
        unfold useller .
        intuition.
        inversion H0.
        eapply Forall_forall;eauto.
        intros.
        simpl in H3.
        destruct H3;eauto;intuition.
        clear H.
        rename H0 into H.
        rewrite <- H3.
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
      assert(step_mid_end : ChainStep mid_state t).
      {
        eapply (step_action mid_state t (seller_call_MarkAsShipped cstate) [] 
        [] )
        ;eauto.
        eapply (eval_call (seller cstate) (seller cstate) caddr 0 
          (contract:WeakContract) (Some (serialize MarkAsShipped))
          ( s1) (serialize
          (prev_state_strong <| itemShipped := true |> <| currentPhase :=
           AWAITING_ACCEPTANCE |>)) 
          []);eauto;intuition.
        eapply reachable_through_reachable in H3.

        eapply (account_balance_nonnegative mid_state (seller cstate)) in H3.
        lia.
        eauto.
        unfold seller_call_MarkAsShipped .
        unfold build_call .
        simpl.
        unfold useller.
        intuition.
        eapply build_env_equiv;eauto;intuition.
        intuition.
      }
      assert(reachable mid_state).
      {
        eapply reachable_through_reachable;eauto.
      }
      eapply reachable_through_step in H5;eauto.
    }
    inversion  Hcstate_s_t0.
    subst.
    simpl in H_exec.
    inversion H_exec;subst.
    inversion Htrans.
    subst.
    inversion Hcs_s'.
    unfold contract_state in H4.
    simpl in H4.
    destruct_address_eq;eauto.
    setoid_rewrite deserialize_serialize in H4.
    inversion H4.
    intuition.
    intuition.
    (* 
      n: sender cstate <> miner
      n0: caddr <> sender cstate
      e: caddr = caddr
      n1: caddr <> miner
    *)
    eapply address_not_contract_negb in H_miner.
    congruence.
    destruct(0 >? env_account_balances s (seller cstate))%Z eqn : H_sell_bal;try congruence.
    rewrite Hec_s in H_send_or_call_MarkAsShipped.
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
          ctx_origin := seller  cstate;
          ctx_from := seller  cstate;
          ctx_contract_address := caddr;
          ctx_contract_balance := 0 + env_account_balances s caddr;
          ctx_amount := 0
        |} s1 (Some (serialize MarkAsShipped)))) eqn : H_wc_receive_s1;try congruence.
    unfold weak_error_to_error_receive in H_wc_receive_s1.
    unfold bind_error in H_wc_receive_s1.
    destruct (wc_receive contract
    (s <| chain_height := S (chain_height s) |> <| current_slot :=
      (current_slot s + 1)%nat |> <| finalized_height :=
      finalized_height s |>)
    {|
      ctx_origin := seller  cstate;
      ctx_from := seller  cstate;
      ctx_contract_address := caddr;
      ctx_contract_balance := 0 + env_account_balances s caddr;
      ctx_amount := 0
    |} s1 (Some (serialize MarkAsShipped)))
      eqn : H_wc_receive_s1';try congruence.
    
    set (cchain := s <| chain_height := S (chain_height s) |> <| current_slot :=
    (current_slot s + 1)%nat |> <| finalized_height :=
    finalized_height s |>) in H_wc_receive_s1'.
    set (cctx := {|
    ctx_origin := seller  cstate;
    ctx_from := seller  cstate;
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
    destruct (require_zero cctx && require_no_self_call cctx) eqn : requirements_check;try congruence.
    reduce_markAsShipped.
    inversion receive_some.
    subst.
    inversion H_wc_receive_s1;subst.
    inversion H_send_or_call_MarkAsShipped;subst.
    simpl in H_exec.
    inversion H_exec.

    assert(Hreachable_through_s'_mid_mid_end_state : reachable_through s t).
    {
      assert(step_s'_mid : ChainStep s mid_state).
      {
        eapply (step_block s mid_state  (get_valid_header miner  s));eauto.
        unfold get_valid_header.
        eapply build_is_valid_next_block;simpl;intuition;eauto.
        
        eapply address_not_contract_negb;eauto.
        unfold miner_reward.
        lia.
        eapply Forall_forall.
        intros.
        clear H.
        rename H0 into H.
        simpl in H3.
        destruct H3.
        rewrite <- H0.
        unfold act_is_from_account.
        simpl.
        
        unfold useller .
        intuition.
        inversion H0.
        eapply Forall_forall;eauto.
        intros.
        simpl in H3.
        destruct H3;eauto;intuition.
        clear H.
        rename H0 into H.
        rewrite <- H3.
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
      assert(step_mid_end : ChainStep mid_state t).
      {
        eapply (step_action mid_state t (seller_call_MarkAsShipped cstate) [] 
        [] )
        ;eauto.
        eapply (eval_call (seller cstate) (seller cstate) caddr 0 
          (contract:WeakContract) (Some (serialize MarkAsShipped))
          ( s1) (serialize
          (prev_state_strong <| itemShipped := true |> <| currentPhase :=
           AWAITING_ACCEPTANCE |>)) 
          []);eauto;intuition.
        eapply reachable_through_reachable in H3.

        eapply (account_balance_nonnegative mid_state (seller cstate)) in H3.
        lia.
        eauto.
        unfold seller_call_MarkAsShipped .
        unfold build_call .
        simpl.
        unfold useller.
        intuition.
        eapply build_env_equiv;eauto;intuition.
        intuition.
      }
      assert(reachable mid_state).
      {
        eapply reachable_through_reachable;eauto.
      }
      eapply reachable_through_step in H5;eauto.
    }
    inversion  Hcstate_s_t0.
    subst.
    simpl in H_exec.
    inversion H_exec;subst.
    inversion Htrans.
    subst.
    inversion Hcs_s'.
    unfold contract_state in H4.
    simpl in H4.
    destruct_address_eq;eauto.
    setoid_rewrite deserialize_serialize in H4.
    inversion H4.
    intuition.
    intuition.
    eauto.
  Qed.

  Lemma buyer_call_AcceptItem_state_correct:
  forall (s s':ChainState) cstate,
    contract_state s caddr = Some cstate ->
    require_phase cstate AWAITING_ACCEPTANCE = true ->
    transition_reachable miner  contract caddr s0 s ->
    transition miner  s (buyer_call_AcceptItem cstate) = Ok s' ->
    exists cstate',
      contract_state s' caddr = Some cstate' /\
      cstate'.(currentPhase) = COMPLETED /\
      cstate'.(itemAccepted) = true /\
      cstate'.(depositAmount) = 0.
  Proof.
    intros * Hcs_s Hphase Htrc_s Htrans.
    eapply transition_reachable_queue_is_empty in Htrc_s as Hqueue_s.
    assert (Hact_call : is_call_act ((buyer_call_AcceptItem cstate)) = true).
    {
      unfold is_call_act.
      unfold buyer_call_AcceptItem.
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
    unfold uarbitrator.
    assert(H_constans:cstate.(seller) = init_cstate.(seller) /\
                      cstate.(buyer) = init_cstate.(buyer) /\
                      cstate.(arbitrator) = init_cstate.(arbitrator)).
    {
      eapply transition_reachable_impl_reachable in Htrc_s as Hrc_s.
      destruct_and_split.
      eapply transition_reachable_impl_reachable_through in Htrc_s as Hrrc_s;eauto.
      eapply contract_constants_reachable_through in Hrrc_s;eauto.
      destruct_and_split.
      rewrite H in Hcs_s.
      inversion Hcs_s.
      subst.
      intuition.
      eauto.
      eauto.
      eapply transition_reachable_impl_reachable_through in Htrc_s as Hrrc_s;eauto.
      eapply contract_constants_reachable_through in Hrrc_s;eauto.
      destruct_and_split.
      rewrite H in Hcs_s.
      inversion Hcs_s.
      subst.
      intuition.
      eauto.
      eauto.
      eapply transition_reachable_impl_reachable_through in Htrc_s as Hrrc_s;eauto.
      eapply contract_constants_reachable_through in Hrrc_s;eauto.
      destruct_and_split.
      rewrite H in Hcs_s.
      inversion Hcs_s.
      subst.
      intuition.
      eauto.
    }
    destruct  H_constans as [H_seller_cons [H_buyer_cons H_arbitrator_cons]].
    assert(H_EOA: address_is_contract (seller cstate) = false /\
                  address_is_contract (buyer cstate) = false /\
                  address_is_contract (arbitrator cstate) = false).
    {
      eapply transition_reachable_impl_reachable in Htrc_s.
      eapply constant_addr_properties_forll in Hcs_s;eauto.
      destruct_and_split.
      eapply address_not_contract_negb in H0.
      eapply address_not_contract_negb in H.
      eauto.
      eapply address_not_contract_negb in H0.
      eapply address_not_contract_negb in H.
      eauto.
      eapply address_not_contract_negb in H1.
      eauto.
      eauto.
    }
    assert(H_addr_neq: address_neqb (cstate.(seller)) (cstate.(arbitrator)) = true
                    /\ address_neqb (cstate.(buyer)) (cstate.(arbitrator))= true
                    /\ address_neqb (cstate.(buyer)) (cstate.(seller))= true).
    {
      eapply transition_reachable_impl_reachable in Htrc_s.
      eapply constant_addr_properties_forll in Hcs_s;eauto.
      destruct_and_split.
      destruct_address_eq;eauto.
      destruct_address_eq;eauto.
      destruct_address_eq;eauto.
      eauto.
    }
    destruct H_EOA as [H_seller_eoa [H_buyer_eoa H_arbitrator_eoa]].
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
    rewrite Hact_call in Htrans.
    destruct (evaluate_action true s (get_valid_header miner s)
    [buyer_call_AcceptItem cstate ]) eqn : H_exec;try congruence.
    unfold evaluate_action in H_exec.
    rewrite get_valid_header_is_valid_header in H_exec.
    destruct (find_origin_neq_from [buyer_call_AcceptItem cstate]) ; try congruence.
    destruct (find_invalid_root_action [buyer_call_AcceptItem cstate]);try congruence.
    set (mid_state := {|
      chain_state_env := add_new_block_to_env (get_valid_header miner s) s;
      chain_state_queue := [buyer_call_AcceptItem cstate]
    |}) in H_exec.
    simpl in *.
    unfold ubuyer in *.
    rewrite <- H_buyer_cons in *.
    destruct(send_or_call (buyer cstate) (buyer cstate) caddr 0
    (Some (serialize AcceptItem))
    (add_new_block_to_env (get_valid_header miner s) s)) eqn : H_send_or_call_AcceptItem;try congruence.
    unfold send_or_call in  H_send_or_call_AcceptItem.
    simpl in H_send_or_call_AcceptItem.
    destruct_address_eq;simpl in *;try congruence;inversion H_addr_neq;simpl;inversion H;inversion H0;inversion H1;inversion H2.
    (* 
      e: sender cstate = miner
      n: caddr <> sender cstate
      e0: caddr = caddr
      n0: caddr <> miner 
    *)
    eapply address_not_contract_negb in H_miner.
    destruct(0 >? miner_reward + env_account_balances s (buyer cstate))%Z;try congruence.
    rewrite Hec_s in H_send_or_call_AcceptItem.
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
          ctx_origin := buyer cstate;
          ctx_from := buyer cstate;
          ctx_contract_address := caddr;
          ctx_contract_balance := 0 + env_account_balances s caddr;
          ctx_amount := 0
        |} s1 (Some (serialize AcceptItem)))) eqn : H_wc_receive_s1;try congruence.
    unfold weak_error_to_error_receive in H_wc_receive_s1.
    unfold bind_error in H_wc_receive_s1.
    destruct (wc_receive contract
    (s <| chain_height := S (chain_height s) |> <| current_slot :=
      (current_slot s + 1)%nat |> <| finalized_height :=
      finalized_height s |>)
    {|
      ctx_origin := buyer cstate;
      ctx_from := buyer cstate;
      ctx_contract_address := caddr;
      ctx_contract_balance := 0 + env_account_balances s caddr;
      ctx_amount := 0
    |} s1 (Some (serialize AcceptItem)))
      eqn : H_wc_receive_s1';try congruence.
    
    set (cchain := s <| chain_height := S (chain_height s) |> <| current_slot :=
    (current_slot s + 1)%nat |> <| finalized_height :=
    finalized_height s |>) in H_wc_receive_s1'.
    set (cctx := {|
    ctx_origin := buyer cstate;
    ctx_from := buyer cstate;
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
    destruct (require_zero cctx && require_no_self_call cctx) eqn : requirements_check;try congruence.
    reduce_acceptItem.
    inversion receive_some.
    subst.
    inversion H_wc_receive_s1;subst.
    inversion H_send_or_call_AcceptItem;subst.
    simpl in H_exec.
    destruct (  send_or_call (buyer cstate) caddr (seller prev_state_strong)
    (depositAmount prev_state_strong) None
    (set_contract_state caddr
       (serialize
          (prev_state_strong <| itemAccepted := true |> <| currentPhase :=
           COMPLETED |> <| depositAmount := 0 |>))
       (transfer_balance (buyer cstate) caddr 0
          (add_new_block_to_env (get_valid_header (buyer cstate) s) s)))) eqn : H_send_or_call_None;try congruence.
    unfold send_or_call in H_send_or_call_None.
    destruct_match in H_send_or_call_None;try congruence.
    destruct_match in H_send_or_call_None;try congruence.
    destruct (
      env_contracts
      (set_contract_state caddr
         (serialize
            (prev_state_strong <| itemAccepted := true |> <|
             currentPhase := COMPLETED |> <| depositAmount := 0 |>))
         (transfer_balance (buyer cstate) caddr 0
            (add_new_block_to_env
               (get_valid_header (buyer cstate) s) s)))
      (seller prev_state_strong) ) 
    eqn : H_none_wc.
    set (
        mid_env:=(set_contract_state caddr
          (serialize (prev_state_strong <| itemAccepted := true |> <|
             currentPhase := COMPLETED |> <| depositAmount := 0 |>))
          (transfer_balance (buyer cstate) caddr 0
              (add_new_block_to_env (get_valid_header (buyer cstate) s) s)))) 
    in H_none_wc.
    set (
      mid_mid_end_state := {|
      chain_state_env :=
      mid_env;
      chain_state_queue :=
        [{|
            act_origin := buyer cstate;
            act_from := caddr;
            act_body :=
              act_transfer (seller prev_state_strong)
                (depositAmount prev_state_strong)
          |}]
      |}
    ).
    assert(Hreachable_through_s'_mid_mid_end_state : reachable_through s mid_mid_end_state).
    {
      assert(step_s'_mid : ChainStep s mid_state).
      {
        eapply (step_block s mid_state  (get_valid_header (buyer cstate) s));eauto.
        unfold get_valid_header.
        eapply build_is_valid_next_block;simpl;intuition;eauto.
        unfold miner_reward.
        lia.
        eapply Forall_forall.
        intros.
        simpl in H3.
        destruct H3.
        rewrite <- H3.
        unfold act_is_from_account.
        simpl.
        unfold ubuyer.
        intuition.
        intuition.
        eapply Forall_forall;eauto.
        intros.
        simpl in H3.
        destruct H3;eauto;intuition.
        rewrite <- H3.
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
        eapply (step_action mid_state mid_mid_end_state (buyer_call_AcceptItem cstate) [] 
        [{|
          act_origin := buyer cstate;
          act_from := caddr;
          act_body :=
            act_transfer (seller prev_state_strong)
              (depositAmount prev_state_strong)
        |}] )
        ;eauto.
        eapply (eval_call (buyer cstate) (buyer cstate) caddr 0 
          (contract:WeakContract) (Some (serialize AcceptItem))
          ( s1) (serialize (prev_state_strong <| itemAccepted := true |> <|
                currentPhase := COMPLETED |> <| depositAmount := 0
                |>)) 
          [act_transfer (seller prev_state_strong) (depositAmount prev_state_strong)]);eauto;intuition.
        eapply reachable_through_reachable in H3.
        eapply (account_balance_nonnegative mid_state (buyer cstate)) in H3.
        lia.
        eauto.
        unfold buyer_call_AcceptItem.
        unfold build_call.
        intuition.
        eapply build_env_equiv;eauto.
      }
      assert(reachable mid_state).
      {
        eapply reachable_through_reachable;eauto.
      }
      eapply reachable_through_step in H4;eauto.
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
    eapply (address_not_contract_not_wc (seller prev_state_strong)) in Hreachable_mid_mid.
    intuition.
    intuition.
    inversion  Hcstate_s_t0.
    rewrite H4 in H_send_or_call_None.
    rewrite H_seller_eoa in H_send_or_call_None.
    inversion H_send_or_call_None;subst.
    simpl in H_exec.
    inversion H_exec;subst.
    inversion Htrans.
    subst.
    inversion Hcs_s'.
    unfold contract_state in H4.
    simpl in H4.
    destruct_address_eq;eauto.
    setoid_rewrite deserialize_serialize in H4.
    inversion H4.
    intuition.
    simpl.
    eauto.
    intuition.
    (* caddr = miner *)
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
    destruct(0 >?  env_account_balances s (buyer cstate))%Z;try congruence.
    rewrite Hec_s in H_send_or_call_AcceptItem.
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
          ctx_origin := buyer cstate;
          ctx_from := buyer cstate;
          ctx_contract_address := caddr;
          ctx_contract_balance := 0 + env_account_balances s caddr;
          ctx_amount := 0
        |} s1 (Some (serialize AcceptItem)))) eqn : H_wc_receive_s1;try congruence.
    unfold weak_error_to_error_receive in H_wc_receive_s1.
    unfold bind_error in H_wc_receive_s1.
    destruct (wc_receive contract
    (s <| chain_height := S (chain_height s) |> <| current_slot :=
      (current_slot s + 1)%nat |> <| finalized_height :=
      finalized_height s |>)
    {|
      ctx_origin := buyer cstate;
      ctx_from := buyer cstate;
      ctx_contract_address := caddr;
      ctx_contract_balance := 0 + env_account_balances s caddr;
      ctx_amount := 0
    |} s1 (Some (serialize AcceptItem)))
      eqn : H_wc_receive_s1';try congruence.
    
    set (cchain := s <| chain_height := S (chain_height s) |> <| current_slot :=
    (current_slot s + 1)%nat |> <| finalized_height :=
    finalized_height s |>) in H_wc_receive_s1'.
    set (cctx := {|
    ctx_origin := buyer cstate;
    ctx_from := buyer cstate;
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
    destruct (require_zero cctx && require_no_self_call cctx) eqn : requirements_check;try congruence.
    reduce_acceptItem.
    inversion receive_some.
    subst.
    inversion H_wc_receive_s1;subst.
    inversion H_send_or_call_AcceptItem;subst.
    simpl in H_exec.
    destruct (  send_or_call (buyer cstate) caddr (seller prev_state_strong)
    (depositAmount prev_state_strong) None
    (set_contract_state caddr
       (serialize
          (prev_state_strong <| itemAccepted := true |> <| currentPhase :=
           COMPLETED |> <| depositAmount := 0 |>))
       (transfer_balance (buyer cstate) caddr 0
          (add_new_block_to_env (get_valid_header miner s) s)))) eqn : H_send_or_call_None;try congruence.
    unfold send_or_call in H_send_or_call_None.
    destruct_match in H_send_or_call_None;try congruence.
    destruct_match in H_send_or_call_None;try congruence.
    destruct (
      env_contracts
      (set_contract_state caddr
         (serialize
            (prev_state_strong <| itemAccepted := true |> <|
             currentPhase := COMPLETED |> <| depositAmount := 0 |>))
         (transfer_balance (buyer cstate) caddr 0
            (add_new_block_to_env
               (get_valid_header miner s) s)))
      (seller prev_state_strong) ) 
    eqn : H_none_wc.
    set (
        mid_env:=(set_contract_state caddr
          (serialize (prev_state_strong <| itemAccepted := true |> <|
             currentPhase := COMPLETED |> <| depositAmount := 0 |>))
          (transfer_balance (buyer cstate) caddr 0
              (add_new_block_to_env (get_valid_header miner s) s)))) 
    in H_none_wc.
    set (
      mid_mid_end_state := {|
      chain_state_env :=
      mid_env;
      chain_state_queue :=
        [{|
            act_origin := buyer cstate;
            act_from := caddr;
            act_body :=
              act_transfer (seller prev_state_strong)
                (depositAmount prev_state_strong)
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
        simpl in H3.
        destruct H3.
        rewrite <- H3.
        unfold act_is_from_account.
        simpl.
        unfold ubuyer.
        intuition.
        intuition.
        eapply Forall_forall;eauto.
        intros.
        simpl in H3.
        destruct H3;eauto;intuition.
        rewrite <- H3.
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
        eapply (step_action mid_state mid_mid_end_state (buyer_call_AcceptItem cstate) [] 
        [{|
          act_origin := buyer cstate;
          act_from := caddr;
          act_body :=
            act_transfer (seller prev_state_strong)
              (depositAmount prev_state_strong)
        |}] )
        ;eauto.
        eapply (eval_call (buyer cstate) (buyer cstate) caddr 0 
          (contract:WeakContract) (Some (serialize AcceptItem))
          ( s1) (serialize (prev_state_strong <| itemAccepted := true |> <|
                currentPhase := COMPLETED |> <| depositAmount := 0
                |>)) 
          [act_transfer (seller prev_state_strong) (depositAmount prev_state_strong)]);eauto;intuition.
        eapply reachable_through_reachable in H3.
        eapply (account_balance_nonnegative mid_state (buyer cstate)) in H3.
        lia.
        eauto.
        unfold buyer_call_AcceptItem.
        unfold build_call.
        intuition.
        eapply build_env_equiv;eauto.
      }
      assert(reachable mid_state).
      {
        eapply reachable_through_reachable;eauto.
      }
      eapply reachable_through_step in H4;eauto.
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
    eapply (address_not_contract_not_wc (seller prev_state_strong)) in Hreachable_mid_mid.
    intuition.
    intuition.
    inversion  Hcstate_s_t0.
    rewrite H4 in H_send_or_call_None.
    rewrite H_seller_eoa in H_send_or_call_None.
    inversion H_send_or_call_None;subst.
    simpl in H_exec.
    inversion H_exec;subst.
    inversion Htrans.
    subst.
    inversion Hcs_s'.
    unfold contract_state in H4.
    simpl in H4.
    destruct_address_eq;eauto.
    setoid_rewrite deserialize_serialize in H4.
    inversion H4.
    intuition.
    simpl.
    eauto.
    intuition.
    eauto.
  Qed.

  Lemma buyer_call_RejectItem_state_correct:
  forall (s s':ChainState) cstate,
    contract_state s caddr = Some cstate ->
    (require_phase cstate AWAITING_ACCEPTANCE = true \/
      require_phase cstate AWAITING_SHIPMENT = true )->
    transition_reachable miner contract caddr s0 s ->
    transition miner s (buyer_call_RejectItem cstate) = Ok s' ->
    exists cstate',
      contract_state s' caddr = Some cstate' /\
      cstate'.(currentPhase) = DISPUTED.
  Proof.
    intros * Hcs_s Hphase Htrc_s Htrans.
    eapply transition_reachable_queue_is_empty in Htrc_s as Hqueue_s.
    assert (Hact_call : is_call_act ((buyer_call_RejectItem cstate)) = true).
    {
      unfold is_call_act.
      unfold buyer_call_RejectItem.
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
    unfold uarbitrator.
    assert(H_constans:cstate.(seller) = init_cstate.(seller) /\
                      cstate.(buyer) = init_cstate.(buyer) /\
                      cstate.(arbitrator) = init_cstate.(arbitrator)).
    {
      eapply transition_reachable_impl_reachable in Htrc_s as Hrc_s.
      destruct_and_split.
      eapply transition_reachable_impl_reachable_through in Htrc_s as Hrrc_s;eauto.
      eapply contract_constants_reachable_through in Hrrc_s;eauto.
      destruct_and_split.
      rewrite H in Hcs_s.
      inversion Hcs_s.
      subst.
      intuition.
      eauto.
      eauto.
      eapply transition_reachable_impl_reachable_through in Htrc_s as Hrrc_s;eauto.
      eapply contract_constants_reachable_through in Hrrc_s;eauto.
      destruct_and_split.
      rewrite H in Hcs_s.
      inversion Hcs_s.
      subst.
      intuition.
      eauto.
      eauto.
      eapply transition_reachable_impl_reachable_through in Htrc_s as Hrrc_s;eauto.
      eapply contract_constants_reachable_through in Hrrc_s;eauto.
      destruct_and_split.
      rewrite H in Hcs_s.
      inversion Hcs_s.
      subst.
      intuition.
      eauto.
    }
    destruct  H_constans as [H_seller_cons [H_buyer_cons H_arbitrator_cons]].
    assert(H_EOA: address_is_contract (seller cstate) = false /\
                  address_is_contract (buyer cstate) = false /\
                  address_is_contract (arbitrator cstate) = false).
    {
      eapply transition_reachable_impl_reachable in Htrc_s.
      eapply constant_addr_properties_forll in Hcs_s;eauto.
      destruct_and_split.
      eapply address_not_contract_negb in H0.
      eapply address_not_contract_negb in H.
      eauto.
      eapply address_not_contract_negb in H0.
      eapply address_not_contract_negb in H.
      eauto.
      eapply address_not_contract_negb in H1.
      eauto.
      eauto.
    }
    assert(H_addr_neq: address_neqb (cstate.(seller)) (cstate.(arbitrator)) = true
                    /\ address_neqb (cstate.(buyer)) (cstate.(arbitrator))= true
                    /\ address_neqb (cstate.(buyer)) (cstate.(seller))= true).
    {
      eapply transition_reachable_impl_reachable in Htrc_s.
      eapply constant_addr_properties_forll in Hcs_s;eauto.
      destruct_and_split.
      destruct_address_eq;eauto.
      destruct_address_eq;eauto.
      destruct_address_eq;eauto.
      eauto.
    }
    destruct H_EOA as [H_seller_eoa [H_buyer_eoa H_arbitrator_eoa]].
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
    rewrite Hact_call in Htrans.
    destruct (evaluate_action true s (get_valid_header miner s)
    [buyer_call_RejectItem cstate]) eqn : H_exec;try congruence.
    unfold evaluate_action in H_exec.
    rewrite get_valid_header_is_valid_header in H_exec.
    destruct (find_origin_neq_from [buyer_call_RejectItem cstate]) ; try congruence.
    destruct (find_invalid_root_action [buyer_call_RejectItem cstate]);try congruence.
    set (mid_state := {|
      chain_state_env := add_new_block_to_env (get_valid_header miner s) s;
      chain_state_queue := [buyer_call_RejectItem cstate]
    |}) in H_exec.
    simpl in *.
    unfold ubuyer in *.
    rewrite <- H_buyer_cons in *.
    destruct(send_or_call (buyer cstate) (buyer cstate) caddr 0
    (Some (serialize RejectItem))
    (add_new_block_to_env (get_valid_header miner s) s)) eqn : H_send_or_call_RejectItem;try congruence.
    unfold send_or_call in  H_send_or_call_RejectItem.
    simpl in H_send_or_call_RejectItem.
    destruct_address_eq;simpl in *;try congruence;inversion H_addr_neq;simpl;inversion H;inversion H0;inversion H1;inversion H2.
    (* 
      e: sender cstate = miner
      n: caddr <> sender cstate
      e0: caddr = caddr
      n0: caddr <> miner 
    *)
    eapply address_not_contract_negb in H_miner.
    destruct(0 >? miner_reward + env_account_balances s (buyer  cstate))%Z;try congruence.
    rewrite Hec_s in H_send_or_call_RejectItem.
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
          ctx_origin := buyer  cstate;
          ctx_from := buyer  cstate;
          ctx_contract_address := caddr;
          ctx_contract_balance := 0 + env_account_balances s caddr;
          ctx_amount := 0
        |} s1 (Some (serialize RejectItem)))) eqn : H_wc_receive_s1;try congruence.
    unfold weak_error_to_error_receive in H_wc_receive_s1.
    unfold bind_error in H_wc_receive_s1.
    destruct (wc_receive contract
    (s <| chain_height := S (chain_height s) |> <| current_slot :=
      (current_slot s + 1)%nat |> <| finalized_height :=
      finalized_height s |>)
    {|
      ctx_origin := buyer  cstate;
      ctx_from := buyer  cstate;
      ctx_contract_address := caddr;
      ctx_contract_balance := 0 + env_account_balances s caddr;
      ctx_amount := 0
    |} s1 (Some (serialize RejectItem)))
      eqn : H_wc_receive_s1';try congruence.
    
    set (cchain := s <| chain_height := S (chain_height s) |> <| current_slot :=
    (current_slot s + 1)%nat |> <| finalized_height :=
    finalized_height s |>) in H_wc_receive_s1'.
    set (cctx := {|
    ctx_origin := buyer  cstate;
    ctx_from := buyer  cstate;
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
    destruct (require_zero cctx && require_no_self_call cctx) eqn : requirements_check;try congruence.
    reduce_rejectItem.
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
    unfold contract_state in H4.
    simpl in H4.
    destruct_address_eq;eauto.
    setoid_rewrite deserialize_serialize in H4.
    inversion H4.
    intuition.
    intuition.
    (* caddr = miner *)
    eapply address_not_contract_negb in H_miner.
    congruence.
    (* 
      n: sender cstate <> miner
      n0: caddr <> sender cstate
      e: caddr = caddr
      n1: caddr <> miner
    *)
    
    eapply address_not_contract_negb in H_miner.
    destruct(0 >? env_account_balances s (buyer  cstate))%Z;try congruence.
    rewrite Hec_s in H_send_or_call_RejectItem.
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
          ctx_origin := buyer  cstate;
          ctx_from := buyer  cstate;
          ctx_contract_address := caddr;
          ctx_contract_balance := 0 + env_account_balances s caddr;
          ctx_amount := 0
        |} s1 (Some (serialize RejectItem)))) eqn : H_wc_receive_s1;try congruence.
    unfold weak_error_to_error_receive in H_wc_receive_s1.
    unfold bind_error in H_wc_receive_s1.
    destruct (wc_receive contract
    (s <| chain_height := S (chain_height s) |> <| current_slot :=
      (current_slot s + 1)%nat |> <| finalized_height :=
      finalized_height s |>)
    {|
      ctx_origin := buyer  cstate;
      ctx_from := buyer  cstate;
      ctx_contract_address := caddr;
      ctx_contract_balance := 0 + env_account_balances s caddr;
      ctx_amount := 0
    |} s1 (Some (serialize RejectItem)))
      eqn : H_wc_receive_s1';try congruence.
    
    set (cchain := s <| chain_height := S (chain_height s) |> <| current_slot :=
    (current_slot s + 1)%nat |> <| finalized_height :=
    finalized_height s |>) in H_wc_receive_s1'.
    set (cctx := {|
    ctx_origin := buyer  cstate;
    ctx_from := buyer  cstate;
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
    destruct (require_zero cctx && require_no_self_call cctx) eqn : requirements_check;try congruence.
    reduce_rejectItem.
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
    unfold contract_state in H4.
    simpl in H4.
    destruct_address_eq;eauto.
    setoid_rewrite deserialize_serialize in H4.
    inversion H4.
    intuition.
    intuition.
    eauto.
  Qed.

  Lemma seller_call_RejectItem_state_correct:
    forall (s s':ChainState) cstate,
      contract_state s caddr = Some cstate ->
      (require_phase cstate AWAITING_ACCEPTANCE = true \/
        require_phase cstate AWAITING_SHIPMENT = true )->
      transition_reachable miner contract caddr s0 s ->
      transition miner s (seller_call_RejectItem cstate) = Ok s' ->
      exists cstate',
        contract_state s' caddr = Some cstate' /\
        cstate'.(currentPhase) = DISPUTED.
  Proof.
    intros * Hcs_s Hphase Htrc_s Htrans.
    eapply transition_reachable_queue_is_empty in Htrc_s as Hqueue_s.
    assert (Hact_call : is_call_act ((seller_call_RejectItem cstate)) = true).
    {
      unfold is_call_act.
      unfold seller_call_RejectItem.
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
    unfold uarbitrator.
    assert(H_constans:cstate.(seller) = init_cstate.(seller) /\
                      cstate.(buyer) = init_cstate.(buyer) /\
                      cstate.(arbitrator) = init_cstate.(arbitrator)).
    {
      eapply transition_reachable_impl_reachable in Htrc_s as Hrc_s.
      destruct_and_split.
      eapply transition_reachable_impl_reachable_through in Htrc_s as Hrrc_s;eauto.
      eapply contract_constants_reachable_through in Hrrc_s;eauto.
      destruct_and_split.
      rewrite H in Hcs_s.
      inversion Hcs_s.
      subst.
      intuition.
      eauto.
      eauto.
      eapply transition_reachable_impl_reachable_through in Htrc_s as Hrrc_s;eauto.
      eapply contract_constants_reachable_through in Hrrc_s;eauto.
      destruct_and_split.
      rewrite H in Hcs_s.
      inversion Hcs_s.
      subst.
      intuition.
      eauto.
      eauto.
      eapply transition_reachable_impl_reachable_through in Htrc_s as Hrrc_s;eauto.
      eapply contract_constants_reachable_through in Hrrc_s;eauto.
      destruct_and_split.
      rewrite H in Hcs_s.
      inversion Hcs_s.
      subst.
      intuition.
      eauto.
    }
    destruct  H_constans as [H_seller_cons [H_buyer_cons H_arbitrator_cons]].
    assert(H_EOA: address_is_contract (seller cstate) = false /\
                  address_is_contract (buyer cstate) = false /\
                  address_is_contract (arbitrator cstate) = false).
    {
      eapply transition_reachable_impl_reachable in Htrc_s.
      eapply constant_addr_properties_forll in Hcs_s;eauto.
      destruct_and_split.
      eapply address_not_contract_negb in H0.
      eapply address_not_contract_negb in H.
      eauto.
      eapply address_not_contract_negb in H0.
      eapply address_not_contract_negb in H.
      eauto.
      eapply address_not_contract_negb in H1.
      eauto.
      eauto.
    }
    assert(H_addr_neq: address_neqb (cstate.(seller)) (cstate.(arbitrator)) = true
                    /\ address_neqb (cstate.(buyer)) (cstate.(arbitrator))= true
                    /\ address_neqb (cstate.(buyer)) (cstate.(seller))= true).
    {
      eapply transition_reachable_impl_reachable in Htrc_s.
      eapply constant_addr_properties_forll in Hcs_s;eauto.
      destruct_and_split.
      destruct_address_eq;eauto.
      destruct_address_eq;eauto.
      destruct_address_eq;eauto.
      eauto.
    }
    destruct H_EOA as [H_seller_eoa [H_buyer_eoa H_arbitrator_eoa]].
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
    rewrite Hact_call in Htrans.
    destruct (evaluate_action true s (get_valid_header miner s)
    [seller_call_RejectItem cstate]) eqn : H_exec;try congruence.
    unfold evaluate_action in H_exec.
    rewrite get_valid_header_is_valid_header in H_exec.
    destruct (find_origin_neq_from [seller_call_RejectItem cstate]) ; try congruence.
    destruct (find_invalid_root_action [seller_call_RejectItem cstate]);try congruence.
    set (mid_state := {|
      chain_state_env := add_new_block_to_env (get_valid_header miner s) s;
      chain_state_queue := [buyer_call_RejectItem cstate]
    |}) in H_exec.
    simpl in *.
    unfold useller in *.
    rewrite <- H_seller_cons in *.
    destruct(send_or_call (seller cstate) (seller cstate) caddr 0
    (Some (serialize RejectItem))
    (add_new_block_to_env (get_valid_header miner s) s)) eqn : H_send_or_call_RejectItem;try congruence.
    unfold send_or_call in  H_send_or_call_RejectItem.
    simpl in H_send_or_call_RejectItem.
    destruct_address_eq;simpl in *;try congruence;inversion H_addr_neq;simpl;inversion H;inversion H0;inversion H1;inversion H2.
    (* 
      e: sender cstate = miner
      n: caddr <> sender cstate
      e0: caddr = caddr
      n0: caddr <> miner 
    *)
    eapply address_not_contract_negb in H_miner.
    destruct(0 >? miner_reward + env_account_balances s (seller  cstate))%Z;try congruence.
    rewrite Hec_s in H_send_or_call_RejectItem.
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
          ctx_origin := seller  cstate;
          ctx_from := seller  cstate;
          ctx_contract_address := caddr;
          ctx_contract_balance := 0 + env_account_balances s caddr;
          ctx_amount := 0
        |} s1 (Some (serialize RejectItem)))) eqn : H_wc_receive_s1;try congruence.
    unfold weak_error_to_error_receive in H_wc_receive_s1.
    unfold bind_error in H_wc_receive_s1.
    destruct (wc_receive contract
    (s <| chain_height := S (chain_height s) |> <| current_slot :=
      (current_slot s + 1)%nat |> <| finalized_height :=
      finalized_height s |>)
    {|
      ctx_origin := seller  cstate;
      ctx_from := seller  cstate;
      ctx_contract_address := caddr;
      ctx_contract_balance := 0 + env_account_balances s caddr;
      ctx_amount := 0
    |} s1 (Some (serialize RejectItem)))
      eqn : H_wc_receive_s1';try congruence.
    
    set (cchain := s <| chain_height := S (chain_height s) |> <| current_slot :=
    (current_slot s + 1)%nat |> <| finalized_height :=
    finalized_height s |>) in H_wc_receive_s1'.
    set (cctx := {|
    ctx_origin := seller  cstate;
    ctx_from := seller  cstate;
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
    destruct (require_zero cctx && require_no_self_call cctx) eqn : requirements_check;try congruence.
    reduce_rejectItem.
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
    unfold contract_state in H4.
    simpl in H4.
    destruct_address_eq;eauto.
    setoid_rewrite deserialize_serialize in H4.
    inversion H4.
    intuition.
    intuition.
    (* caddr = miner *)
    eapply address_not_contract_negb in H_miner.
    congruence.
    (* 
      n: sender cstate <> miner
      n0: caddr <> sender cstate
      e: caddr = caddr
      n1: caddr <> miner
    *)
    
    eapply address_not_contract_negb in H_miner.
    destruct(0 >? env_account_balances s (seller  cstate))%Z;try congruence.
    rewrite Hec_s in H_send_or_call_RejectItem.
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
          ctx_origin := seller  cstate;
          ctx_from := seller  cstate;
          ctx_contract_address := caddr;
          ctx_contract_balance := 0 + env_account_balances s caddr;
          ctx_amount := 0
        |} s1 (Some (serialize RejectItem)))) eqn : H_wc_receive_s1;try congruence.
    unfold weak_error_to_error_receive in H_wc_receive_s1.
    unfold bind_error in H_wc_receive_s1.
    destruct (wc_receive contract
    (s <| chain_height := S (chain_height s) |> <| current_slot :=
      (current_slot s + 1)%nat |> <| finalized_height :=
      finalized_height s |>)
    {|
      ctx_origin := seller  cstate;
      ctx_from := seller  cstate;
      ctx_contract_address := caddr;
      ctx_contract_balance := 0 + env_account_balances s caddr;
      ctx_amount := 0
    |} s1 (Some (serialize RejectItem)))
      eqn : H_wc_receive_s1';try congruence.
    
    set (cchain := s <| chain_height := S (chain_height s) |> <| current_slot :=
    (current_slot s + 1)%nat |> <| finalized_height :=
    finalized_height s |>) in H_wc_receive_s1'.
    set (cctx := {|
    ctx_origin := seller  cstate;
    ctx_from := seller  cstate;
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
    destruct (require_zero cctx && require_no_self_call cctx) eqn : requirements_check;try congruence.
    reduce_rejectItem.
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
    unfold contract_state in H4.
    simpl in H4.
    destruct_address_eq;eauto.
    setoid_rewrite deserialize_serialize in H4.
    inversion H4.
    intuition.
    intuition.
    eauto.
  Qed.

  Lemma arbitrator_call_Arbitrate_state_correct:
    forall (s s':ChainState) cstate buyerWins,
      contract_state s caddr = Some cstate ->
      require_phase cstate DISPUTED = true ->
      transition_reachable miner contract caddr s0 s ->
      transition miner s (arbitrator_call_Arbitrate cstate buyerWins) = Ok s' ->
      exists cstate',
        contract_state s' caddr = Some cstate' /\
        cstate'.(currentPhase) = COMPLETED /\
        cstate'.(depositAmount) = 0.
  Proof.
    intros * Hcs_s Hphase Htrc_s Htrans.
    eapply transition_reachable_queue_is_empty in Htrc_s as Hqueue_s.
    assert (Hact_call : is_call_act ((arbitrator_call_Arbitrate cstate buyerWins)) = true).
    {
      unfold is_call_act.
      unfold arbitrator_call_Arbitrate.
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
    unfold uarbitrator.
    assert(H_constans:cstate.(seller) = init_cstate.(seller) /\
                      cstate.(buyer) = init_cstate.(buyer) /\
                      cstate.(arbitrator) = init_cstate.(arbitrator)).
    {
      eapply transition_reachable_impl_reachable in Htrc_s as Hrc_s.
      destruct_and_split.
      eapply transition_reachable_impl_reachable_through in Htrc_s as Hrrc_s;eauto.
      eapply contract_constants_reachable_through in Hrrc_s;eauto.
      destruct_and_split.
      rewrite H in Hcs_s.
      inversion Hcs_s.
      subst.
      intuition.
      eauto.
      eauto.
      eapply transition_reachable_impl_reachable_through in Htrc_s as Hrrc_s;eauto.
      eapply contract_constants_reachable_through in Hrrc_s;eauto.
      destruct_and_split.
      rewrite H in Hcs_s.
      inversion Hcs_s.
      subst.
      intuition.
      eauto.
      eauto.
      eapply transition_reachable_impl_reachable_through in Htrc_s as Hrrc_s;eauto.
      eapply contract_constants_reachable_through in Hrrc_s;eauto.
      destruct_and_split.
      rewrite H in Hcs_s.
      inversion Hcs_s.
      subst.
      intuition.
      eauto.
    }
    destruct  H_constans as [H_seller_cons [H_buyer_cons H_arbitrator_cons]].
    assert(H_EOA: address_is_contract (seller cstate) = false /\
                  address_is_contract (buyer cstate) = false /\
                  address_is_contract (arbitrator cstate) = false).
    {
      eapply transition_reachable_impl_reachable in Htrc_s.
      eapply constant_addr_properties_forll in Hcs_s;eauto.
      destruct_and_split.
      eapply address_not_contract_negb in H0.
      eapply address_not_contract_negb in H.
      eauto.
      eapply address_not_contract_negb in H0.
      eapply address_not_contract_negb in H.
      eauto.
      eapply address_not_contract_negb in H1.
      eauto.
      eauto.
    }
    assert(H_addr_neq: address_neqb (cstate.(seller)) (cstate.(arbitrator)) = true
                    /\ address_neqb (cstate.(buyer)) (cstate.(arbitrator))= true
                    /\ address_neqb (cstate.(buyer)) (cstate.(seller))= true).
    {
      eapply transition_reachable_impl_reachable in Htrc_s.
      eapply constant_addr_properties_forll in Hcs_s;eauto.
      destruct_and_split.
      destruct_address_eq;eauto.
      destruct_address_eq;eauto.
      destruct_address_eq;eauto.
      eauto.
    }
    destruct H_EOA as [H_seller_eoa [H_buyer_eoa H_arbitrator_eoa]].
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
    destruct buyerWins.
    + 
      unfold transition in Htrans.
      unfold queue_isb_empty in Htrans.
      rewrite Hqueue_s in Htrans.
      rewrite Hact_call in Htrans.
      destruct (evaluate_action true s (get_valid_header miner s)
      [arbitrator_call_Arbitrate cstate true ]) eqn : H_exec;try congruence.
      unfold evaluate_action in H_exec.
      rewrite get_valid_header_is_valid_header in H_exec.
      destruct (find_origin_neq_from [arbitrator_call_Arbitrate cstate true]) ; try congruence.
      destruct (find_invalid_root_action [arbitrator_call_Arbitrate cstate true]);try congruence.
      set (mid_state := {|
        chain_state_env := add_new_block_to_env (get_valid_header miner s) s;
        chain_state_queue := [arbitrator_call_Arbitrate cstate true]
      |}) in H_exec.
      simpl in *.
      unfold uarbitrator in *.
      rewrite <- H_arbitrator_cons in *.
      destruct(send_or_call (arbitrator cstate) (arbitrator cstate) caddr 0
      (Some (serialize (Arbitrate true)))
      (add_new_block_to_env (get_valid_header miner s) s)) eqn : H_send_or_call_Arbitrate;try congruence.
      unfold send_or_call in  H_send_or_call_Arbitrate.
      simpl in H_send_or_call_Arbitrate.
      destruct_address_eq;simpl in *;try congruence;inversion H_addr_neq;simpl;inversion H;inversion H0;inversion H1;inversion H2.
      (* 
        e: sender cstate = miner
        n: caddr <> sender cstate
        e0: caddr = caddr
        n0: caddr <> miner 
      *)
      eapply address_not_contract_negb in H_miner.
      destruct(0 >? miner_reward + env_account_balances s (arbitrator cstate))%Z;try congruence.
      rewrite Hec_s in H_send_or_call_Arbitrate.
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
            ctx_origin := arbitrator cstate;
            ctx_from := arbitrator cstate;
            ctx_contract_address := caddr;
            ctx_contract_balance := 0 + env_account_balances s caddr;
            ctx_amount := 0
          |} s1 (Some (serialize (Arbitrate true))))) eqn : H_wc_receive_s1;try congruence.
      unfold weak_error_to_error_receive in H_wc_receive_s1.
      unfold bind_error in H_wc_receive_s1.
      destruct (wc_receive contract
      (s <| chain_height := S (chain_height s) |> <| current_slot :=
        (current_slot s + 1)%nat |> <| finalized_height :=
        finalized_height s |>)
      {|
        ctx_origin := arbitrator cstate;
        ctx_from := arbitrator cstate;
        ctx_contract_address := caddr;
        ctx_contract_balance := 0 + env_account_balances s caddr;
        ctx_amount := 0
      |} s1 (Some (serialize (Arbitrate true))))
        eqn : H_wc_receive_s1';try congruence.
      
      set (cchain := s <| chain_height := S (chain_height s) |> <| current_slot :=
      (current_slot s + 1)%nat |> <| finalized_height :=
      finalized_height s |>) in H_wc_receive_s1'.
      set (cctx := {|
      ctx_origin := arbitrator cstate;
      ctx_from := arbitrator cstate;
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
      destruct (require_zero cctx && require_no_self_call cctx) eqn : requirements_check;try congruence.
      reduce_arbitrate.
      inversion receive_some.
      subst.
      inversion H_wc_receive_s1;subst.
      inversion H_send_or_call_Arbitrate;subst.
      simpl in H_exec.
      destruct (  send_or_call (arbitrator cstate) caddr (buyer prev_state_strong)
      (depositAmount prev_state_strong) None
      (set_contract_state caddr
        (serialize
            (prev_state_strong <| currentPhase := COMPLETED |> <| depositAmount := 0
            |>))
        (transfer_balance (arbitrator cstate) caddr 0
            (add_new_block_to_env (get_valid_header (arbitrator cstate) s) s)))) eqn : H_send_or_call_None;try congruence.
      unfold send_or_call in H_send_or_call_None.
      destruct_match in H_send_or_call_None;try congruence.
      destruct_match in H_send_or_call_None;try congruence.
      destruct (env_contracts
      (set_contract_state caddr
        (serialize
            (prev_state_strong <| currentPhase := COMPLETED |> <|
            depositAmount := 0 |>))
        (transfer_balance (arbitrator cstate) caddr 0
            (add_new_block_to_env
              (get_valid_header (arbitrator cstate) s) s)))
      (buyer prev_state_strong)) 
      eqn : H_none_wc.
      set (
          mid_env:=(set_contract_state caddr
          (serialize
            (prev_state_strong <| currentPhase := COMPLETED |> <|
            depositAmount := 0 |>))
          (transfer_balance (arbitrator cstate) caddr 0
            (add_new_block_to_env
                (get_valid_header (arbitrator cstate) s) s)))) 
      in H_none_wc.
      set (
        mid_mid_end_state := {|
        chain_state_env :=
        mid_env;
        chain_state_queue :=
          [{|
              act_origin := arbitrator cstate;
              act_from := caddr;
              act_body :=
                act_transfer (buyer  prev_state_strong)
                  (depositAmount prev_state_strong)
            |}]
        |}
      ).
      assert(Hreachable_through_s'_mid_mid_end_state : reachable_through s mid_mid_end_state).
      {
        assert(step_s'_mid : ChainStep s mid_state).
        {
          eapply (step_block s mid_state  (get_valid_header (arbitrator cstate) s));eauto.
          unfold get_valid_header.
          eapply build_is_valid_next_block;simpl;intuition;eauto.
          unfold miner_reward.
          lia.
          eapply Forall_forall.
          intros.
          simpl in H3.
          destruct H3.
          rewrite <- H3.
          unfold act_is_from_account.
          simpl.
          unfold uarbitrator.
          intuition.
          intuition.
          eapply Forall_forall;eauto.
          intros.
          simpl in H3.
          destruct H3;eauto;intuition.
          rewrite <- H3.
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
          eapply (step_action mid_state mid_mid_end_state (arbitrator_call_Arbitrate cstate true) [] 
          [{|
            act_origin := arbitrator cstate;
            act_from := caddr;
            act_body :=
              act_transfer (buyer   prev_state_strong)
                (depositAmount prev_state_strong)
          |}] )
          ;eauto.
          eapply (eval_call (arbitrator cstate) (arbitrator cstate) caddr 0 
            (contract:WeakContract) (Some (serialize (Arbitrate true)))
            ( s1) (serialize (prev_state_strong <| currentPhase := COMPLETED
            |> <| depositAmount := 0 |>)) 
            [act_transfer (buyer prev_state_strong) (depositAmount prev_state_strong)]);eauto;intuition.
          eapply reachable_through_reachable in H3.
          eapply (account_balance_nonnegative mid_state (arbitrator  cstate)) in H3.
          lia.
          eauto.
          unfold arbitrator_call_Arbitrate .
          unfold build_call.
          intuition.
          simpl.
          intuition.
          eapply build_env_equiv;eauto.
        }
        assert(reachable mid_state).
        {
          eapply reachable_through_reachable;eauto.
        }
        eapply reachable_through_step in H4;eauto.
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
      eapply (address_not_contract_not_wc (buyer  prev_state_strong)) in Hreachable_mid_mid.
      intuition.
      intuition.
      inversion  Hcstate_s_t0.
      rewrite H4 in H_send_or_call_None.
      rewrite H_buyer_eoa in H_send_or_call_None.
      inversion H_send_or_call_None;subst.
      simpl in H_exec.
      inversion H_exec;subst.
      inversion Htrans.
      subst.
      inversion Hcs_s'.
      unfold contract_state in H4.
      simpl in H4.
      destruct_address_eq;eauto.
      setoid_rewrite deserialize_serialize in H4.
      inversion H4.
      intuition.
      simpl.
      eauto.
      intuition.
      (* caddr = miner *)
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
      destruct(0 >? env_account_balances s (arbitrator cstate))%Z;try congruence.
      rewrite Hec_s in H_send_or_call_Arbitrate.
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
            ctx_origin := arbitrator cstate;
            ctx_from := arbitrator cstate;
            ctx_contract_address := caddr;
            ctx_contract_balance := 0 + env_account_balances s caddr;
            ctx_amount := 0
          |} s1 (Some (serialize (Arbitrate true))))) eqn : H_wc_receive_s1;try congruence.
      unfold weak_error_to_error_receive in H_wc_receive_s1.
      unfold bind_error in H_wc_receive_s1.
      destruct (wc_receive contract
      (s <| chain_height := S (chain_height s) |> <| current_slot :=
        (current_slot s + 1)%nat |> <| finalized_height :=
        finalized_height s |>)
      {|
        ctx_origin := arbitrator cstate;
        ctx_from := arbitrator cstate;
        ctx_contract_address := caddr;
        ctx_contract_balance := 0 + env_account_balances s caddr;
        ctx_amount := 0
      |} s1 (Some (serialize (Arbitrate true))))
        eqn : H_wc_receive_s1';try congruence.
      
      set (cchain := s <| chain_height := S (chain_height s) |> <| current_slot :=
      (current_slot s + 1)%nat |> <| finalized_height :=
      finalized_height s |>) in H_wc_receive_s1'.
      set (cctx := {|
      ctx_origin := arbitrator cstate;
      ctx_from := arbitrator cstate;
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
      destruct (require_zero cctx && require_no_self_call cctx) eqn : requirements_check;try congruence.
      reduce_arbitrate.
      inversion receive_some.
      subst.
      inversion H_wc_receive_s1;subst.
      inversion H_send_or_call_Arbitrate;subst.
      simpl in H_exec.
      destruct ( send_or_call (arbitrator cstate) caddr (buyer prev_state_strong)
      (depositAmount prev_state_strong) None
      (set_contract_state caddr
        (serialize
            (prev_state_strong <| currentPhase := COMPLETED |> <| depositAmount := 0
            |>))
        (transfer_balance (arbitrator cstate) caddr 0
            (add_new_block_to_env (get_valid_header miner s) s)))) eqn : H_send_or_call_None;try congruence.
      unfold send_or_call in H_send_or_call_None.
      destruct_match in H_send_or_call_None;try congruence.
      destruct_match in H_send_or_call_None;try congruence.
      destruct (env_contracts
      (set_contract_state caddr
        (serialize
            (prev_state_strong <| currentPhase := COMPLETED |> <| depositAmount := 0
            |>))
        (transfer_balance (arbitrator cstate) caddr 0
            (add_new_block_to_env (get_valid_header miner s) s)))
      (buyer prev_state_strong)) 
      eqn : H_none_wc.
      set (
          mid_env:=(set_contract_state caddr
          (serialize
            (prev_state_strong <| currentPhase := COMPLETED |> <|
            depositAmount := 0 |>))
          (transfer_balance (arbitrator cstate) caddr 0
            (add_new_block_to_env
            (get_valid_header miner s) s)))) 
      in H_none_wc.
      set (
        mid_mid_end_state := {|
        chain_state_env :=
        mid_env;
        chain_state_queue :=
          [{|
              act_origin := arbitrator cstate;
              act_from := caddr;
              act_body :=
                act_transfer (buyer  prev_state_strong)
                  (depositAmount prev_state_strong)
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
          simpl in H3.
          destruct H3.
          rewrite <- H3.
          unfold act_is_from_account.
          simpl.
          unfold uarbitrator.
          intuition.
          intuition.
          eapply Forall_forall;eauto.
          intros.
          simpl in H3.
          destruct H3;eauto;intuition.
          rewrite <- H3.
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
          eapply (step_action mid_state mid_mid_end_state (arbitrator_call_Arbitrate cstate true) [] 
          [{|
            act_origin := arbitrator cstate;
            act_from := caddr;
            act_body :=
              act_transfer (buyer   prev_state_strong)
                (depositAmount prev_state_strong)
          |}] )
          ;eauto.
          eapply (eval_call (arbitrator cstate) (arbitrator cstate) caddr 0 
            (contract:WeakContract) (Some (serialize (Arbitrate true)))
            ( s1) (serialize (prev_state_strong <| currentPhase := COMPLETED
            |> <| depositAmount := 0 |>)) 
            [act_transfer (buyer prev_state_strong) (depositAmount prev_state_strong)]);eauto;intuition.
          eapply reachable_through_reachable in H3.
          eapply (account_balance_nonnegative mid_state (arbitrator  cstate)) in H3.
          lia.
          eauto.
          unfold arbitrator_call_Arbitrate .
          unfold build_call.
          intuition.
          simpl.
          intuition.
          eapply build_env_equiv;eauto.
        }
        assert(reachable mid_state).
        {
          eapply reachable_through_reachable;eauto.
        }
        eapply reachable_through_step in H4;eauto.
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
      eapply (address_not_contract_not_wc (buyer  prev_state_strong)) in Hreachable_mid_mid.
      intuition.
      intuition.
      inversion  Hcstate_s_t0.
      rewrite H4 in H_send_or_call_None.
      rewrite H_buyer_eoa in H_send_or_call_None.
      inversion H_send_or_call_None;subst.
      simpl in H_exec.
      inversion H_exec;subst.
      inversion Htrans.
      subst.
      inversion Hcs_s'.
      unfold contract_state in H4.
      simpl in H4.
      destruct_address_eq;eauto.
      setoid_rewrite deserialize_serialize in H4.
      inversion H4.
      intuition.
      simpl.
      eauto.
      intuition.
    + 
      unfold transition in Htrans.
      unfold queue_isb_empty in Htrans.
      rewrite Hqueue_s in Htrans.
      rewrite Hact_call in Htrans.
      destruct (evaluate_action true s (get_valid_header miner s)
      [arbitrator_call_Arbitrate cstate false ]) eqn : H_exec;try congruence.
      unfold evaluate_action in H_exec.
      rewrite get_valid_header_is_valid_header in H_exec.
      destruct (find_origin_neq_from [arbitrator_call_Arbitrate cstate false]) ; try congruence.
      destruct (find_invalid_root_action [arbitrator_call_Arbitrate cstate false]);try congruence.
      set (mid_state := {|
        chain_state_env := add_new_block_to_env (get_valid_header miner s) s;
        chain_state_queue := [arbitrator_call_Arbitrate cstate false]
      |}) in H_exec.
      simpl in *.
      unfold uarbitrator in *.
      rewrite <- H_arbitrator_cons in *.
      destruct(send_or_call (arbitrator cstate) (arbitrator cstate) caddr 0
      (Some (serialize (Arbitrate false)))
      (add_new_block_to_env (get_valid_header miner s) s)) eqn : H_send_or_call_Arbitrate;try congruence.
      unfold send_or_call in  H_send_or_call_Arbitrate.
      simpl in H_send_or_call_Arbitrate.
      destruct_address_eq;simpl in *;try congruence;inversion H_addr_neq;simpl;inversion H;inversion H0;inversion H1;inversion H2.
      (* 
        arbitrator cstate = miner
      *)
      eapply address_not_contract_negb in H_miner.
      destruct(0 >? miner_reward + env_account_balances s (arbitrator cstate))%Z;try congruence.
      rewrite Hec_s in H_send_or_call_Arbitrate.
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
            ctx_origin := arbitrator cstate;
            ctx_from := arbitrator cstate;
            ctx_contract_address := caddr;
            ctx_contract_balance := 0 + env_account_balances s caddr;
            ctx_amount := 0
          |} s1 (Some (serialize (Arbitrate false))))) eqn : H_wc_receive_s1;try congruence.
      unfold weak_error_to_error_receive in H_wc_receive_s1.
      unfold bind_error in H_wc_receive_s1.
      destruct (wc_receive contract
      (s <| chain_height := S (chain_height s) |> <| current_slot :=
        (current_slot s + 1)%nat |> <| finalized_height :=
        finalized_height s |>)
      {|
        ctx_origin := arbitrator cstate;
        ctx_from := arbitrator cstate;
        ctx_contract_address := caddr;
        ctx_contract_balance := 0 + env_account_balances s caddr;
        ctx_amount := 0
      |} s1 (Some (serialize (Arbitrate false))))
        eqn : H_wc_receive_s1';try congruence.
      
      set (cchain := s <| chain_height := S (chain_height s) |> <| current_slot :=
      (current_slot s + 1)%nat |> <| finalized_height :=
      finalized_height s |>) in H_wc_receive_s1'.
      set (cctx := {|
      ctx_origin := arbitrator cstate;
      ctx_from := arbitrator cstate;
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
      destruct (require_zero cctx && require_no_self_call cctx) eqn : requirements_check;try congruence.
      reduce_arbitrate.
      inversion receive_some.
      subst.
      inversion H_wc_receive_s1;subst.
      inversion H_send_or_call_Arbitrate;subst.
      simpl in H_exec.
      destruct (  send_or_call (arbitrator cstate) caddr (seller prev_state_strong)
      (depositAmount prev_state_strong) None
      (set_contract_state caddr
        (serialize
            (prev_state_strong <| currentPhase := COMPLETED |> <| depositAmount := 0
            |>))
        (transfer_balance (arbitrator cstate) caddr 0
            (add_new_block_to_env (get_valid_header (arbitrator cstate) s) s)))) eqn : H_send_or_call_None;try congruence.
      unfold send_or_call in H_send_or_call_None.
      destruct_match in H_send_or_call_None;try congruence.
      destruct_match in H_send_or_call_None;try congruence.
      destruct (env_contracts
      (set_contract_state caddr
         (serialize
            (prev_state_strong <| currentPhase := COMPLETED |> <|
            depositAmount := 0 |>))
         (transfer_balance (arbitrator cstate) caddr 0
            (add_new_block_to_env
               (get_valid_header (arbitrator cstate) s) s)))
      (seller prev_state_strong)) 
      eqn : H_none_wc.
      set (
          mid_env:=(set_contract_state caddr
          (serialize
             (prev_state_strong <| currentPhase := COMPLETED |> <|
             depositAmount := 0 |>))
          (transfer_balance (arbitrator cstate) caddr 0
             (add_new_block_to_env
                (get_valid_header (arbitrator cstate) s) s)))) 
      in H_none_wc.
      set (
        mid_mid_end_state := {|
        chain_state_env :=
        mid_env;
        chain_state_queue :=
          [{|
              act_origin := arbitrator cstate;
              act_from := caddr;
              act_body :=
                act_transfer (seller  prev_state_strong)
                  (depositAmount prev_state_strong)
            |}]
        |}
      ).
      assert(Hreachable_through_s'_mid_mid_end_state : reachable_through s mid_mid_end_state).
      {
        assert(step_s'_mid : ChainStep s mid_state).
        {
          eapply (step_block s mid_state  (get_valid_header (arbitrator cstate) s));eauto.
          unfold get_valid_header.
          eapply build_is_valid_next_block;simpl;intuition;eauto.
          unfold miner_reward.
          lia.
          eapply Forall_forall.
          intros.
          simpl in H3.
          destruct H3.
          rewrite <- H3.
          unfold act_is_from_account.
          simpl.
          unfold uarbitrator.
          intuition.
          intuition.
          eapply Forall_forall;eauto.
          intros.
          simpl in H3.
          destruct H3;eauto;intuition.
          rewrite <- H3.
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
          eapply (step_action mid_state mid_mid_end_state (arbitrator_call_Arbitrate cstate false) [] 
          [{|
            act_origin := arbitrator cstate;
            act_from := caddr;
            act_body :=
              act_transfer (seller prev_state_strong)
                (depositAmount prev_state_strong)
          |}] )
          ;eauto.
          eapply (eval_call (arbitrator cstate) (arbitrator cstate) caddr 0 
            (contract:WeakContract) (Some (serialize (Arbitrate false)))
            ( s1) (serialize (prev_state_strong <| currentPhase := COMPLETED
            |> <| depositAmount := 0 |>)) 
            [act_transfer (seller prev_state_strong) (depositAmount prev_state_strong)]);eauto;intuition.
          eapply reachable_through_reachable in H3.
          eapply (account_balance_nonnegative mid_state (arbitrator  cstate)) in H3.
          lia.
          eauto.
          unfold arbitrator_call_Arbitrate .
          unfold build_call.
          intuition.
          simpl.
          intuition.
          eapply build_env_equiv;eauto.
        }
        assert(reachable mid_state).
        {
          eapply reachable_through_reachable;eauto.
        }
        eapply reachable_through_step in H4;eauto.
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
      eapply (address_not_contract_not_wc (seller  prev_state_strong)) in Hreachable_mid_mid.
      intuition.
      intuition.
      inversion  Hcstate_s_t0.
      rewrite H4 in H_send_or_call_None.
      rewrite H_seller_eoa in H_send_or_call_None.
      inversion H_send_or_call_None;subst.
      simpl in H_exec.
      inversion H_exec;subst.
      inversion Htrans.
      subst.
      inversion Hcs_s'.
      unfold contract_state in H4.
      simpl in H4.
      destruct_address_eq;eauto.
      setoid_rewrite deserialize_serialize in H4.
      inversion H4.
      intuition.
      simpl.
      eauto.
      intuition.
      (* caddr = miner *)
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
      destruct(0 >? env_account_balances s (arbitrator cstate))%Z;try congruence.
      rewrite Hec_s in H_send_or_call_Arbitrate.
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
            ctx_origin := arbitrator cstate;
            ctx_from := arbitrator cstate;
            ctx_contract_address := caddr;
            ctx_contract_balance := 0 + env_account_balances s caddr;
            ctx_amount := 0
          |} s1 (Some (serialize (Arbitrate false))))) eqn : H_wc_receive_s1;try congruence.
      unfold weak_error_to_error_receive in H_wc_receive_s1.
      unfold bind_error in H_wc_receive_s1.
      destruct (wc_receive contract
      (s <| chain_height := S (chain_height s) |> <| current_slot :=
        (current_slot s + 1)%nat |> <| finalized_height :=
        finalized_height s |>)
      {|
        ctx_origin := arbitrator cstate;
        ctx_from := arbitrator cstate;
        ctx_contract_address := caddr;
        ctx_contract_balance := 0 + env_account_balances s caddr;
        ctx_amount := 0
      |} s1 (Some (serialize (Arbitrate false))))
        eqn : H_wc_receive_s1';try congruence.
      
      set (cchain := s <| chain_height := S (chain_height s) |> <| current_slot :=
      (current_slot s + 1)%nat |> <| finalized_height :=
      finalized_height s |>) in H_wc_receive_s1'.
      set (cctx := {|
      ctx_origin := arbitrator cstate;
      ctx_from := arbitrator cstate;
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
      destruct (require_zero cctx && require_no_self_call cctx) eqn : requirements_check;try congruence.
      reduce_arbitrate.
      inversion receive_some.
      subst.
      inversion H_wc_receive_s1;subst.
      inversion H_send_or_call_Arbitrate;subst.
      simpl in H_exec.
      destruct (send_or_call (arbitrator cstate) caddr (seller prev_state_strong)
      (depositAmount prev_state_strong) None
      (set_contract_state caddr
         (serialize
            (prev_state_strong <| currentPhase := COMPLETED |> <| depositAmount := 0
             |>))
         (transfer_balance (arbitrator cstate) caddr 0
            (add_new_block_to_env (get_valid_header miner s) s)))) eqn : H_send_or_call_None;try congruence.
      unfold send_or_call in H_send_or_call_None.
      destruct_match in H_send_or_call_None;try congruence.
      destruct_match in H_send_or_call_None;try congruence.
      destruct ( env_contracts
      (set_contract_state caddr
         (serialize
            (prev_state_strong <| currentPhase := COMPLETED |> <|
            depositAmount := 0 |>))
         (transfer_balance (arbitrator cstate) caddr 0
            (add_new_block_to_env (get_valid_header miner s) s)))
      (seller prev_state_strong)) 
      eqn : H_none_wc.
      set (
          mid_env:=(set_contract_state caddr
          (serialize
             (prev_state_strong <| currentPhase := COMPLETED |> <|
             depositAmount := 0 |>))
          (transfer_balance (arbitrator cstate) caddr 0
             (add_new_block_to_env (get_valid_header miner s) s)))) 
      in H_none_wc.
      set (
        mid_mid_end_state := {|
        chain_state_env :=
        mid_env;
        chain_state_queue :=
          [{|
              act_origin := arbitrator cstate;
              act_from := caddr;
              act_body :=
                act_transfer (seller  prev_state_strong)
                  (depositAmount prev_state_strong)
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
          simpl in H3.
          destruct H3.
          rewrite <- H3.
          unfold act_is_from_account.
          simpl.
          unfold uarbitrator.
          intuition.
          intuition.
          eapply Forall_forall;eauto.
          intros.
          simpl in H3.
          destruct H3;eauto;intuition.
          rewrite <- H3.
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
          eapply (step_action mid_state mid_mid_end_state (arbitrator_call_Arbitrate cstate false) [] 
          [{|
            act_origin := arbitrator cstate;
            act_from := caddr;
            act_body :=
              act_transfer (seller prev_state_strong)
                (depositAmount prev_state_strong)
          |}] )
          ;eauto.
          eapply (eval_call (arbitrator cstate) (arbitrator cstate) caddr 0 
            (contract:WeakContract) (Some (serialize (Arbitrate false)))
            ( s1) (serialize (prev_state_strong <| currentPhase := COMPLETED
            |> <| depositAmount := 0 |>)) 
            [act_transfer (seller prev_state_strong) (depositAmount prev_state_strong)]);eauto;intuition.
          eapply reachable_through_reachable in H3.
          eapply (account_balance_nonnegative mid_state (arbitrator  cstate)) in H3.
          lia.
          eauto.
          unfold arbitrator_call_Arbitrate .
          unfold build_call.
          intuition.
          simpl.
          intuition.
          eapply build_env_equiv;eauto.
        }
        assert(reachable mid_state).
        {
          eapply reachable_through_reachable;eauto.
        }
        eapply reachable_through_step in H4;eauto.
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
      eapply (address_not_contract_not_wc (seller  prev_state_strong)) in Hreachable_mid_mid.
      intuition.
      intuition.
      inversion  Hcstate_s_t0.
      rewrite H4 in H_send_or_call_None.
      rewrite H_seller_eoa in H_send_or_call_None.
      inversion H_send_or_call_None;subst.
      simpl in H_exec.
      inversion H_exec;subst.
      inversion Htrans.
      subst.
      inversion Hcs_s'.
      unfold contract_state in H4.
      simpl in H4.
      destruct_address_eq;eauto.
      setoid_rewrite deserialize_serialize in H4.
      inversion H4.
      intuition.
      simpl.
      eauto.
      intuition.
    + eauto.
  Qed.

  Lemma escrow_satisfy_base_liqudity:
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
    clear H0.
    eapply transition_reachable_queue_is_empty in Htrc_s as Hqueue_s.
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
    assert(H_constans:cstate.(seller) = init_cstate.(seller) /\
                      cstate.(buyer) = init_cstate.(buyer) /\
                      cstate.(arbitrator) = init_cstate.(arbitrator)).
    {
      eapply transition_reachable_impl_reachable in Htrc_s as Hrc_s.
      destruct_and_split.
      eapply transition_reachable_impl_reachable_through in Htrc_s as Hrrc_s;eauto.
      eapply contract_constants_reachable_through in Hrrc_s;eauto.
      destruct_and_split.
      rewrite H in Hcs_s.
      inversion Hcs_s.
      subst.
      intuition.
      eauto.
      eauto.
      eapply transition_reachable_impl_reachable_through in Htrc_s as Hrrc_s;eauto.
      eapply contract_constants_reachable_through in Hrrc_s;eauto.
      destruct_and_split.
      rewrite H in Hcs_s.
      inversion Hcs_s.
      subst.
      intuition.
      eauto.
      eauto.
      eapply transition_reachable_impl_reachable_through in Htrc_s as Hrrc_s;eauto.
      eapply contract_constants_reachable_through in Hrrc_s;eauto.
      destruct_and_split.
      rewrite H in Hcs_s.
      inversion Hcs_s.
      subst.
      intuition.
      eauto.
    }
    assert(Hdeployed : env_contracts s caddr = Some (contract: WeakContract)).
    {
      eapply reachable_through_contract_deployed;eauto.
    }
    destruct  H_constans as [H_seller_cons [H_buyer_cons H_arbitrator_cons]].
    assert(H_EOA: address_is_contract (seller cstate) = false /\
                  address_is_contract (buyer cstate) = false /\
                  address_is_contract (arbitrator cstate) = false).
    {
      eapply transition_reachable_impl_reachable in Htrc_s.
      eapply constant_addr_properties_forll in Hcs_s;eauto.
      destruct_and_split.
      eapply address_not_contract_negb in H0.
      eapply address_not_contract_negb in H.
      eauto.
      eapply address_not_contract_negb in H0.
      eapply address_not_contract_negb in H.
      eauto.
      eapply address_not_contract_negb in H1.
      eauto.
      eauto.
    }
    assert(H_addr_neq: address_neqb (cstate.(seller)) (cstate.(arbitrator)) = true
                    /\ address_neqb (cstate.(buyer)) (cstate.(arbitrator))= true
                    /\ address_neqb (cstate.(buyer)) (cstate.(seller))= true).
    {
      eapply transition_reachable_impl_reachable in Htrc_s.
      eapply constant_addr_properties_forll in Hcs_s;eauto.
      destruct_and_split.
      destruct_address_eq;eauto.
      destruct_address_eq;eauto.
      destruct_address_eq;eauto.
      eauto.
    }
    destruct H_EOA as [H_seller_eoa [H_buyer_eoa H_arbitrator_eoa]].
    assert( H_caddr_not_EOA : address_is_contract caddr = true).
    {
      eapply contract_addr_format in Hdeployed.
      eauto.
      eapply transition_reachable_impl_reachable in Htrc_s;eauto.
    }
    destruct (cstate.(currentPhase)) eqn : HcurrentPhase.
    - pose proof Htrc_s.
      eapply buyer_call_RejectItem_transition_correct in H;eauto.
      destruct H as [s' Htrans].
      pose proof Htrans.
      eapply buyer_call_RejectItem_state_correct in  H;eauto.
      destruct H as [cstate' [Hcs_s' HPhase]].
      assert (transition_reachable miner contract caddr s0 s').
      {
        
        decompose_transition_reachable Htrc_s.
        assert (TransitionTrace miner s0 s').
        assert(is_call_act (buyer_call_RejectItem cstate) = true).
        {
          eapply (buyer_call_AcceptItem_is_call_act cstate).
        }
        eapply (snoc trace (step_trans miner (buyer_call_RejectItem cstate) H  Htrans)).
        econstructor;eauto.
      }
      assert (trace_s_s' :inhabited(TransitionTrace miner s s')).
      {
        decompose_transition_reachable Htrc_s.
        assert (TransitionTrace miner s s) by eapply clnil.
        assert(is_call_act (buyer_call_RejectItem cstate) = true).
        {
          eapply (buyer_call_AcceptItem_is_call_act cstate).
        }
        econstructor;eauto.
        eapply (snoc X (step_trans miner (buyer_call_RejectItem cstate) H0  Htrans)).
      }
      pose proof H.
      eapply (arbitrator_call_Arbitrate_transition_correct
       s' cstate' true)in H;eauto.
      destruct H as [s'' Htrans'].
      pose proof Htrans'.
      eapply arbitrator_call_Arbitrate_state_correct in H;eauto.
      destruct H as [cstate'' [Hcs_s'' [HPhase' Hbal ]]].
      assert (Hready':transition_reachable miner contract caddr s0 s'').
      {
        decompose_transition_reachable H0.
        assert (TransitionTrace miner s0 s'').
        assert(is_call_act (arbitrator_call_Arbitrate cstate' true) = true).
        {
          eapply (buyer_call_AcceptItem_is_call_act cstate' ).
        }
        eapply (snoc trace (step_trans miner (arbitrator_call_Arbitrate cstate' true) H  Htrans')).
        econstructor;eauto.
      }
      assert (trace_s_s'' :inhabited(TransitionTrace miner s s'')).
      {
        decompose_transition_reachable Hready'.
        
        assert(is_call_act (arbitrator_call_Arbitrate cstate' true) = true).
        {
          eapply (buyer_call_AcceptItem_is_call_act cstate' ).
        }
        destruct trace_s_s' as [trace_s_s'].
        econstructor;eauto.
        eapply (snoc trace_s_s' (step_trans miner (arbitrator_call_Arbitrate cstate' true) H  Htrans')).
      }
      pose proof Hready'.
      eapply transition_reachable_impl_reachable in H.
      eapply balance_on_chain_forall in Hcs_s'';eauto.
      exists s''.
      split.
      eauto.
      unfold funds.
      intuition.
      eapply transition_reachable_impl_reachable_through in Hready';eauto.
      eapply reachable_through_contract_deployed in Hready';eauto.
      unfold outgoing_acts.
      eapply transition_reachable_queue_is_empty in Hready'.
      rewrite Hready'.
      intuition.
      eauto.
      eauto.
      unfold require_phase.
      rewrite HPhase;eauto.
      unfold require_phase.
      rewrite HPhase;eauto.
      right.
      unfold require_phase.
      rewrite HcurrentPhase;eauto.
      right.
      unfold require_phase.
      rewrite HcurrentPhase;eauto.
    - pose proof Htrc_s.
      eapply buyer_call_AcceptItem_transition_correct in H;eauto.
      destruct H as [s' Htrans].
      pose proof Htrans.
      eapply buyer_call_AcceptItem_state_correct in  H;eauto.
      destruct H as [cstate' [Hcs_s' HPhase]].
      assert (transition_reachable miner contract caddr s0 s').
      {
        destruct_and_split.
        decompose_transition_reachable Htrc_s.
        assert (TransitionTrace miner s0 s').
        assert(is_call_act (buyer_call_AcceptItem cstate) = true).
        {
          eapply (buyer_call_AcceptItem_is_call_act cstate).
        }
        eapply (snoc trace (step_trans miner (buyer_call_AcceptItem cstate) H5  Htrans)).
        econstructor;eauto.
      }
      assert (trace_s_s' :inhabited(TransitionTrace miner s s')).
      {
        decompose_transition_reachable H.
        assert (TransitionTrace miner s s) by eapply clnil.
        assert(is_call_act (buyer_call_RejectItem cstate) = true).
        {
          eapply (buyer_call_AcceptItem_is_call_act cstate).
        }
        econstructor;eauto.
        eapply (snoc X (step_trans miner (buyer_call_AcceptItem  cstate) H  Htrans)).
      }
      exists s'.
      split.
      eauto.
      pose proof H.
      eapply transition_reachable_impl_reachable in H.
      eapply balance_on_chain_forall in H;eauto.
      unfold funds.
      lia.
      eapply transition_reachable_impl_reachable_through in H0;eauto.
      eapply reachable_through_contract_deployed in H0;eauto.
      unfold outgoing_acts.
      eapply transition_reachable_queue_is_empty in H0.
      rewrite H0.
      intuition.
      eauto.
      eauto.
      unfold require_phase.
      rewrite HcurrentPhase;eauto.
      unfold require_phase.
      rewrite HcurrentPhase;eauto.
    - pose proof Hcs_s as Ht.
      eapply COMPLETED_impl_bal_forall in Hcs_s;eauto.
      exists s.
      split.
      eauto.
      destruct_and_split.
      pose proof Htrc_s.
      econstructor;eauto.
      econstructor;eauto.
      pose proof Htrc_s.
      eapply transition_reachable_impl_reachable in H.
      eapply balance_on_chain_forall in Ht;eauto.
      unfold funds.
      lia.
      eapply transition_reachable_queue_is_empty in Htrc_s.
      unfold outgoing_acts.
      rewrite Htrc_s.
      intuition.
      eauto.
      eauto.
    - pose proof Htrc_s.
      eapply (arbitrator_call_Arbitrate_transition_correct
       s cstate true)in H;eauto.
      destruct H as [s' Htrans].
      pose proof Htrans.
      eapply arbitrator_call_Arbitrate_state_correct in H;eauto.
      destruct H as [cstate' [Hcs_s' [HPhase Hbal ]]].
      assert (Hready':transition_reachable miner contract caddr s0 s').
      {
        decompose_transition_reachable Htrc_s.
        assert (TransitionTrace miner s0 s').
        assert(is_call_act (arbitrator_call_Arbitrate cstate' true) = true).
        {
          eapply (buyer_call_AcceptItem_is_call_act cstate').
        }
        eapply (snoc trace (step_trans miner (arbitrator_call_Arbitrate cstate' true) H Htrans)).
        econstructor;eauto.
      }
      assert (trace_s_s' :inhabited(TransitionTrace miner s s')).
      {
        assert(is_call_act (arbitrator_call_Arbitrate cstate true) = true).
        {
          eapply (buyer_call_AcceptItem_is_call_act cstate).
        }
        assert (TransitionTrace miner s s) by eapply clnil.
        econstructor;eauto.
        eapply (snoc X (step_trans miner (arbitrator_call_Arbitrate cstate true) H  Htrans)).
      }
      pose proof Hready'.
      eapply transition_reachable_impl_reachable in H.
      eapply balance_on_chain_forall in Hcs_s';eauto.
      exists s'.
      split.
      eauto.
      unfold funds.
      intuition.
      eapply transition_reachable_impl_reachable_through in Hready';eauto.
      eapply reachable_through_contract_deployed in Hready';eauto.
      eapply transition_reachable_queue_is_empty in Hready'.
      unfold outgoing_acts.
      rewrite Hready'.
      intuition.
      eauto.
      eauto.
      unfold require_phase.
      rewrite HcurrentPhase;eauto.
      unfold require_phase.
      rewrite HcurrentPhase;eauto.
    - eauto. 
  Qed.

  Definition good_seller_addrs := [useller;uarbitrator].

  Definition good_seller : (strat miner good_seller_addrs) :=
    fun s0 s tr  =>
      match get_contract_state s caddr with
      | Some state =>
          match state.(currentPhase) with
          | AWAITING_SHIPMENT =>
              [seller_call_MarkAsShipped state]
          | AWAITING_ACCEPTANCE =>
              [seller_call_RejectItem state]
          | DISPUTED =>
              [(arbitrator_call_Arbitrate state true);
                (arbitrator_call_Arbitrate state false)]
          | _ => []
          end
      | None => []
      end.


  Definition bad_seller_addrs := [useller].

  Definition bad_seller : (strat miner bad_seller_addrs) :=
    fun s0 s tr =>
      match get_contract_state s caddr with
      | Some state =>
          match state.(currentPhase) with
          | AWAITING_SHIPMENT =>
              []
          | AWAITING_ACCEPTANCE =>
              []
          | DISPUTED =>
              []
          | _ => []
          end
      | None => []
      end.

  Definition good_buyer_addrs := [ubuyer;uarbitrator].

  Definition good_buyer : (strat miner good_buyer_addrs) :=
    fun s0 s tr =>
      match get_contract_state s caddr with
      | Some state =>
          match state.(currentPhase) with
          | AWAITING_SHIPMENT =>
              [buyer_call_RejectItem state]
          | AWAITING_ACCEPTANCE =>
              [buyer_call_AcceptItem state;buyer_call_RejectItem state]
          | DISPUTED =>
              [(arbitrator_call_Arbitrate state true);
              (arbitrator_call_Arbitrate state false)]
          | _ => []
          end
      | None => []
      end.
    
  Definition bad_buyer_addrs := [ubuyer].
    

  Definition bad_buyer : (strat miner bad_buyer_addrs) :=
    fun s0 s tr =>
      match get_contract_state s caddr with
      | Some state =>
          match state.(currentPhase) with
          | AWAITING_SHIPMENT =>
              []
          | AWAITING_ACCEPTANCE =>
              []
          | DISPUTED =>
              []
          | _ => []
          end
      | None => []
      end.

  Lemma escrow_satisfy_strat_liquidity_with_good_buyer_bad_seller:
    strat_liquidity miner good_buyer_addrs good_buyer bad_seller_addrs  bad_seller contract caddr  s0.
  Proof.
    unfold strat_liquidity.
    intros.
    rename H into Hwell_sys.
    assert(H_init_t: is_init_state contract caddr s0) by eauto.
    decompose_is_init_state H_init_t.
    assert(Hrct_s0_s' : reachable_through s0 s').
    {
      eapply transition_reachable_impl_reachable_through in H_init;eauto.
      econstructor;eauto.
    }
    assert( H_caddr_not_EOA : address_is_contract caddr = true).
    {
      eapply contract_addr_format in H_reachable;eauto.  
    }
    eapply (reachable_through_contract_deployed s0 s' caddr contract) in Hrct_s0_s' as Hec_s';eauto.
    assert(Hrc_s' : reachable s').
    {
      assert(transition_reachable miner contract caddr  s0 s').
      {
        econstructor;eauto.
      }
      eapply transition_reachable_impl_reachable in H;eauto.
    }
    assert(Hqueue_s':chain_state_queue s' = []).
    {
      eapply transition_reachable_queue_is_empty in Hwell_sys;eauto.
      econstructor;eauto.
    }
    rename s' into s.
    pose proof Hec_s'.
    eapply deployed_contract_state_typed in H;eauto.
    destruct H as [cstate Hcs].
    destruct(cstate.(currentPhase)) eqn : HcurrentPhase.
    + assert(Htr1:exists s' : ChainState,
            transition miner s (buyer_call_RejectItem cstate) = Ok s').
      {
        eapply buyer_call_RejectItem_transition_correct;eauto.
        right.
        unfold require_phase.
        rewrite HcurrentPhase.
        eauto.
        econstructor;eauto.
      }
      destruct Htr1 as [s' Htranss'].
      assert (Hact_call1:is_call_act (buyer_call_RejectItem cstate) = true).
      {
        eapply buyer_call_RejectItem_is_call_act.
      }
      set(tr'':=(snoc tr' (step_trans miner (buyer_call_RejectItem cstate) Hact_call1 Htranss'))).
      assert (Hsd1:stratDrive miner good_buyer_addrs good_buyer  s0 s tr' s' tr'').
      {
        econstructor.
        exists Hact_call1,Htranss'.
        split.
        unfold good_buyer.
        unfold get_contract_state.
        pose proof Hcs.
        unfold contract_state in Hcs.
        simpl in Hcs.
        destruct (env_contract_states s caddr) eqn : Htt.
        rewrite Hcs.
        rewrite HcurrentPhase.
        intuition.
        unfold contract_state  in H.
        simpl in H.
        destruct (env_contract_states s caddr).
        inversion Htt.
        inversion H.
        eauto.
      }
      pose proof Htranss' as Htt1.
      assert(Htt2:exists cstate' : State,
      contract_state s' caddr = Some cstate' /\ currentPhase cstate' = DISPUTED).
      {
        eapply buyer_call_RejectItem_state_correct in Htt1;eauto.
        right.
        unfold require_phase.
        rewrite HcurrentPhase.
        eauto.
        econstructor;eauto.
      }
      assert(Hready' : transition_reachable miner contract caddr s0 s').
      {
        econstructor;eauto.
      }
      destruct Htt2 as [cstate' [Hcs_s' HcurrentPhase']].
      assert(Htt2:exists s'' : ChainState,
          transition miner s' (arbitrator_call_Arbitrate cstate' true) = Ok s'').
      {
        eapply arbitrator_call_Arbitrate_transition_correct
        ;eauto.
        unfold require_phase .
        rewrite HcurrentPhase'.
        eauto.
      }
      destruct Htt2 as [s'' Htranss''].
      assert (Hact_call2:is_call_act (arbitrator_call_Arbitrate cstate' true) = true).
      {
        eapply arbitrator_call_Arbitrate_is_call_act.
      }
      set(tr''':=(snoc tr'' (step_trans miner (arbitrator_call_Arbitrate cstate' true) Hact_call2 Htranss''))).
      assert (Hsd2:stratDrive miner good_buyer_addrs good_buyer  s0 s' tr'' s'' tr''').
      {
        econstructor.
        exists Hact_call2,Htranss''.
        split.
        unfold good_buyer.
        unfold get_contract_state.
        pose proof Hcs_s'.
        unfold contract_state in Hcs_s'.
        simpl in Hcs_s'.
        destruct (env_contract_states s' caddr) eqn : Htt.
        rewrite Hcs_s'.
        rewrite HcurrentPhase'.
        intuition.
        unfold contract_state  in H.
        simpl in H.
        destruct (env_contract_states s' caddr).
        inversion Htt.
        inversion H.
        eauto.
      }
      pose proof Htranss'' as Htt1'.

      assert(Htt2:exists cstate'' : State,
      contract_state s'' caddr = Some cstate'' /\
      currentPhase cstate'' = COMPLETED /\ depositAmount cstate'' = 0).
      {
        eapply arbitrator_call_Arbitrate_state_correct in Htt1';eauto.
        destruct_and_split.
        unfold require_phase.
        rewrite HcurrentPhase'.
        eauto.
      }
      assert(Hready'' : transition_reachable miner contract caddr s0 s'').
      {
        econstructor;eauto.
      }
      destruct Htt2 as [cstate'' [Hcs_s'' [HcurrentPhase'' Hbal']]].
      pose proof Hready''.
      eapply transition_reachable_impl_reachable in H;eauto.
      assert(Hbal: env_account_balances s'' caddr = depositAmount cstate'').
      {
        eapply balance_on_chain_forall in H;eauto.
        eauto.
        eapply transition_reachable_impl_reachable_through in Hready'';eauto.
        eapply reachable_through_contract_deployed in Hready'';eauto.
        eapply transition_reachable_queue_is_empty in Hready''.
        unfold outgoing_acts.
        rewrite Hready''.
        intuition.
        eauto.
      }
      destruct (funds s' caddr =? 0) eqn : Hfs'.
      eapply ULM_Step;eauto.
      
      eapply EPM_Base;eauto.
      propify.
      eauto.
      propify.
      assert(funds s' caddr > 0).
      {
        eapply transition_reachable_impl_reachable in Hready'.
        eapply (reachable_funds_nonnegative s' caddr)  in Hready'.
        eauto.
        lia.
        eauto.
      }
      eapply ULM_Step;eauto.
      eapply EPM_Step;eauto.
      intros.
      eapply multiSuccTrace_delta_empty_refl_multr_s_tr in H2.
      destruct_and_split.
      inversion H3.
      eapply ULM_Step;eauto.
      eapply EPM_Base;eauto.
      unfold funds.
      lia.
      unfold bad_seller.
      destruct (get_contract_state s' caddr);eauto.
      destruct  (currentPhase s1);eauto.
    + assert(Htr1:exists s' : ChainState,
            transition miner s (buyer_call_AcceptItem cstate) = Ok s').
      {
        eapply buyer_call_AcceptItem_transition_correct;eauto.
        unfold require_phase.
        rewrite HcurrentPhase.
        eauto.
        econstructor;eauto.
      }
      destruct Htr1 as [s' Htranss'].
      assert (Hact_call1:is_call_act (buyer_call_AcceptItem cstate) = true).
      {
        eapply buyer_call_AcceptItem_is_call_act.
      }
      set(tr'':=(snoc tr' (step_trans miner (buyer_call_AcceptItem cstate) Hact_call1 Htranss'))).
      assert (Hsd1:stratDrive miner good_buyer_addrs good_buyer  s0  s tr' s' tr'').
      {
        econstructor.
        exists Hact_call1,Htranss'.
        split.
        unfold good_buyer.
        unfold get_contract_state.
        pose proof Hcs.
        unfold contract_state in Hcs.
        simpl in Hcs.
        destruct (env_contract_states s caddr) eqn : Htt.
        rewrite Hcs.
        rewrite HcurrentPhase.
        intuition.
        unfold contract_state  in H.
        simpl in H.
        destruct (env_contract_states s caddr).
        inversion Htt.
        inversion H.
        eauto.
      }
      pose proof Htranss' as Htt1.
      assert(Htt2:exists cstate' : State,
      contract_state s' caddr = Some cstate' /\
      currentPhase cstate' = COMPLETED /\
      itemAccepted cstate' = true /\ depositAmount cstate' = 0).
      {
        eapply buyer_call_AcceptItem_state_correct in Htt1;eauto.
        unfold require_phase.
        rewrite HcurrentPhase.
        eauto.
        econstructor;eauto.
      }
      assert(Hready' : transition_reachable miner contract caddr s0 s').
      {
        econstructor;eauto.
      }
      destruct Htt2 as [cstate' [Hcs_s' HcurrentPhase']].
      destruct_and_split.
      pose proof Hready' as Htrst'.
      pose proof Hready' as Htrs'.
      eapply transition_reachable_impl_reachable in Htrs';eauto.
      assert(Hbal: env_account_balances s' caddr = depositAmount cstate').
      {
        eapply balance_on_chain_forall in Htrs';eauto.
        eauto.
        eapply transition_reachable_impl_reachable_through in Htrst';eauto.
        eapply reachable_through_contract_deployed in Htrst';eauto.
        eapply transition_reachable_queue_is_empty in Hready'.
        unfold outgoing_acts.
        rewrite Hready'.
        intuition.
        eauto.
      }
      eapply ULM_Step;eauto.
      eapply EPM_Base;eauto.
      unfold funds.
      lia.
    + 
      assert(Hbal: env_account_balances s caddr = depositAmount cstate).
      {
        eapply balance_on_chain_forall in Hrc_s';eauto.
        eauto.
        unfold outgoing_acts.
        rewrite Hqueue_s'.
        intuition.
      }
      eapply COMPLETED_impl_bal_forall in HcurrentPhase;eauto.
      eapply ULM_Base.
      unfold funds;lia.
    + assert(Htt2:exists s' : ChainState,
          transition miner s (arbitrator_call_Arbitrate cstate true) = Ok s').
      {
        eapply arbitrator_call_Arbitrate_transition_correct
        ;eauto.
        unfold require_phase .
        rewrite HcurrentPhase.
        eauto.
        econstructor;eauto.
      }
      destruct Htt2 as [s' Htranss'].
      assert (Hact_call2:is_call_act (arbitrator_call_Arbitrate cstate true) = true).
      {
        eapply arbitrator_call_Arbitrate_is_call_act.
      }
      set(tr'':=(snoc tr' (step_trans miner (arbitrator_call_Arbitrate cstate true) Hact_call2 Htranss'))).
      assert (Hsd2:stratDrive miner  good_buyer_addrs good_buyer s0  s tr' s' tr'').
      {
        econstructor.
        exists Hact_call2,Htranss'.
        split.
        unfold good_buyer.
        unfold get_contract_state.
        pose proof Hrc_s'.
        unfold contract_state in Hcs.
        simpl in Hcs.
        destruct (env_contract_states s caddr) eqn : Htt.
        rewrite Hcs.
        rewrite HcurrentPhase.
        intuition.
        unfold contract_state  in H.
        simpl in H.
        destruct (env_contract_states s caddr).
        inversion Htt.
        inversion Hcs.
        eauto.
      }
      pose proof Htranss' as Htt1'.
      assert(Htt2:exists cstate' : State,
      contract_state s' caddr = Some cstate' /\
      currentPhase cstate' = COMPLETED /\ depositAmount cstate' = 0).
      {
        eapply arbitrator_call_Arbitrate_state_correct in Htt1';eauto.
        destruct_and_split.
        unfold require_phase.
        rewrite HcurrentPhase.
        eauto.
        econstructor;eauto.
      }
      assert(Hready' : transition_reachable miner contract caddr s0 s').
      {
        econstructor;eauto.
      }
      destruct Htt2 as [cstate'' [Hcs_s'' [HcurrentPhase'' Hbal']]].
      pose proof Hready'.
      eapply transition_reachable_impl_reachable in H;eauto.
      assert(Hbal: env_account_balances s' caddr = depositAmount cstate'').
      {
        eapply balance_on_chain_forall in H;eauto.
        eauto.
        eapply transition_reachable_impl_reachable_through in Hready';eauto.
        eapply reachable_through_contract_deployed in Hready';eauto.
        unfold outgoing_acts.
        eapply transition_reachable_queue_is_empty in Hready'.
        rewrite Hready'.
        intuition.
        eauto.
      }
        eapply ULM_Step;eauto.
        eapply EPM_Base;eauto.
        unfold funds.
        lia.
  Qed.

  Lemma escrow_satisfy_strat_liquidity_with_good_seller_bad_buyer:
    strat_liquidity miner good_seller_addrs good_seller bad_buyer_addrs  bad_buyer contract caddr  s0.
  Proof.
    unfold strat_liquidity.
    intros.
    rename H into Hwell_sys.
    assert(H_init_t: is_init_state contract caddr s0) by eauto.
    decompose_is_init_state H_init_t.
    assert(Hrct_s0_s' : reachable_through s0 s').
    {
      eapply transition_reachable_impl_reachable_through in H_init;eauto.
      econstructor;eauto.
    }
    assert( H_caddr_not_EOA : address_is_contract caddr = true).
    {
      eapply contract_addr_format in H_reachable;eauto.  
    }
    eapply (reachable_through_contract_deployed s0 s' caddr contract) in Hrct_s0_s' as Hec_s';eauto.
    assert(Hrc_s' : reachable s').
    {
      assert(transition_reachable miner contract caddr  s0 s').
      {
        econstructor;eauto.
      }
      eapply transition_reachable_impl_reachable in H;eauto.
    }
    assert(Hqueue_s':chain_state_queue s' = []).
    {
      eapply transition_reachable_queue_is_empty in Hwell_sys;eauto.
      econstructor;eauto.
    }
    rename s' into s.
    pose proof Hec_s'.
    eapply deployed_contract_state_typed in H;eauto.
    destruct H as [cstate Hcs].
    destruct(cstate.(currentPhase)) eqn : HcurrentPhase.
    + assert(Htr1:exists s' : ChainState,
            transition miner s (seller_call_MarkAsShipped cstate) = Ok s').
      {
        eapply seller_call_MarkAsShipped_transition_correct;eauto.
        
        unfold require_phase.
        rewrite HcurrentPhase.
        eauto.
        econstructor;eauto.
      }
      destruct Htr1 as [s' Htranss'].
      assert (Hact_call1:is_call_act (seller_call_MarkAsShipped cstate) = true).
      {
        eapply seller_call_MarkAsShipped_is_call_act.
      }
      set(tr'':=(snoc tr' (step_trans miner (seller_call_MarkAsShipped cstate) Hact_call1 Htranss'))).
      assert (Hsd1:stratDrive miner good_seller_addrs good_seller  s0 s tr' s' tr'').
      {
        econstructor.
        exists Hact_call1,Htranss'.
        split.
        unfold good_seller.
        unfold get_contract_state.
        pose proof Hcs.
        unfold contract_state in Hcs.
        simpl in Hcs.
        destruct (env_contract_states s caddr) eqn : Htt.
        rewrite Hcs.
        rewrite HcurrentPhase.
        intuition.
        unfold contract_state  in H.
        simpl in H.
        destruct (env_contract_states s caddr).
        inversion Htt.
        inversion H.
        eauto.
      }
      pose proof Htranss' as Htt1.
      assert(Htt2:exists cstate' : State,
      contract_state s' caddr = Some cstate' /\
      currentPhase cstate' = AWAITING_ACCEPTANCE /\ itemShipped cstate' = true).
      {
        eapply seller_call_MarkAsShipped_state_correct in Htt1;eauto.
        unfold require_phase.
        rewrite HcurrentPhase.
        eauto.
        econstructor;eauto.
      }
      assert(Hready' : transition_reachable miner contract caddr s0 s').
      {
        econstructor;eauto.
      }
      destruct Htt2 as [cstate' [Hcs_s' [HcurrentPhase' HitemShipped]]].
      assert(Htt2:exists s'' : ChainState,
          transition miner s' (seller_call_RejectItem cstate') = Ok s'').
      {
        eapply seller_call_RejectItem_transition_correct;eauto.
        left.
        unfold require_phase .
        rewrite HcurrentPhase'.
        eauto.
      }
      destruct Htt2 as [s'' Htranss''].
      assert (Hact_call2:is_call_act (seller_call_RejectItem cstate' ) = true).
      {
        eapply seller_call_RejectItem_is_call_act.
      }
      set(tr''':=(snoc tr'' (step_trans miner (seller_call_RejectItem cstate') Hact_call2 Htranss''))).
      assert (Hsd2:stratDrive miner   good_seller_addrs good_seller s0 s' tr'' s'' tr''').
      {
        econstructor.
        exists Hact_call2,Htranss''.
        split.
        unfold good_seller.
        unfold get_contract_state.
        pose proof Hcs_s'.
        unfold contract_state in Hcs_s'.
        simpl in Hcs_s'.
        destruct (env_contract_states s' caddr) eqn : Htt.
        rewrite Hcs_s'.
        rewrite HcurrentPhase'.
        intuition.
        unfold contract_state  in H.
        simpl in H.
        destruct (env_contract_states s' caddr).
        inversion Htt.
        inversion H.
        eauto.
      }
      pose proof Htranss'' as Htt1'.

      assert(Htt2:exists cstate' : State,
      contract_state s'' caddr = Some cstate' /\ currentPhase cstate' = DISPUTED).
      {
        eapply seller_call_RejectItem_state_correct in Htt1';eauto.
        left.
        unfold require_phase.
        rewrite HcurrentPhase'.
        eauto.
      }
      assert(Hready'' : transition_reachable miner contract caddr s0 s'').
      {
        econstructor;eauto.
      }
      destruct Htt2 as [cstate'' [Hcs_s'' HcurrentPhase'']].
      assert(Htt2:exists s''' : ChainState,
          transition miner s'' (arbitrator_call_Arbitrate cstate'' true) = Ok s''').
      {
        eapply arbitrator_call_Arbitrate_transition_correct;eauto.
        unfold require_phase .
        rewrite HcurrentPhase''.
        eauto.
      }
      destruct Htt2 as [s''' Htranss'''].
      assert (Hact_call3:is_call_act (arbitrator_call_Arbitrate cstate'' true) = true).
      {
        eapply (seller_call_RejectItem_is_call_act cstate'').
      }
      set(tr'''':=(snoc tr''' (step_trans miner (arbitrator_call_Arbitrate cstate' true) Hact_call3 Htranss'''))).
      assert (Hsd3:stratDrive miner good_seller_addrs good_seller   s0 s'' tr''' s''' tr'''').
      {
        econstructor.
        exists Hact_call3,Htranss'''.
        split.
        unfold good_seller.
        unfold get_contract_state.
        pose proof Hcs_s''.
        unfold contract_state in Hcs_s''.
        simpl in Hcs_s''.
        destruct (env_contract_states s'' caddr) eqn : Htt'.
        rewrite Hcs_s''.
        rewrite HcurrentPhase''.
        intuition.
        unfold contract_state  in H.
        simpl in H.
        destruct (env_contract_states s'' caddr).
        inversion Htt'.
        inversion H.
        eauto.
      }
      pose proof Htranss''' as Htt1''.
      assert(Htt2:exists cstate' : State,
      contract_state s''' caddr = Some cstate' /\
      currentPhase cstate' = COMPLETED /\ depositAmount cstate' = 0).
      {
        eapply arbitrator_call_Arbitrate_state_correct in Htt1'';eauto.
        unfold require_phase.
        rewrite HcurrentPhase''.
        eauto.
      }
      assert(Hready''' : transition_reachable miner contract caddr s0 s''').
      {
        econstructor;eauto.
      }
      destruct Htt2 as [cstate''' [Hcs_s''' HcurrentPhase''']].
      pose proof Hready'''.
      eapply transition_reachable_impl_reachable in H;eauto.
      assert(Hbal: env_account_balances s''' caddr = depositAmount cstate''').
      {
        eapply balance_on_chain_forall in H;eauto.
        eauto.
        eapply transition_reachable_impl_reachable_through in Hready''';eauto.
        eapply reachable_through_contract_deployed in Hready''';eauto.
        eapply transition_reachable_queue_is_empty in Hready''';eauto.
        unfold outgoing_acts.
        rewrite Hready'''.
        intuition.
      }
      destruct (funds s' caddr =? 0) eqn : Hfs'.
      eapply ULM_Step;eauto.
      
      eapply EPM_Base;eauto.
      propify.
      eauto.
      propify.
      assert(funds s' caddr > 0).
      {
        eapply transition_reachable_impl_reachable in Hready'.
        eapply (reachable_funds_nonnegative s' caddr)  in Hready'.
        eauto.
        lia.
        eauto.
      }
      destruct (funds s'' caddr =? 0) eqn : Hfs''. 
      eapply ULM_Step;eauto.
      eapply EPM_Step;eauto.
      intros.
      eapply multiSuccTrace_delta_empty_refl_multr_s_tr in H2.
      destruct_and_split.
      inversion H3.
      eapply ULM_Step;eauto.
      eapply EPM_Base;eauto.
      propify.
      eauto.
      propify.
      unfold bad_buyer .
      destruct (get_contract_state s' caddr);eauto.
      destruct  (currentPhase s1);eauto.
      assert(funds s'' caddr > 0).
      {
        eapply transition_reachable_impl_reachable in Hready''.
        eapply (reachable_funds_nonnegative s'' caddr)  in Hready''.
        eauto.
        lia.
        eauto.
      }
      eapply ULM_Step;eauto.
      eapply EPM_Step;eauto.
      intros.
      eapply multiSuccTrace_delta_empty_refl_multr_s_tr in H3.
      destruct_and_split.
      inversion H4.
      eapply ULM_Step;eauto.
      eapply EPM_Step;eauto.
      intros.
      eapply multiSuccTrace_delta_empty_refl_multr_s_tr in H7.
      destruct_and_split.
      inversion H10.
      eapply ULM_Step;eauto.
      eapply EPM_Base;eauto.
      unfold funds.
      lia.
      unfold bad_buyer .
      destruct (get_contract_state s'' caddr);eauto.
      destruct  (currentPhase s1);eauto.
      unfold bad_buyer .
      destruct (get_contract_state s' caddr);eauto.
      destruct  (currentPhase s1);eauto.
    + assert(Htr1:exists s' : ChainState,
            transition miner s (seller_call_RejectItem cstate) = Ok s').
      {
        eapply seller_call_RejectItem_transition_correct;eauto.
        left.
        unfold require_phase.
        rewrite HcurrentPhase.
        eauto.
        econstructor;eauto.
      }
      destruct Htr1 as [s' Htranss'].
      assert (Hact_call1:is_call_act (seller_call_RejectItem cstate) = true).
      {
        eapply seller_call_RejectItem_is_call_act.
      }
      set(tr'':=(snoc tr' (step_trans miner (seller_call_RejectItem cstate) Hact_call1 Htranss'))).
      assert (Hsd1:stratDrive miner  good_seller_addrs good_seller s0 s tr' s' tr'').
      {
        econstructor.
        exists Hact_call1,Htranss'.
        split.
        unfold good_seller.
        unfold get_contract_state.
        pose proof Hcs.
        unfold contract_state in Hcs.
        simpl in Hcs.
        destruct (env_contract_states s caddr) eqn : Htt.
        rewrite Hcs.
        rewrite HcurrentPhase.
        intuition.
        unfold contract_state  in H.
        simpl in H.
        destruct (env_contract_states s caddr).
        inversion Htt.
        inversion H.
        eauto.
      }
      pose proof Htranss' as Htt1.
      assert(Htt2:exists cstate' : State,
      contract_state s' caddr = Some cstate' /\ currentPhase cstate' = DISPUTED).
      {
        eapply seller_call_RejectItem_state_correct in Htt1;eauto.
        left.
        unfold require_phase.
        rewrite HcurrentPhase.
        eauto.
        econstructor;eauto.
      }
      assert(Hready' : transition_reachable miner contract caddr s0 s').
      {
        econstructor;eauto.
      }
      destruct Htt2 as [cstate' [Hcs_s' HcurrentPhase']].
      assert(Htt2:exists s'' : ChainState,
          transition miner s' (arbitrator_call_Arbitrate cstate' true) = Ok s'').
      {
        eapply arbitrator_call_Arbitrate_transition_correct
        ;eauto.
        unfold require_phase .
        rewrite HcurrentPhase'.
        eauto.
      }
      destruct Htt2 as [s'' Htranss''].
      assert (Hact_call2:is_call_act (arbitrator_call_Arbitrate cstate' true) = true).
      {
        eapply arbitrator_call_Arbitrate_is_call_act.
      }
      set(tr''':=(snoc tr'' (step_trans miner (arbitrator_call_Arbitrate cstate' true) Hact_call2 Htranss''))).
      assert (Hsd2:stratDrive miner  good_seller_addrs good_seller s0 s' tr'' s'' tr''').
      {
        econstructor.
        exists Hact_call2,Htranss''.
        split.
        unfold good_seller.
        unfold get_contract_state.
        pose proof Hcs_s'.
        unfold contract_state in Hcs_s'.
        simpl in Hcs_s'.
        destruct (env_contract_states s' caddr) eqn : Htt.
        rewrite Hcs_s'.
        rewrite HcurrentPhase'.
        intuition.
        unfold contract_state  in H.
        simpl in H.
        destruct (env_contract_states s' caddr).
        inversion Htt.
        inversion H.
        eauto.
      }
      pose proof Htranss'' as Htt1'.

      assert(Htt2:exists cstate'' : State,
      contract_state s'' caddr = Some cstate'' /\
      currentPhase cstate'' = COMPLETED /\ depositAmount cstate'' = 0).
      {
        eapply arbitrator_call_Arbitrate_state_correct in Htt1';eauto.
        destruct_and_split.
        unfold require_phase.
        rewrite HcurrentPhase'.
        eauto.
      }
      assert(Hready'' : transition_reachable miner contract caddr s0 s'').
      {
        econstructor;eauto.
      }
      destruct Htt2 as [cstate'' [Hcs_s'' [HcurrentPhase'' Hbal']]].
      pose proof Hready''.
      eapply transition_reachable_impl_reachable in H;eauto.
      assert(Hbal: env_account_balances s'' caddr = depositAmount cstate'').
      {
        eapply balance_on_chain_forall in H;eauto.
        eauto.
        eapply transition_reachable_impl_reachable_through in Hready'';eauto.
        eapply reachable_through_contract_deployed in Hready'';eauto.
        eapply transition_reachable_queue_is_empty in  Hready'';eauto.
        unfold outgoing_acts.
        rewrite Hready''.
        intuition.
      }
      destruct (funds s' caddr =? 0) eqn : Hfs'.
      eapply ULM_Step;eauto.
      
      eapply EPM_Base;eauto.
      propify.
      eauto.
      propify.
      assert(funds s' caddr > 0).
      {
        eapply transition_reachable_impl_reachable in Hready'.
        eapply (reachable_funds_nonnegative s' caddr)  in Hready'.
        eauto.
        lia.
        eauto.
      }
      eapply ULM_Step;eauto.
      eapply EPM_Step;eauto.
      intros.
      eapply multiSuccTrace_delta_empty_refl_multr_s_tr in H2.
      destruct_and_split.
      inversion H3.
      eapply ULM_Step;eauto.
      eapply EPM_Base;eauto.
      unfold funds.
      lia.
      unfold bad_buyer.
      destruct (get_contract_state s' caddr);eauto.
      destruct  (currentPhase s1);eauto.
    + assert(Hbal: env_account_balances s caddr = depositAmount cstate).
      {
        eapply balance_on_chain_forall in Hrc_s';eauto.
        eauto.
        unfold outgoing_acts.
        rewrite Hqueue_s'.
        intuition.
      }
      eapply COMPLETED_impl_bal_forall in HcurrentPhase;eauto.
      eapply ULM_Base.
      unfold funds;lia.
    + assert(Htt2:exists s' : ChainState,
          transition miner s (arbitrator_call_Arbitrate cstate true) = Ok s').
      {
        eapply arbitrator_call_Arbitrate_transition_correct
        ;eauto.
        unfold require_phase .
        rewrite HcurrentPhase.
        eauto.
        econstructor;eauto.
      }
      destruct Htt2 as [s' Htranss'].
      assert (Hact_call2:is_call_act (arbitrator_call_Arbitrate cstate true) = true).
      {
        eapply arbitrator_call_Arbitrate_is_call_act.
      }
      set(tr'':=(snoc tr' (step_trans miner (arbitrator_call_Arbitrate cstate true) Hact_call2 Htranss'))).
      assert (Hsd2:stratDrive miner good_seller_addrs good_seller  s0 s tr' s' tr'').
      {
        econstructor.
        exists Hact_call2,Htranss'.
        split.
        unfold good_seller.
        unfold get_contract_state.
        pose proof Hrc_s'.
        unfold contract_state in Hcs.
        simpl in Hcs.
        destruct (env_contract_states s caddr) eqn : Htt.
        rewrite Hcs.
        rewrite HcurrentPhase.
        intuition.
        unfold contract_state  in H.
        simpl in H.
        destruct (env_contract_states s caddr).
        inversion Htt.
        inversion Hcs.
        eauto.
      }
      pose proof Htranss' as Htt1'.
      assert(Htt2:exists cstate' : State,
      contract_state s' caddr = Some cstate' /\
      currentPhase cstate' = COMPLETED /\ depositAmount cstate' = 0).
      {
        eapply arbitrator_call_Arbitrate_state_correct in Htt1';eauto.
        destruct_and_split.
        unfold require_phase.
        rewrite HcurrentPhase.
        eauto.
        econstructor;eauto.
      }
      assert(Hready' : transition_reachable miner contract caddr s0 s').
      {
        econstructor;eauto.
      }
      destruct Htt2 as [cstate'' [Hcs_s'' [HcurrentPhase'' Hbal']]].
      pose proof Hready'.
      eapply transition_reachable_impl_reachable in H;eauto.
      assert(Hbal: env_account_balances s' caddr = depositAmount cstate'').
      {
        eapply balance_on_chain_forall in H;eauto.
        eauto.
        eapply transition_reachable_impl_reachable_through in Hready';eauto.
        eapply reachable_through_contract_deployed in Hready';eauto.
        eapply transition_reachable_queue_is_empty in Hready';eauto.
        unfold outgoing_acts.
        rewrite Hready'.
        intuition.
      }
      eapply ULM_Step;eauto.
      eapply EPM_Base;eauto.
      unfold funds.
      lia.
  Qed.

End Lqiuidity.


