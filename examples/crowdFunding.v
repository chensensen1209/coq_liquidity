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

Section Crowdfund.

  Context {BaseTypes : ChainBase}.
  Set Primitive Projections.
  Set Nonrecursive Elimination Schemes.
  Context {AddrSize : N}.
  
  Local Open Scope Z.

  (* 定义 donors 映射类型 *)
  Definition DonorsMap := FMap Address Amount.

  (* 合约状态 *)
  Record State := build_state {
    end_donate : nat;            (* 最后一个捐赠区块 *)
    target : Amount;             (* 目标金额 *)
    owner : Address;             (* 资金接收者 *)
    donors : DonorsMap;          (* 捐赠者映射 *)
    target_reached : bool;       (* 目标是否达到 *)
    balance : Amount;            (* 合约当前余额 *)
  }.

  (* 设置参数 *)
  Record Setup := build_setup {
    setup_owner : Address;       (* 资金接收者地址 *)
    setup_end_donate : nat;      (* 最后一个捐赠区块 *)
    setup_target : Amount;       (* 目标金额 *)
  }.

  (* 设置可设置实例 *)
  Instance state_settable : Settable State :=
    settable! build_state <end_donate; target; owner; donors; target_reached; balance>.

  Instance setup_settable : Settable Setup :=
    settable! build_setup <setup_owner; setup_end_donate; setup_target>.

  (* 消息类型 *)
  Inductive Msg :=
  | Donate (amount : Amount)          (* 捐赠消息 *)
  | WdOwner                          (* 所有者提取资金消息 *)
  | WdDonor.                         (* 捐赠者提取资金消息 *)

  (* 序列化 *)
  Section Serialization.

    Global Instance Msg_serializable : Serializable Msg :=
      Derive Serializable Msg_rect<Donate, WdOwner, WdDonor>.

    Global Instance Setup_serializable : Serializable Setup :=
      Derive Serializable Setup_rect<build_setup>.

    Global Instance State_serializable : Serializable State :=
      Derive Serializable State_rect<build_state>.

  End Serialization.

  (* 错误类型 *)
  Definition Error : Type := nat.
  Definition default_error : Error := 1%nat.

  (* 辅助函数：查找捐赠者的捐赠金额，若不存在则返回 0 *)
  Definition find_donor (addr : Address) (dmap : DonorsMap) : Amount :=
    match FMap.find addr dmap with
    | Some amt => amt
    | None => 0
    end.

  (* 初始化合约 *)
  Definition init
             (chain : Chain)
             (ctx : ContractCallContext)
             (setup : Setup)
    : result State Error :=
    let msg_sender := ctx_from ctx in
    let msg_value := ctx_amount ctx in
    if msg_value =? 0
    then
      Ok (build_state
            setup.(setup_end_donate)       (* end_donate *)
            setup.(setup_target)           (* target *)
            setup.(setup_owner)            (* owner *)
            FMap.empty                     (* donors *)
            false                          (* target_reached *)
            0%Z                            (* balance *)
          )
    else
      Err default_error.

  Definition is_target_reached (state : State) : bool :=
    (state.(balance) >=? state.(target))%Z.

  (* 捐赠函数 *)
  Definition donate
             (chain : Chain)
             (ctx : ContractCallContext)
             (state : State)
             (amount : Amount)
    : result (State * list ActionBody) Error :=
    (* 检查当前区块是否在捐赠期内 *)
    if (chain.(current_slot) <=? state.(end_donate))%nat
    then
      (* 更新捐赠者的捐赠金额 *)
      let current_donation := find_donor ctx.(ctx_from) state.(donors) in
      let updated_donors := FMap.add ctx.(ctx_from) (current_donation + amount) state.(donors) in
      (* 更新余额 *)
      let new_balance := state.(balance) + amount in
      (* 检查是否达到目标 *)
      let new_target_reached := if (new_balance >=? state.(target))%Z then true else state.(target_reached) in
      (* 更新状态 *)
      let new_state := state <| donors := updated_donors |>
                             <| balance := new_balance |>
                             <| target_reached := new_target_reached |>
      in
      Ok (new_state, [])
    else
      Err default_error.

  (* 所有者提取资金 *)
  Definition wdOwner
             (chain : Chain)
             (ctx : ContractCallContext)
             (state : State)
    : result (State * list ActionBody) Error :=
    (* 检查是否达到目标且捐赠期已结束 *)
    if (state.(target_reached) && (Nat.leb state.(end_donate) chain.(current_slot)))
    then
      (* 转移资金给所有者 *)
      let actions := [act_transfer state.(owner) state.(balance)] in
      (* 更新状态余额为 0 *)
      let new_state := state <| balance := 0 |>
                             <| donors := FMap.empty |>
      in
      Ok (new_state, actions)
    else
      Err default_error.

  (* 捐赠者提取资金 *)
  Definition wdDonor
             (chain : Chain)
             (ctx : ContractCallContext)
             (state : State)
    : result (State * list ActionBody) Error :=
    (* 检查捐赠期是否已结束 *)
    if (Nat.leb state.(end_donate) chain.(current_slot))
    then
      (* 检查目标未达到 *)
      if negb state.(target_reached)
      then
        let donor_amount := find_donor ctx.(ctx_from) state.(donors) in
        if (donor_amount >? 0)%Z
        then
          (* 转移资金给捐赠者 *)
          let actions := [act_transfer ctx.(ctx_from) donor_amount] in
          (* 更新捐赠者的捐赠金额为 0 *)
          let updated_donors := FMap.add ctx.(ctx_from) 0 state.(donors) in
          (* 更新余额 *)
          let new_balance := state.(balance) - donor_amount in
          (* 更新状态 *)
          let new_state := state <| donors := updated_donors |>
                                 <| balance := new_balance |>
          in
          Ok (new_state, actions)
        else
          Err default_error
      else
        Err default_error (* BUG: 应该检查 target_reached *)
    else
      Err default_error.

  (* 合约接收函数 *)
  Definition receive
             (chain : Chain)
             (ctx : ContractCallContext)
             (state : State)
             (msg : option Msg)
    : result (State * list ActionBody) Error :=
    match msg with
    | Some (Donate amount) => donate chain ctx state amount
    | Some WdOwner => wdOwner chain ctx state
    | Some WdDonor => wdDonor chain ctx state
    | None => Err default_error
    end.

  (* 定义合约 *)
  Definition contract : Contract Setup Msg State Error :=
    build_contract init receive.

End Crowdfund.

Section Theories.

  Context {BaseTypes : ChainBase}.
  Set Primitive Projections.
  Set Nonrecursive Elimination Schemes.
  Context {AddrSize : N}.

  Variable miner_address : Address.

  Hypothesis miner_always_eoa : address_is_contract miner_address = false.

  Global Definition depth_first := true.

  Global Definition miner_reward := 10%Z.

  Local Open Scope Z.

  Tactic Notation "contract_simpl" := contract_simpl @receive @init.

  Ltac destruct_message :=
      repeat match goal with
      | H : Blockchain.receive _ _ _ _ _ = Ok _ |- _ => unfold Blockchain.receive in H; cbn in H
      | msg : option Msg |- _ => destruct msg
      | msg : Msg |- _ => destruct msg
      | H : Blockchain.receive _ _ _ _ None = Ok _ |- _ => now contract_simpl
      | H : receive _ _ _ None = Ok _ |- _ => now contract_simpl
      end.
  
  Ltac just_do_it arg :=
    cbn in *; destruct_match in arg; try congruence.

  Ltac analyze_is_init_bstate H :=
    match type of H with
    | is_init_bstate _ _ _ =>
        unfold is_init_bstate in H;
        destruct H as  [tr_init_bstate [H_reachable [H_queue [H_env_contracts H_env]]]];
        destruct H_env as [ctx [setup [state [H_env_contract_states H_init]]]]
    | _ => fail "The hypothesis" H "is not of the form is_init_bstate contract init_bstate."
    end.

  Definition get_state (bstate : ChainState)
                       (contract_addr : Address)
                        : option State :=
    match env_contract_states bstate contract_addr with
    | Some serialized_state =>
        deserialize serialized_state
    | None => None
    end.

  Lemma CrowdfundBL:
    forall caddr,
      BasicLiquidity miner_address contract caddr.
  Proof.
    unfold BasicLiquidity.
    intros.
    analyze_is_init_bstate H.
  Qed.
  

  



  
End Theories.

