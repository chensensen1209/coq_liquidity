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


Section LotteryContract.

  Context {BaseTypes : ChainBase}.
  Set Primitive Projections.
  Set Nonrecursive Elimination Schemes.

  (* 定义玩家的状态 *)
  Inductive PlayerState :=
  | Committed  (* 玩家已承诺秘密 *)
  | Redeemed   (* 玩家已赎回资金 *)
  | Prime.      (* 玩家未释放秘密导致被惩罚 *)

  (* 定义 PlayerState 的比较函数 *)
Definition eqb_PlayerState (s1 s2 : PlayerState) : bool :=
  match s1, s2 with
  | Committed, Committed => true
  | Redeemed, Redeemed => true
  | _, _ => false
  end.

  (* 定义合约状态 *)
  Record State := build_state {
    player_a : Address;             (* 玩家 A 的地址 *)
    player_b : Address;             (* 玩家 B 的地址 *)
    secret_a : option N;            (* 玩家 A 的秘密 *)
    secret_b : option N;            (* 玩家 B 的秘密 *)
    state_a : PlayerState;          (* 玩家 A 的状态 *)
    state_b : PlayerState;          (* 玩家 B 的状态 *)
    deposit_a : Amount;             (* 玩家 A 存入的押金 *)
    deposit_b : Amount;             (* 玩家 B 存入的押金 *)
    deadline_t : nat;               (* 玩家 B 披露秘密的截止时间 t *)
    deadline_t_prime : nat;         (* 玩家 A 披露秘密的最终截止时间 t' *)
    winnings : option Address       (* 获胜者 *)
  }.

  (* 设置参数 *)
  Record Setup := build_setup {
    setup_player_a : Address;       (* 玩家 A 的地址 *)
    setup_player_b : Address;       (* 玩家 B 的地址 *)
    setup_deadline_t : nat;         (* 玩家 A、B 披露秘密的截止时间 t *)
    setup_deadline_t_prime : nat    (* 玩家 A、B 披露秘密的获取未产生奖金 t' *)
  }.

    (* 定义 State 的 Settable 实例 *)
  Instance state_settable : Settable State :=
    settable! build_state <player_a; player_b; secret_a; secret_b; state_a; state_b; deposit_a; deposit_b; deadline_t;deadline_t_prime ; winnings>.

  (* 定义 Setup 的 Settable 实例 *)
  Instance setup_settable : Settable Setup :=
    settable! build_setup <setup_player_a; setup_player_b; setup_deadline_t;setup_deadline_t_prime>.


  (* 定义消息类型 *)
  Inductive Msg :=
  | ClaimPrimeA                    (* 玩家 A 承诺秘密 a *)
  | ClaimPrimeB                    (* 玩家 B 承诺秘密 b *)
  | RevealSecretA (secret : N)       (* 玩家 A 披露秘密 a *)
  | RevealSecretB (secret : N)       (* 玩家 B 披露秘密 b *)
  | ClaimPenaltyA                    (* 玩家 A 在截止时间 t 后取回 B 的惩罚 *)
  | ClaimPenaltyB                    (* 玩家 B 在截止时间 t' 后取回 A 的惩罚 *)
  | ResolveWinner.                   (* 决定赢家 *)

  (* 定义错误类型 *)
  Definition Error : Type := nat.
  Definition default_error : Error := 1%nat.

  (* 序列化 *)
  Section Serialization.

    Global Instance Msg_serializable : Serializable Msg :=
      Derive Serializable Msg_rect<ClaimPrimeA, ClaimPrimeB, RevealSecretA, RevealSecretB, ClaimPenaltyA, ClaimPenaltyB, ResolveWinner>.

    Global Instance Setup_serializable : Serializable Setup :=
      Derive Serializable Setup_rect<build_setup>.

    Global Instance PlayerState_serializable : Serializable PlayerState :=
      Derive Serializable PlayerState_rect<Committed, Redeemed,Prime>.
  
    Global Instance State_serializable : Serializable State :=
      Derive Serializable State_rect<build_state>.

  End Serialization.

  (* 初始化合约 *)
  Definition init
             (chain : Chain)
             (ctx : ContractCallContext)
             (setup : Setup)
    : result State Error :=
    let time := chain.(current_slot) in
    if (setup.(setup_deadline_t) <=? setup.(setup_deadline_t_prime)) then
      Ok (build_state setup.(setup_player_a)
                      setup.(setup_player_b)
                      None
                      None
                      Committed
                      Committed
                      3 (* 玩家 A 押金 6B *)
                      3 (* 玩家 B 押金 6B *)
                      (time + setup.(setup_deadline_t))
                      (time + setup.(setup_deadline_t_prime))
                      None)
    else 
      Err default_error.

  (* 玩家 B 披露秘密 *)
  Definition reveal_secret_b
             (chain : Chain)
             (ctx : ContractCallContext)
             (state : State)
             (secret : N)
    : result (State * list ActionBody) Error :=
    match state.(secret_b) with
    | None =>
        if (ctx.(ctx_from) =? state.(player_b))%address
        then let new_state := state <| secret_b := Some secret |>
                                 <| state_b := Redeemed |> in
             let actions := [act_transfer state.(player_b) 2] in
             Ok (new_state, actions)
        else Err default_error
    | Some _ => Err default_error
    end.

  (* 玩家 A 披露秘密 *)
  Definition reveal_secret_a
             (chain : Chain)
             (ctx : ContractCallContext)
             (state : State)
             (secret : N)
    : result (State * list ActionBody) Error :=
    match state.(secret_a) with
    | None =>
        if (ctx.(ctx_from) =? state.(player_a))%address
        then let new_state := state <| secret_a := Some secret |>
                                 <| state_a := Redeemed |> in
             let actions := [act_transfer state.(player_a) 2] in
             Ok (new_state, actions)
        else Err default_error
    | Some _ => Err default_error
    end.

  (* 玩家 A 在截止时间 t 后取回 B 的惩罚 *)
  Definition claim_penalty_a
             (chain : Chain)
             (ctx : ContractCallContext)
             (state : State)
    : result (State * list ActionBody) Error :=
    if (state.(deadline_t) <=? chain.(current_slot))%nat
       && (ctx.(ctx_from) =? state.(player_a))%address
       && eqb_PlayerState state.(state_b) Committed
    then
      let new_state := state <| state_b := Redeemed |> in
      let actions := [act_transfer state.(player_a) 2] in
      Ok (new_state, actions)
    else Err default_error.

  (* 玩家 B 在截止时间 t 后取回 A 的惩罚 *)
  Definition claim_penalty_b
             (chain : Chain)
             (ctx : ContractCallContext)
             (state : State)
    : result (State * list ActionBody) Error :=
    if (state.(deadline_t) <=? chain.(current_slot))%nat
       && (ctx.(ctx_from) =? state.(player_b))%address
       && eqb_PlayerState state.(state_a) Committed
    then
      let new_state := state <| state_a := Redeemed |> in
      let actions := [act_transfer state.(player_b) 2] in
      Ok (new_state, actions)
    else Err default_error.


  (* 获胜规则 *)
  Parameter rule : N -> N -> bool.

  (* 决定赢家，任何人都可以调用 *)
  Definition resolve_winner
             (chain : Chain)
             (ctx : ContractCallContext)
             (state : State)
    : result (State * list ActionBody) Error :=
    match state.(winnings) with
    | None =>
      match state.(secret_a), state.(secret_b) with
      | Some a, Some b =>
          if rule a b
          then
            let new_state := state <| winnings := Some state.(player_a) |> in
            let actions := [act_transfer state.(player_a) 2] in
            Ok (new_state, actions)
          else
            let new_state := state <| winnings := Some state.(player_b) |> in
            let actions := [act_transfer state.(player_b) 2] in
            Ok (new_state, actions)
      | _, _ => Err default_error
      end
    | _ => Err default_error
    end.


    (* 玩家 A 在截止时间 t' 后取回 B 的惩罚 *)
  Definition claim_prime_a
             (chain : Chain)
             (ctx : ContractCallContext)
             (state : State)
    : result (State * list ActionBody) Error :=
    if (state.(deadline_t_prime) <? chain.(current_slot))%nat
       && eqb_PlayerState state.(state_b) Committed
       && eqb_PlayerState state.(state_a) Redeemed
    then
      let new_state := state <| state_b := Prime |> in
      let actions := [act_transfer state.(player_a) 2] in
      Ok (new_state, actions)
    else Err default_error.

  (* 玩家 B 在截止时间 t' 后取回 A 的惩罚 *)
  Definition claim_prime_b
             (chain : Chain)
             (ctx : ContractCallContext)
             (state : State)
    : result (State * list ActionBody) Error :=
    if (state.(deadline_t_prime) <? chain.(current_slot))%nat
       && eqb_PlayerState state.(state_a) Committed
       && eqb_PlayerState state.(state_b) Redeemed
    then
      let new_state := state <| state_a := Prime |> in
      let actions := [act_transfer state.(player_b) 2] in
      Ok (new_state, actions)
    else Err default_error.


  (* 接收函数 *)
  Definition receive
             (chain : Chain)
             (ctx : ContractCallContext)
             (state : State)
             (msg : option Msg)
    : result (State * list ActionBody) Error :=
    match msg with
    | Some (RevealSecretA secret) => reveal_secret_a chain ctx state secret
    | Some (RevealSecretB secret) => reveal_secret_b chain ctx state secret
    | Some ClaimPenaltyA => claim_penalty_a chain ctx state
    | Some ClaimPenaltyB => claim_penalty_b chain ctx state
    | Some ResolveWinner => resolve_winner chain ctx state
    | Some ClaimPrimeA => claim_prime_a chain ctx state
    | Some ClaimPrimeB => claim_prime_b chain ctx state
    | _ => Err default_error
    end.

  (* 定义合约 *)
  Definition contract : Contract Setup Msg State Error :=
    build_contract init receive.


  (* 玩家 A 披露秘密 *)
  Definition a_RevealSecretA (state : State) (caddr : Address) (n : N) : Action :=
    build_call state.(player_a) caddr 0 (RevealSecretA n).

  (* 玩家 B 披露秘密 *)
  Definition a_RevealSecretB (state : State) (caddr : Address) (n : N) : Action :=
    build_call state.(player_b) caddr 0 (RevealSecretB n).

  (* 玩家 A 索取惩罚 *)
  Definition a_ClaimPenaltyA (state : State) (caddr : Address) : Action :=
    build_call state.(player_a) caddr 0 ClaimPenaltyA.

  (* 玩家 B 索取惩罚 *)
  Definition a_ClaimPenaltyB (state : State) (caddr : Address) : Action :=
    build_call state.(player_b) caddr 0 ClaimPenaltyB.

  (* 决定赢家 *)
  Definition a_ResolveWinner (state : State) (player : Address) (caddr : Address) : Action :=
    build_call player caddr 0 ResolveWinner.

  (* 玩家 A 超时后取回余额 *)
  Definition a_ClaimPrimeA (state : State) (caddr : Address) : Action :=
    build_call state.(player_a) caddr 0 ClaimPrimeA.

  (* 玩家 B 超时后取回余额 *)
  Definition a_ClaimPrimeB (state : State) (caddr : Address) : Action :=
    build_call state.(player_b) caddr 0 ClaimPrimeB.

  Definition get_contract_state (state : ChainState) (addr : Address) : option State :=
      match env_contract_states state addr with
      | Some serialized_state =>
        deserialize serialized_state
      | None => None
      end.

  Variable caddr : Address.

  Variable s0 : ChainState.

  Hypothesis H_init: is_init_bstate contract caddr s0.

  Variable miner_address : Address.

  Hypothesis H_miner : address_not_contract miner_address = true.

  Lemma get_contract_state_correct :
    exists cstate, get_contract_state s0 caddr = Some cstate.
  Proof.
    intros.
    unfold is_init_bstate in H_init.
    destruct H_init.
    destruct H.
    destruct H0.
    destruct H1.
    destruct H2.
    destruct H2.
    destruct H2.
    destruct H2.
    exists x2.
    unfold get_contract_state .
    rewrite H2.
    setoid_rewrite deserialize_serialize.
    reflexivity.
  Qed.

  Variable init_cstate : State.

  Hypothesis H_state : get_contract_state s0 caddr = Some init_cstate.

  Definition playera := (init_cstate.(player_a)).

  Definition playerb := (init_cstate.(player_b)).

  Parameter generate_secret : Address -> N.

  Definition secretA := generate_secret playera.

  Definition secretB := generate_secret playerb.

  Definition player_a_strategy : strat miner_address :=
    fun s0 s tr [playera]  =>
      let time := current_slot s in
      match get_contract_state s caddr with
      | Some state =>
          match state.(state_a) with
          | Committed => 
              [a_RevealSecretA state caddr secretA ]
          | Redeemed => 
            match state.(state_b) with
            | Committed =>
              if (state.(deadline_t) <? time) then 
                [a_ClaimPenaltyA state caddr]
              else if (state.(deadline_t_prime) <? time) then 
                [a_ClaimPrimeA state caddr]
              else 
                []
            | Redeemed => 
              match state.(winnings) with
              | None => [a_ResolveWinner state state.(player_a) caddr]
              | _ => []
              end
            | _ => []
            end
          | _ => []
          end
      | None => []
      end.

      

  Definition Lottery_liquidity usr_strategy usr_addr env_strategy env_addrs :=
    delta_liquidity miner_address usr_strategy usr_addr env_strategy env_addrs caddr contract s0 .
  
  Lemma Lottery_liquidity_with_playa:
    forall player_b_strategy,
      Lottery_liquidity player_a_strategy [playera] player_b_strategy [playerb].
  Proof.
    unfold Lottery_liquidity.
    intros.
    unfold delta_liquidity.
    intros.
    exists 5000.
    do 2 eexists.
    
    assert(env_contracts s' caddr = Some (contract : WeakContract)).
    {
      admit.
    }
    assert(exists cstate , get_contract_state s' caddr = Some cstate).
    {
      admit.
    }
    destruct H6.
    rename x into cstate.
    destruct (state_a cstate) eqn : H_a_state.
    - assert (exists s1, transition miner_address s' (a_RevealSecretA cstate caddr secretA) = Ok s1 ).
      {
        admit.
      }
      destruct H7.
      eapply ULM_Step.
      lia.
      unfold stratDrive.
      exists (a_RevealSecretA cstate caddr secretA) , H7.
      split.
      unfold player_a_strategy.
      rewrite H6.
      rewrite H_a_state.
      intuition.
      intuition.
      eapply EPM_Step.
      assert((funds x caddr > 0)%Z). { admit. }
      eauto.
      intros.
      rename s'0 into s2.
      rename tr'0 into tr_s2.
      assert()


      


      
      exists H7.

    assert(cstate.())



    

    
  Qed.
  

  



Variable s0 : ChainState.

Variable 




End strat.
