
Require Import Monads.
Require Import Blockchain.
Require Import Containers.
Require Import Serializable.
Require Import Blockchain.
Require Import BoundedN.
Require Import ChainedList.
Require Import Containers.
Require Import Monads.
Require Import ResultMonad.
Require Import Serializable.
Require Import Automation.
Require Import Extras.
Require Import RecordUpdate.
From Coq Require Import ZArith.
From Coq Require Import Permutation.
From Coq Require Import List.
From Coq Require Import Psatz.

Import ListNotations.

Section InstanceBlockchain.

  Local Open Scope bool.

  Context {AddrSize : N}.
  Context {DepthFirst : bool}.

  Definition ContractAddrBase : N := AddrSize / 2.

  Global Instance LocalChainBase : ChainBase :=
    {| Address := BoundedN AddrSize;
      address_eqb := BoundedN.eqb;
      address_eqb_spec := BoundedN.eqb_spec;
      address_is_contract a := (ContractAddrBase <=? BoundedN.to_N a)%N
    |}.
  
  Record LocalChain :=
    build_local_chain {
      lc_height : nat;
      lc_slot : nat;
      lc_fin_height : nat;
      lc_account_balances : FMap Address Amount;
      lc_contract_state : FMap Address SerializedValue;
      lc_contracts : FMap Address WeakContract;
    }.

  Instance local_chain_settable : Settable _ :=
    settable! build_local_chain
    <lc_height; lc_slot; lc_fin_height;
     lc_account_balances; lc_contract_state; lc_contracts>.

  Definition lc_to_env (lc : LocalChain) : Environment :=
    {| env_chain :=
          {| chain_height := lc_height lc;
            current_slot := lc_slot lc;
            finalized_height := lc_fin_height lc; |};
      env_account_balances a := with_default 0%Z (FMap.find a (lc_account_balances lc));
      env_contract_states a := FMap.find a (lc_contract_state lc);
      env_contracts a := FMap.find a (lc_contracts lc); |}.
  
  Global Coercion lc_to_env : LocalChain >-> Environment.

  Section ExecuteActions.
    Local Open Scope Z.

    Definition add_balance
                (addr : Address)
                (amt : Amount)
                (lc : LocalChain)
                : LocalChain :=
      let update opt := Some (amt + with_default 0 opt) in
      lc<|lc_account_balances ::= FMap.partial_alter update addr|>.

    Definition transfer_balance
                (from to : Address)
                (amount : Amount)
                (lc : LocalChain)
                : LocalChain :=
      add_balance to amount (add_balance from (-amount) lc).

    Definition get_new_contract_addr (lc : LocalChain) : option Address :=
      BoundedN.of_N (ContractAddrBase + N.of_nat (FMap.size (lc_contracts lc))).

    Definition add_contract
                (addr : Address)
                (wc : WeakContract)
                (lc : LocalChain) : LocalChain :=
      lc<|lc_contracts ::= FMap.add addr wc|>.

    Definition set_contract_state
                (addr : Address)
                (state : SerializedValue)
                (lc : LocalChain) : LocalChain :=
      lc<|lc_contract_state ::= FMap.add addr state|>.

    Definition weak_error_to_error_init
                (r : result SerializedValue SerializedValue)
                : result SerializedValue ActionEvaluationError :=
      bind_error (fun err => init_failed err) r.

    Definition weak_error_to_error_receive
                (r : result (SerializedValue * list ActionBody) SerializedValue)
                : result (SerializedValue * list ActionBody) ActionEvaluationError :=
      bind_error (fun err => receive_failed err) r.

    Definition send_or_call
                (origin : Address)
                (from to : Address)
                (amount : Amount)
                (msg : option SerializedValue)
                (lc : LocalChain) : result (list Action * LocalChain) ActionEvaluationError :=
      do if amount <? 0 then Err (amount_negative amount) else Ok tt;
      do if amount >? env_account_balances lc from then Err (amount_too_high amount) else Ok tt;
      (* 查找接收地址是否为合约地址 *)
      match FMap.find to lc.(lc_contracts) with
      | None =>
        (* 如果 to 是一个合约地址，但没有找到对应的合约，返回错误 no_such_contract *)
        do if address_is_contract to then Err (no_such_contract to) else Ok tt;
        match msg with
          (* 即只是转账，没有消息 *)
          | None => Ok ([], transfer_balance from to amount lc)
          (* 如果 msg 不为 None，则返回错误 no_such_contract *)
          | Some msg => Err (no_such_contract to)
        end
      | Some wc =>
        (* 获取合约的状态，如果没有状态则返回内部错误 *)
        do state <- result_of_option (env_contract_states lc to) internal_error;
        let lc := transfer_balance from to amount lc in
        let ctx := build_ctx origin from to (env_account_balances lc to) amount in
        (* 调用合约的 receive 方法，返回的新的合约状态和新的动作 *)
        do '(new_state, new_actions) <- weak_error_to_error_receive (wc_receive wc lc ctx state msg);
        let lc := set_contract_state to new_state lc in
          Ok (map (build_act origin to) new_actions, lc)
      end.

    Definition deploy_contract
                (origin : Address)
                (from : Address)
                (amount : Amount)
                (wc : WeakContract)
                (setup : SerializedValue)
                (lc : LocalChain)
                : result (list Action * LocalChain) ActionEvaluationError :=
      do if amount <? 0 then Err (amount_negative amount) else Ok tt;
      do if amount >? env_account_balances lc from then Err (amount_too_high amount) else Ok tt;
      do contract_addr <- result_of_option (get_new_contract_addr lc) too_many_contracts;
      (* 查找接收地址是否为合约地址 *)
      do match FMap.find contract_addr (lc_contracts lc) with
        | Some _ => Err internal_error
        | None => Ok tt
        end;
      let lc := transfer_balance from contract_addr amount lc in
      let ctx := build_ctx origin from contract_addr amount amount in
      do state <- weak_error_to_error_init (wc_init wc lc ctx setup);
      let lc := add_contract contract_addr wc lc in
      let lc := set_contract_state contract_addr state lc in
      Ok ([], lc).

    Local Open Scope nat.

    Definition execute_action
                (act : Action)
                (lc : LocalChain)
                : result (list Action * LocalChain) ActionEvaluationError :=
      match act with
      | build_act origin from (act_transfer to amount) =>
        send_or_call origin from to amount None lc
      | build_act origin from (act_deploy amount wc setup) =>
        deploy_contract origin from amount wc setup lc
      | build_act origin from (act_call to amount msg) =>
        send_or_call origin from to amount (Some msg) lc
      end.

Definition execute_action_temp
  (act : Action)
  (lc : LocalChain)
  : result (list Action * LocalChain) ActionEvaluationError :=
  let temp_lc := lc in (* 在临时状态上操作 *)
  match act with
  | build_act origin from (act_transfer to amount) =>
      send_or_call origin from to amount None temp_lc
  | build_act origin from (act_deploy amount wc setup) =>
      deploy_contract origin from amount wc setup temp_lc
  | build_act origin from (act_call to amount msg) =>
      send_or_call origin from to amount (Some msg) temp_lc
  end.

Fixpoint execute_actions_with_recovery
  (count : nat)
  (acts : list Action)
  (lc : LocalChain)
  (depth_first : bool)
  : result LocalChain (list (Action * ActionEvaluationError)) :=
  match count, acts with
  | _, [] => Ok lc
  | 0, _ => Ok lc (* 达到深度限制时不再执行 *)
  | S count, act :: acts =>
    match execute_action_temp act lc with
    | Ok (next_acts, lc) =>
        let acts := if depth_first
                    then next_acts ++ acts
                    else acts ++ next_acts in
        execute_actions_with_recovery count acts lc depth_first
    | Err act_err =>
        (* 捕获失败，并继续执行其他动作 *)
        let acts := if depth_first
                    then acts
                    else acts in
        let errors := [(act, act_err)] in
        execute_actions_with_recovery count acts lc depth_first
    end
  end.


    Fixpoint execute_actions
              (count : nat)
              (acts : list Action)
              (lc : LocalChain)
              (depth_first : bool)
              : result LocalChain AddBlockError :=
      match count, acts with
      (* 执行完当前链中的所有动作 *)
      | _, [] => Ok lc
      | 0, _ => Err action_evaluation_depth_exceeded
      | S count, act :: acts =>
        match execute_action act lc with
        | Ok (next_acts, lc) =>
          let acts := if depth_first
                      then next_acts ++ acts
                      else acts ++ next_acts in
          execute_actions count acts lc depth_first
        | Err act_err =>
          Err (action_evaluation_error act act_err)
        end
      end.
  
Lemma transfer_balance_equiv
            (from to : Address)
            (amount : Amount)
            (lc : LocalChain)
            (env : Environment) :
      EnvironmentEquiv lc env ->
      EnvironmentEquiv
        (transfer_balance from to amount lc)
        (Blockchain.transfer_balance from to amount env).
    Proof.
      intros <-.
      apply build_env_equiv; auto.
      cbn.
      intros addr.
      unfold Amount in *.
      destruct_address_eq; subst;
        repeat
          (try rewrite FMap.find_partial_alter;
          try rewrite FMap.find_partial_alter_ne by auto;
          cbn); lia.
    Defined.

    Lemma set_contract_state_equiv addr state (lc : LocalChain) (env : Environment) :
      EnvironmentEquiv lc env ->
      EnvironmentEquiv
        (set_contract_state addr state lc)
        (Blockchain.set_contract_state addr state env).
    Proof.
      intros <-.
      apply build_env_equiv; auto.
      intros addr'.
      cbn.
      unfold set_chain_contract_state.
      destruct_address_eq.
      - subst. now rewrite FMap.find_add.
      - rewrite FMap.find_add_ne; auto.
    Defined.

    Lemma add_contract_equiv addr wc (lc : LocalChain) (env : Environment) :
      EnvironmentEquiv lc env ->
      EnvironmentEquiv
        (add_contract addr wc lc)
        (Blockchain.add_contract addr wc env).
    Proof.
      intros <-.
      apply build_env_equiv; auto.
      intros addr'.
      cbn.
      destruct_address_eq.
      - subst. now rewrite FMap.find_add.
      - rewrite FMap.find_add_ne; auto.
    Defined.

    Local Open Scope Z.
    Lemma gtb_le x y :
      x >? y = false ->
      x <= y.
    Proof.
      intros H.
      rewrite Z.gtb_ltb in H.
      apply Z.ltb_ge.
      auto.
    Defined.

    Lemma ltb_ge x y :
      x <? y = false ->
      x >= y.
    Proof.
      intros H.
      apply Z.ltb_ge in H.
      lia.
    Defined.

    Local Hint Resolve gtb_le ltb_ge : core.

    Lemma send_or_call_step origin from to amount msg act lc_before new_acts lc_after :
      send_or_call origin from to amount msg lc_before = Ok (new_acts, lc_after) ->
      act = build_act origin from (match msg with
                                  | None => act_transfer to amount
                                  | Some msg => act_call to amount msg
                                  end) ->
      ActionEvaluation lc_before act lc_after new_acts.
    Proof.
      intros sent act_eq.
      unfold send_or_call in sent.
      destruct (Z.ltb amount 0) eqn:amount_nonnegative;
        [cbn in *; congruence|].
      destruct (Z.gtb amount (env_account_balances lc_before from)) eqn:balance_enough;
        [cbn in *; congruence|].
      destruct (FMap.find to (lc_contracts lc_before)) as [wc|] eqn:to_contract.
      - (* there is a contract at destination, so do call *)
        destruct (env_contract_states _ _) as [prev_state|] eqn:prev_state_eq;
          [|cbn in *; congruence].
        cbn -[lc_to_env] in *.
        destruct (wc_receive wc _ _ _ _) as [[new_state resp_acts]|] eqn:receive;
          [|cbn in *; congruence].
        apply (eval_call origin from to amount wc msg prev_state new_state resp_acts);
          try solve [cbn in *; auto; congruence].
        + cbn in sent.
          inversion_clear sent.
          rewrite <- receive.
          auto.
        + inversion sent; subst;
            now apply set_contract_state_equiv, transfer_balance_equiv.
      - (* no contract at destination, so msg should be empty *)
        destruct (address_is_contract to) eqn:addr_format; cbn in *; try congruence.
        destruct msg; cbn in *; try congruence.
        assert (new_acts = []) by congruence; subst new_acts.
        apply (eval_transfer origin from to amount); auto.
        inversion sent; subst; now apply transfer_balance_equiv.
    Defined.

    Lemma get_new_contract_addr_is_contract_addr lc addr :
      get_new_contract_addr lc = Some addr ->
      address_is_contract addr = true.
    Proof.
      intros get.
      unfold get_new_contract_addr in get.
      pose proof (BoundedN.of_N_some get) as eq.
      destruct addr as [addr prf].
      cbn in *; rewrite eq.
      match goal with
      | [|- context[N.leb ?a ?b = true]] => destruct (N.leb_spec a b); auto; lia
      end.
    Defined.

    Local Hint Resolve get_new_contract_addr_is_contract_addr : core.
    Lemma deploy_contract_step origin from amount wc setup act lc_before new_acts lc_after :
      deploy_contract origin from amount wc setup lc_before = Ok (new_acts, lc_after) ->
      act = build_act origin from (act_deploy amount wc setup) ->
      ActionEvaluation lc_before act lc_after new_acts.
    Proof.
      intros dep act_eq.
      unfold deploy_contract in dep.
      destruct (Z.ltb amount 0) eqn:amount_nonnegative;
        [cbn in *; congruence|].
      destruct (Z.gtb amount (env_account_balances lc_before from)) eqn:balance_enough;
        [cbn in *; congruence|].
      destruct (get_new_contract_addr lc_before) as [contract_addr|] eqn:new_contract_addr;
        [|cbn in *; congruence].
      cbn -[incoming_txs] in dep.
      destruct (FMap.find _ _) eqn:no_contracts; [cbn in *; congruence|].
      destruct (wc_init _ _ _ _) as [state|] eqn:recv; [|cbn in *; congruence].
      cbn in dep.
      assert (new_acts = []) by congruence; subst new_acts.
      apply (eval_deploy origin from contract_addr amount wc setup state); eauto.
      inversion dep; subst lc_after.
      now apply set_contract_state_equiv, add_contract_equiv, transfer_balance_equiv.
    Defined.

    Local Hint Resolve send_or_call_step deploy_contract_step : core.
    Lemma execute_action_step
          (act : Action)
          (new_acts : list Action)
          (lc_before : LocalChain)
          (lc_after : LocalChain) :
      execute_action act lc_before = Ok (new_acts, lc_after) ->
      ActionEvaluation lc_before act lc_after new_acts.
    Proof.
      intros exec.
      unfold execute_action in exec.
      destruct act as [orig from body].
      destruct body as [to amount|to amount msg|amount wc setup]; eauto.
    Defined.

    Hint Constructors ChainStep : core.
    Hint Constructors ChainedList : core.
    Hint Unfold ChainTrace : core.

  End ExecuteActions.

  Definition lc_initial : LocalChain :=
    {| lc_height := 0;
      lc_slot := 0;
      lc_fin_height := 0;
      lc_account_balances := FMap.empty;
      lc_contract_state := FMap.empty;
      lc_contracts := FMap.empty; |}.

  Record LocalChainBuilder :=
    build_local_chain_builder {
      lcb_lc : LocalChain;
      lcb_trace : ChainTrace empty_state (build_chain_state lcb_lc []);
    }.

  Definition lcb_initial : LocalChainBuilder :=
    {| lcb_lc := lc_initial; lcb_trace := clnil |}.

  Definition validate_header (header : BlockHeader) (chain : Chain) : bool :=
    (block_height header =? S (chain_height chain))
    && (current_slot chain <? block_slot header)
    && (finalized_height chain <=? block_finalized_height header)
    && (block_finalized_height header <? block_height header)
    && negb (address_is_contract (block_creator header))
    && (block_reward header >=? 0)%Z.

  Lemma validate_header_valid header chain :
    validate_header header chain = true ->
    IsValidNextBlock header chain.
  Proof.
    intros valid.
    unfold validate_header in valid.
    repeat
      (match goal with
      | [H: context[Nat.eqb ?a ?b] |- _] => destruct (Nat.eqb_spec a b)
      | [H: context[Nat.ltb ?a ?b] |- _] => destruct (Nat.ltb_spec a b)
      | [H: context[Nat.leb ?a ?b] |- _] => destruct (Nat.leb_spec a b)
      | [H: context[Z.geb ?a ?b] |- _] => destruct (Z.geb_spec a b)
      end; [|repeat rewrite Bool.andb_false_r in valid; cbn in valid; congruence]).
    destruct (negb (address_is_contract (block_creator header))) eqn:to_acc;
      [|cbn in valid; congruence].
    apply Bool.negb_true_iff in to_acc.
    apply build_is_valid_next_block; cbn; auto.
    lia.
  Defined.

  Definition find_origin_neq_from (actions : list Action) : option Action :=
    find (fun act => negb (address_eqb (act_origin act) (act_from act))) actions.

    From Coq Require Import ssr.ssrbool.

  Lemma validate_origin_neq_from_valid actions :
    find_origin_neq_from actions = None ->
    Forall (fun act => address_eqb (act_origin act) (act_from act) = true) actions.
  Proof.
    intros find_none.
    unfold find_origin_neq_from in find_none.
    specialize (List.find_none _ _ find_none) as all_nin.
    cbn in *.
    assert (all_nin0 : forall x, In x actions -> (act_origin x =? act_from x)%address = true).
    { intros. apply ssrbool.negbFE. eauto. } 
    now apply Forall_forall in all_nin0.
  Defined.

  Definition find_invalid_root_action (actions : list Action) : option Action :=
    find (fun act => address_is_contract (act_from act)) actions.

  Lemma validate_actions_valid actions :
    find_invalid_root_action actions = None ->
    Forall (fun act => act_is_from_account act) actions.
  Proof.
    intros find_none.
    unfold find_invalid_root_action in find_none.
    specialize (List.find_none _ _ find_none) as all_nin.
    unfold act_is_from_account.
    now apply Forall_forall in all_nin.
  Defined.

  Definition add_new_block (header : BlockHeader) (lc : LocalChain) : LocalChain :=
    let lc := add_balance (block_creator header) (block_reward header) lc in
    lc<|lc_height := block_height header|>
      <|lc_slot := block_slot header|>
      <|lc_fin_height := block_finalized_height header|>.

  Lemma add_new_block_equiv header (lc : LocalChain) (env : Environment) :
    EnvironmentEquiv lc env ->
    EnvironmentEquiv
      (add_new_block header lc)
      (Blockchain.add_new_block_to_env header env).
  Proof.
    intros eq.
    apply build_env_equiv; try apply eq; auto.
    intros addr.
    cbn.
    unfold Blockchain.add_balance.
    destruct_address_eq.
    - subst. rewrite FMap.find_partial_alter.
      cbn.
      f_equal.
      apply eq.
    - rewrite FMap.find_partial_alter_ne; auto.
      apply eq.
  Defined.

  (* The computational bits of adding a block *)
  (* 用于在本地链（LocalChain）中添加一个区块（Block） *)
  Definition add_block_exec
            (depth_first : bool)
            (lc : LocalChain)
            (header : BlockHeader)
            (actions : list Action) : result LocalChain AddBlockError :=
    do (if validate_header header lc then Ok tt else Err (invalid_header header));
    do (match find_origin_neq_from actions with
        | Some act => Err (origin_from_mismatch act)
        | None => Ok tt
        end);
    do (match find_invalid_root_action actions with
        | Some act => Err (invalid_root_action act)
        | None => Ok tt
        end);
    let lc := add_new_block header lc in
    execute_actions 1000 actions lc depth_first.

  Local Hint Resolve validate_header_valid validate_actions_valid validate_origin_neq_from_valid : core.

  (* Adds a block to the chain by executing the specified chain actions.
    Returns the new chain if the execution succeeded (for instance,
    transactions need enough funds, contracts should not reject, etc. *)
  Definition add_block
            (depth_first : bool)
            (lcb : LocalChainBuilder)
            (header : BlockHeader)
            (actions : list Action) : result LocalChainBuilder AddBlockError.
  Proof.
    set (lcopt := add_block_exec depth_first (lcb_lc lcb) header actions).
    unfold add_block_exec in lcopt.
    destruct lcopt as [lc|e] eqn:exec; [|exact (Err e)].
    subst lcopt.
    destruct (validate_header _) eqn:validate; [|cbn in exec; congruence].
    destruct (find_origin_neq_from _) eqn:no_origin_neq_from; [cbn in exec; congruence|].
    destruct (find_invalid_root_action _) eqn:no_invalid_root_act; [cbn in exec; congruence|].
    destruct lcb as [prev_lc_end prev_lcb_trace].
    refine (Ok {| lcb_lc := lc; lcb_trace := _ |}).
    cbn -[execute_actions] in exec.

    refine (execute_actions_trace _ _ _ _ _ _ exec).
    refine (snoc prev_lcb_trace _).
    apply (step_block _ _ header); auto.
    apply add_new_block_equiv.
    reflexivity.
  Defined.

  Definition LocalChainBuilderImpl : ChainBuilderType :=
    {| builder_type := LocalChainBuilder;
      builder_initial := lcb_initial;
      builder_env lcb := lcb_lc lcb;
      builder_add_block := add_block DepthFirst;
      builder_trace := lcb_trace; |}.

End LocalBlockchain.

Arguments LocalChainBase : clear implicits.
Arguments LocalChainBuilder : clear implicits.
Arguments LocalChainBuilderImpl : clear implicits.
Arguments lcb_initial : clear implicits.

  


  
End InstanceBlockchain.

Definition Error : Type := nat.
Definition default_error: Error := 1%nat.
Section exec.

  Context {BaseTypes : ChainBase}.
  Set Primitive Projections.
  Set Nonrecursive Elimination Schemes.
  Context {AddrSize : N}.
  Context {DepthFirst : bool}.


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

  Local Open Scope Z.
  Variable contract_addr : Address.

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

  Definition correct_contract_addr (bstate : ChainState) (caddr : Address) : bool :=
    address_is_contract caddr && isNone (env_contracts bstate.(chain_state_env) caddr).

  Definition deploy_contract
              (origin : Address)
              (from : Address)
              (to : Address)
              (amount : Amount)
              (wc : WeakContract)
              (setup : SerializedValue)
              (bstate : ChainState)
              : result ChainState Error :=
    if negb (queue_isb_empty bstate) then
      Err default_error
    else
      let env := bstate.(chain_state_env) in
      if amount <? 0 then
        Err default_error
      else if amount >? env_account_balances env from then
        Err default_error
      else
        let contract_addr := to in
        if correct_contract_addr bstate contract_addr then
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


  Lemma deploy_contract_step origin from to amount wc setup act bstate  new_bstate :
    deploy_contract origin from to amount wc setup bstate = Ok new_bstate ->
      let new_acts := new_bstate.(chain_state_queue) in
      act = build_act origin from (act_deploy amount wc setup) ->
      ActionEvaluation (bstate.(chain_state_env)) act (new_bstate.(chain_state_env)) new_acts.
    Proof.
      intros dep new_acts act_eq.
      unfold deploy_contract in dep.
      destruct (negb (queue_isb_empty bstate)) eqn : H_queue;try congruence;cbn in *.
      destruct (Z.ltb amount 0) eqn:amount_nonnegative;
        [cbn in *; congruence|].
      destruct (Z.gtb amount (env_account_balances bstate from)) eqn:balance_enough;
        [cbn in *; congruence|].
      destruct (correct_contract_addr bstate to) eqn: ctr_addr;try congruence.
      destruct (wc_init _ _ _ _) as [state|] eqn:recv; [|cbn in *; congruence].
      assert (new_acts = []) . subst new_acts.
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
      destruct (env_contracts bstate to );try congruence.
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

  Definition stack_count := 10%nat.
  Definition Depth := true.

  Section envExec.

  Definition send_or_call_env
              (origin : Address)
              (from to : Address)
              (amount : Amount)
              (msg : option SerializedValue)
              (env : Environment)
              : result (Environment * list Action) Error :=
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
            Ok (new_env,[])  (* 空的动作队列 *)
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
            Ok (new_env,(map (build_act origin to) new_actions)) (* 将新生成的动作添加到动作队列中 *)
          end
        end
      end.
 
 Local Open Scope nat.
 
 Definition execute_action_env
             (act : Action)
             (env : Environment)
             : result (Environment * list Action) Error :=
   match act with
   | build_act origin from (act_transfer to amount) =>
     send_or_call_env origin from to amount None env
   | build_act origin from (act_call to amount msg) =>
     send_or_call_env origin from to amount (Some msg) env
   | _ => Err default_error
   end.
 
 Fixpoint execute_actions_env
               (count : nat)
               (acts : list Action)
               (lc : Environment)
               (depth_first : bool)
               : result Environment Error :=
       match count, acts with
       | _, [] => Ok lc
       | 0, _ => Err default_error
       | S count, act :: acts =>
         match execute_action_env act lc with
         | Ok (lc, next_acts) =>
           let acts := if depth_first
                       then next_acts ++ acts
                       else acts ++ next_acts in
           execute_actions_env count acts lc depth_first
         | Err default_error =>
         Err default_error
         end
       end.
 
  End envExec.

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
            (depth_first : bool)
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
        let new_acts := if depth_first
                        then new_bstate.(chain_state_queue) ++ acts (* 深度优先：先执行当前的动作 *)
                        else acts ++ new_bstate.(chain_state_queue) (* 广度优先：先执行队列中的动作 *) in
        let new_env := new_bstate.(chain_state_env) in
        (* 递归调用 execute_actions 继续处理新的动作 *)
        execute_actions count (build_chain_state new_env new_acts) depth_first
      | Err e =>
        Err e (* 如果执行失败，返回错误 *)
      end
    end.
  End cstExec.
  
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
    - (* there is a contract at destination, so do call *)
      destruct (env_contract_states _ _) as [prev_state|] eqn:prev_state_eq;
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
    - (* no contract at destination, so msg should be empty *)
      destruct (address_is_contract to) eqn:addr_format; cbn in *; try congruence.
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
  Lemma send_or_call_env_step origin from to amount msg act lc_before new_acts lc_after :
    send_or_call_env origin from to amount msg lc_before = Ok (lc_after ,new_acts ) ->
    act = build_act origin from (match msg with
                                | None => act_transfer to amount
                                | Some msg => act_call to amount msg
                                end) ->
    ActionEvaluation lc_before act lc_after new_acts.
  Proof.
    intros sent act_eq.
    unfold send_or_call_env in sent.
    destruct (Z.ltb amount 0) eqn:amount_nonnegative;
      [cbn in *; congruence|].
    destruct (Z.gtb amount (env_account_balances lc_before from)) eqn:balance_enough;
      [cbn in *; congruence|].
    destruct (env_contracts lc_before to) as [wc|] eqn:to_contract.
    - (* there is a contract at destination, so do call *)
      destruct (env_contract_states _ _) as [prev_state|] eqn:prev_state_eq;
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
        apply build_env_equiv; auto.
    - destruct (address_is_contract to) eqn:addr_format; cbn in *; try       congruence.
      destruct msg; cbn in *; try congruence.
      assert (new_acts = []).
      inversion sent. simpl. eauto.
      rewrite H.
      apply (eval_transfer origin from to amount); auto.
      lia. lia.
      inversion sent; subst.
      apply build_env_equiv; auto.
  Qed.
  
  Local Hint Resolve send_or_call_step send_or_call_env_step : core.
  
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


  Local Hint Resolve send_or_call_env_step : core.
  Lemma execute_action_env_step
            (act : Action)
            (new_acts : list Action)
            (lc_before : Environment)
            (lc_after : Environment) :
      execute_action_env act lc_before = Ok (lc_after,new_acts) ->
      ActionEvaluation lc_before act lc_after new_acts.
  Proof.
    intros exec.
    unfold execute_action_env in exec.
    destruct act as [orig from body].
    destruct body as [to amount|to amount msg|amount wc setup]; eauto.
    congruence.
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
    - (* Base case: count = 0 *)
      (* 当 count = 0 时，根据 execute_actions 的定义，如果动作队列不为空，将返回错误。 *)
      simpl in Hexec.
      destruct prev_bstate.(chain_state_queue) eqn:Hqueue.
      + (* 动作队列为空 *)
        inversion Hexec. subst.
        reflexivity.
      + (* 动作队列不为空 *)
        (* execute_actions 在这种情况下应该返回 Err，但 Hexec 告诉我们它返回了 Ok *)
        (* 矛盾，因此这种情况不会发生 *)
        discriminate Hexec.
    - (* Inductive step: count = S count' *)
      simpl in Hexec.
      destruct prev_bstate.(chain_state_queue) eqn:Hqueue.
      + (* 动作队列为空 *)
        inversion Hexec. subst.
        reflexivity.
      + (* 动作队列为 x :: xs *)
        (* 执行 execute_action *)
        destruct (execute_action a prev_bstate.(chain_state_env)) eqn:Hexec_act.
        * (* execute_action 返回 Ok *)
          destruct t as [env_after new_queue].
          (* 根据 depth_first，不同地更新 new_acts *)
          destruct df.
          -- (* df = true，深度优先 *)
              simpl in Hexec.
              set (new_acts := new_queue ++ l).
              (* 递归调用 execute_actions *)
              apply IH in Hexec.
              assumption.
          -- (* df = false，广度优先 *)
              simpl in Hexec.
              set (new_acts := l ++ new_queue).
              (* 递归调用 execute_actions *)
              apply IH in Hexec.
              assumption.
        * (* execute_action 返回 Err *)
          (* 这与 Hexec 返回 Ok 矛盾 *)
          discriminate Hexec.
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
  
  Lemma execute_actions_env_trace count acts_1 acts_2 (lc lc_final : Environment) df
  (trace : ChainTrace empty_state (build_chain_state lc (acts_1++acts_2))) :
  execute_actions_env count acts_1 lc df = Ok lc_final ->
  df = true ->
  ChainTrace (build_chain_state lc (acts_1++acts_2)) (build_chain_state lc_final acts_2).
  Proof.
    revert acts_1 acts_2 lc lc_final trace.
    induction count as [| count IH]; intros acts_1 acts_2 lc lc_final trace exec df_true; cbn in *.
    - destruct acts_1 eqn : acts.
      simpl in *. eauto.
      inversion exec.
      eauto.
      congruence.
    - destruct acts_1 as [|x xs] eqn : acts1'; try congruence.
      simpl in trace. eauto.
      inversion exec. eauto.
      destruct (execute_action_env x lc) as [[lc_after new_acts ]|] eqn:exec_once;
        cbn in *; try congruence.
      assert (step : ActionEvaluation lc x lc_after new_acts).
      {
          apply execute_action_env_step.
          eauto.
      }
      rewrite df_true in *.
      assert (step1 : ChainStep
      {| chain_state_env := lc; chain_state_queue := x :: xs ++ acts_2 |}
      {| chain_state_env := lc_after; chain_state_queue := new_acts ++ xs ++ acts_2 |}).
      {
        set (mid_bstate :=  {| chain_state_env := lc; chain_state_queue := x :: xs ++ acts_2 |}).
          set (next_bstate := {| chain_state_env := lc_after; chain_state_queue := new_acts ++ xs ++ acts_2 |}).
        (* 使用 step 构造这一步的 ChainTrace *)
        eapply step_action.
        eauto.
        eauto.
        eauto.
      }
      assert (s1 :reachable {| chain_state_env := lc; chain_state_queue := x :: xs ++ acts_2 |}).
      {
        apply trace_reachable in trace.
        eauto.
      }
      assert(s2 : reachable {| chain_state_env := lc_after; chain_state_queue := new_acts ++ xs ++ acts_2 |}).
      {
        eapply reachable_step.
        eauto.
        eauto.
      }
      unfold reachable in s2.
      assert (trace' : (ChainTrace empty_state
      {| chain_state_env := lc_after; chain_state_queue := new_acts ++ xs ++ acts_2 |})) by eauto.
      set (mid := {| chain_state_env := lc_after; chain_state_queue := (new_acts ++ xs)  ++ acts_2 |}).
  
      assert (trace1 : ChainTrace
      {| chain_state_env := lc_after; chain_state_queue := (new_acts ++ xs) ++ acts_2 |}
      {| chain_state_env := lc_final; chain_state_queue := acts_2 |}).
    {
      apply IH with (lc := lc_after) (lc_final := lc_final)
                    (acts_1 := new_acts ++ xs) (acts_2 := acts_2).
                    rewrite  app_assoc in trace'.
      eauto.
      eauto.
      eauto.
    }
    assert (trace2 : ChainTrace {| chain_state_env := lc; chain_state_queue := x :: xs ++ acts_2 |}
    {| chain_state_env := lc_after; chain_state_queue := new_acts ++ xs ++ acts_2 |}).
    {
      eauto. 
    }
    rewrite  app_assoc in trace2.
    set (final_trace := clist_app trace2 trace1).
    eauto.
  Qed.
  
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
            (depth_first:bool) 
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
                execute_actions stack_count new_bstate depth_first
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
    set(trace' := clist_app trace X).
    eauto.
  Qed.

End exec.

Section Strat.

  Context {BaseTypes : ChainBase}.
  Set Primitive Projections.
  Set Nonrecursive Elimination Schemes.
  Context {AddrSize : N}.
  Context {DepthFirst : bool}.
  Context {Setup Msg State Error : Type}
          `{Serializable Setup}
          `{Serializable Msg}
          `{Serializable State}
          `{Serializable Error}.



  Variable miner_address : Address.

  Axiom miner_always_eoa : address_is_contract miner_address = false.

  Global Definition depth_first := true.

  Global Definition miner_reward := 10%Z.

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
  


  Definition activesc (bstate : ChainState)
                      (caddr : Address) 
                      (contract : Contract Setup Msg State Error)
                      : Prop :=
  reachable bstate /\
  chain_state_queue bstate = [] /\
  env_contracts bstate caddr = Some (contract : WeakContract).

  Definition initial_contract_state
            (bstate : ChainState)
            (caddr : Address)
            (wc : WeakContract)
            : Prop :=
    reachable bstate /\
    bstate.(chain_state_queue) = [] /\
    env_contracts bstate caddr = Some wc /\
    let env := bstate.(chain_state_env) in
    exists ctx state setup,
      env_contract_states bstate caddr = Some state /\
      wc_init wc env ctx setup = Ok state.


  Lemma init_state_is_acive_aux  : 
    forall s (contract : Contract Setup Msg State Error)  caddr,
    reachable s -> 
    s.(chain_state_queue) = [] ->
    env_contracts s caddr = Some (contract: WeakContract) ->
    (exists env ctx state setup,
      env_contract_states s caddr = Some state /\
      wc_init contract env ctx setup = Ok state) ->
    activesc s caddr contract.
  Proof.
    intros * [].
    intros.
    unfold activesc .
    split.
    eapply trace_reachable in X.
    eauto.
    split.
    eauto.
    eauto.
  Qed.

  Lemma init_state_is_activesc  : 
    forall s (contract : Contract Setup Msg State Error)  caddr,
      initial_contract_state s caddr contract ->
      activesc s caddr contract.
  Proof.
    intros.
    unfold initial_contract_state in H3.
    destruct H3.
    destruct H4.
    destruct H5.
    eapply init_state_is_acive_aux;eauto.
  Qed.

  Definition NonStratLiquid (contract : Contract Setup Msg State Error) bstate caddr (trace : ChainTrace empty_state bstate): Prop :=
    activesc bstate caddr contract ->
    (funds bstate caddr > 0)%Z ->
    exists bstate',
      reachable_through bstate bstate' /\
      (funds bstate' caddr = 0)%Z.


  (* 添加记法，使得 tr ( s ) 可以被识别为 tr s *)
  Notation "trace( s )" := (ChainTrace empty_state s) (at level 10).

  Definition empty_action := 
    build_act miner_address miner_address (act_transfer miner_address 0).

  Definition is_empty_action (act : Action) : bool :=
    match act with
    | build_act from to (act_transfer to' amount) =>
        (address_eqb from to) && (address_eqb to to') && (amount =? 0)%Z
    | _ => false
    end.

  Definition delta_actions_with_empty delta s (tr_s : trace(s)) : list Action :=
    match (delta s tr_s) with
    | [] => [empty_action]
    | _ => (delta s tr_s) ++ [empty_action]
    end.
  
  Local Hint Unfold delta_actions_with_empty : core.


  (* 使用记法定义 strat *)
  Definition strat := forall s, trace(s) -> list Action.

  Definition wait_action n := 
    build_act miner_address miner_address (act_transfer miner_address n).

  Definition is_wait_action (act : Action) : bool :=
    match act with
    | build_act from to (act_transfer to' amount) =>
        (address_eqb from to) && (address_eqb to to') && (amount >? 0)%Z
    | _ => false
    end.

  Definition get_valid_header bstate : BlockHeader :=
    build_block_Header 
      (S (chain_height bstate))
      (current_slot bstate + 1)%nat
      (finalized_height bstate)
      miner_reward
      miner_address.

  Definition get_valid_header_forward_n bstate n: BlockHeader :=
    build_block_Header 
      (S (chain_height bstate))
      (current_slot bstate + n)%nat
      (finalized_height bstate)
      miner_reward
      miner_address. 

  Lemma queue_isb_empty_true : 
    forall bstate,
    queue_isb_empty bstate = true ->
    chain_state_queue bstate = [].
  Proof.
    intros.
    unfold queue_isb_empty in H3.
    destruct ( chain_state_queue bstate);try congruence;eauto.
  Qed.


  Definition transition
    (prev_bstate : ChainState)
    (act : Action) :result ChainState Strategy.Error :=
    if (queue_isb_empty prev_bstate) then
      let header := get_valid_header prev_bstate in
      if is_empty_action act then
        Ok prev_bstate
      else
        let header := get_valid_header prev_bstate in
        match add_block_exec depth_first prev_bstate header [act] with
        | Ok new_bstate => Ok new_bstate
        | Err _ => Err default_error
        end
    else 
      Err default_error.

  Lemma transition_emmpty_action:
    forall s,
      s.(chain_state_queue) = [] ->
      transition s empty_action = Ok s.
  Proof.
    intros.
    unfold transition.
    destruct (queue_isb_empty s) eqn : acts.
    - destruct (is_empty_action empty_action) eqn : H'.
      + eauto.
      + unfold is_empty_action in H'.
        simpl in H'.
        destruct_address_eq;try congruence.
        lia.
    - unfold queue_isb_empty in acts.
      destruct (chain_state_queue s) ;try congruence.
  Qed.

  Definition is_legal_action s a : bool :=
    match transition s a with
    | Ok _ => true
    | Err _ => false
    end.

  Parameter all_possible_actions : ChainState -> list Action.

  Axiom strat_subset_all_actions :
  forall (delta : strat) (s : ChainState) (tr_s : trace(s)),
    incl (delta s tr_s) (all_possible_actions s).

  (* 当前区块包含的所有合法动作，包含空动作 *)
  Definition legal_actions (s : ChainState) : list Action :=
    filter (fun a => is_legal_action s a) (all_possible_actions s).

  Definition delta_all : strat :=
    fun s tr_s => legal_actions s.

  (* 策略产生的任何动作都可以到一个状态，不会发生错误 *)
  Definition wellStrat (delta : strat) : Prop :=
    forall (s : ChainState) (tr_s : trace(s)),
      chain_state_queue s = [] ->
      Forall (fun a => exists s', transition s a = Ok s') (delta_actions_with_empty delta s tr_s).

  Lemma delta_all_is_wellStrat:
    wellStrat delta_all.
  Proof.
    unfold wellStrat.
    intros s  tr_s Hqueue.
    (* 展开 delta_actions_with_empty 的定义 *)
    unfold delta_actions_with_empty.
    unfold delta_all.
    unfold legal_actions.
    apply Forall_forall.
    intros a H_in.
    destruct (filter (fun a : Action => is_legal_action s a) (all_possible_actions s)) eqn:H_filter.
    - simpl in H_in.
      (* 因此 a = empty_action *)
      destruct H_in as [H_eq | H_in]; [| contradiction].
      subst a.
      exists s.
      eapply transition_emmpty_action.
      eauto.
    - apply in_app_or in H_in.
      destruct H_in as [H_in_filter | H_eq_empty].
      + rewrite <- H_filter in H_in_filter.
        apply filter_In in H_in_filter.
        destruct H_in_filter as [H_in_all_possible H_is_legal].
        (* 展开 is_legal_action 的定义 *)
        unfold is_legal_action in H_is_legal.
        destruct (transition s a) eqn:H_trans.
        * (* 情况：transition s a = Ok s' 成立 *)
          exists t.
          eauto.
        * (* 矛盾：is_legal_action s a = true, 但是 transition s a = Err _ *)
          discriminate H_is_legal.
      + simpl in H_eq_empty.
        destruct H_eq_empty.
        exists s.
        rewrite <- H3.
        eapply transition_emmpty_action.
        eauto.
        inversion H3.
  Qed.

  Lemma strategy_subset_delta_all :
    forall (delta : strat) s tr_s,
      wellStrat delta ->
      chain_state_queue s = [] ->
      incl (delta s tr_s) (delta_all s tr_s).
  Proof.
    intros delta s tr_s Hwell Hqueue a H_in.
    unfold delta_all.
    unfold legal_actions.
    apply filter_In.
    split.
    - unfold is_legal_action.
      unfold delta_actions_with_empty in H_in.
      destruct (delta s tr_s) eqn : d.
      + assert(is_empty_action a = true).
        simpl in H_in.
        destruct H_in;try congruence.
        unfold is_empty_action. simpl. destruct_address_eq;try congruence. simpl. eauto.
        inversion H3.
        simpl in H_in.
        inversion H_in.
      + 
        rewrite <- d in H_in.
        eapply strat_subset_all_actions in H_in.
        eauto.
    - unfold is_legal_action.
      destruct (transition s a) eqn:H_tr;eauto.
      exfalso.
      unfold wellStrat in Hwell.
      specialize(Hwell s tr_s).
      apply Forall_forall with (x := a) in Hwell;eauto.
      + destruct Hwell as [s' H_ok].
        rewrite H_tr in H_ok.
        discriminate.
      + unfold delta_actions_with_empty.
        destruct (delta s tr_s) eqn : d.
        * simpl in H_in.
          inversion H_in.
        * apply in_or_app.
          left.
          eauto.
  Qed.

  Lemma strategy_subset_delta_all_action :
  forall (delta : strat) s tr_s a,
    wellStrat delta ->
    chain_state_queue s = [] ->
    In a (delta s tr_s) ->
    In a (delta_all s tr_s).
  Proof.
    intros delta s tr_s a Hwell Hqueue H_in.
    unfold delta_all.
    unfold legal_actions.
    apply filter_In.
    split.
    - (* 证明 a ∈ all_possible_actions_with_empty s *)
      destruct (delta s tr_s) eqn : d.
      simpl in H_in.
      inversion H_in.
      rewrite  <-d in H_in.
      eapply strat_subset_all_actions.
      eauto.
    - unfold is_legal_action.
      destruct (transition s a) eqn:H_tr;eauto.
      exfalso.
      unfold wellStrat in Hwell.
      specialize(Hwell s tr_s).
      apply Forall_forall with (x := a) in Hwell;eauto.
      + destruct Hwell as [s' H_ok].
        rewrite H_tr in H_ok.
        discriminate.
      + unfold delta_actions_with_empty.
        destruct (delta s tr_s) eqn : d.
        * simpl in H_in.
          inversion H_in.
        * apply in_or_app.
          left.
          eauto.
  Qed.


  Lemma transition_reachable_through:
    forall (s s' : ChainState) (tr_s : trace(s)) a,
      reachable s ->
      s.(chain_state_queue) = [] ->
      transition s a = Ok s' ->
      reachable_through s s'.
  Proof.
    intros.
    unfold transition in H5.
    destruct (queue_isb_empty s) eqn : H_quueu;try congruence.
    destruct (is_empty_action a) eqn : H_empty;inversion H5.
    - rewrite <- H7.
      eapply reachable_through_refl.
      eauto.
    - destruct (add_block_exec depth_first s (get_valid_header s) [a]) eqn : Hadb.
      + inversion H5.  rewrite <- H8.
        assert (trace_1 : ChainTrace s t).
        {
          eapply add_block_reachable_through_aux in Hadb;eauto.
        }
        unfold reachable_through.
        split;eauto.
      + inversion H5. 
        (* rewrite <- H8.
        eauto. *)
  Qed.

  Lemma transition_next_state_queue_empty : 
    forall (s s' : ChainState) (tr_s : trace(s)) a,
      transition s a = Ok s' ->
      s'.(chain_state_queue) = [].
  Proof.
    intros.
    unfold transition in H3.
    destruct (queue_isb_empty s) eqn : H_queue;try congruence.
    destruct_match in H3.
    unfold queue_isb_empty  in H_queue.
    destruct (chain_state_queue s) eqn : h';try congruence.
    destruct (add_block_exec depth_first s (get_valid_header s) [a]) eqn :h'.
    - eapply add_block_next_state_queue_empty in h';eauto.
      inversion H3;subst.
      eauto.
    - apply queue_isb_empty_true. 
      inversion H3;subst.
      (* eauto. *)
  Qed.

  Lemma activesc_transition_activesc :
    forall (s s' : ChainState) (tr_s : trace(s)) a caddr contract,
    activesc s caddr contract ->
    transition s a = Ok s' ->
    activesc s' caddr contract.
  Proof.
    intros.
    unfold activesc in H3.
    destruct_and_split.
    assert(reachable_through s s').
    {
      eapply transition_reachable_through;eauto.
    }
    assert (chain_state_queue s' = []).
    {
      eapply transition_next_state_queue_empty;eauto.
    }
    assert(reachable s') by eauto.
    unfold activesc.
    repeat split;eauto.
    assert (trace( s')).
    {
      unfold transition in H4.
      destruct_match in H4;try congruence.
      destruct_match in H4;try congruence.
      destruct (add_block_exec depth_first s (get_valid_header s) [a]) eqn: h';try congruence.
      eapply add_block_reachable_through_aux in h';eauto.
      inversion H4.
      rewrite H11 in h'.
      set (final_trace := clist_app tr_s h').
      eauto.
    }
    eauto.
    eapply reachable_through_contract_deployed in H7;eauto.
  Qed.


  Lemma delta_actions_with_empty_include_empty_action:
    forall s tr_s delta,
      In empty_action (delta_actions_with_empty delta s tr_s).
  Proof.
    intros.
    unfold delta_actions_with_empty.
    destruct (delta s tr_s) eqn: actions.
    - simpl. eauto.
    - simpl. 
      right.
      simpl.
      apply in_or_app.
      right.
      simpl.
      eauto.
  Qed.

  Lemma delta_actions_with_empty_not_empty:
    forall delta s (tr_s : trace(s)),
      delta_actions_with_empty delta s (tr_s : trace(s)) <> [].
  Proof.
    intros.
    unfold delta_actions_with_empty.
    destruct (delta s tr_s) eqn : h';try congruence;eauto.   
  Qed.

  (* 单纯的表示两个状态间的关系是策略引起的 *)
  Definition stratSucc  (s s' : ChainState)
                        (tr_s : trace(s))
                        (delta : strat)
                        : Prop :=
    exists (a : Action),
      (In a (delta_actions_with_empty delta s tr_s)) /\
      transition s a = Ok s'.

  Lemma wellStrat_has_exist_next_state :
    forall (delta : strat) (s : ChainState) (tr_s : trace(s)),
      wellStrat(delta) ->
      s.(chain_state_queue) = [] ->
      exists s',
        stratSucc s s' tr_s delta.
  Proof.
    intros * HwellStrat Hqueue.
    unfold wellStrat in HwellStrat.
    destruct (delta_actions_with_empty delta s tr_s) as [| a actions] eqn:Hdelta.
    apply delta_actions_with_empty_not_empty in Hdelta.
    inversion Hdelta.
    specialize(HwellStrat s tr_s).
    rewrite Hdelta in HwellStrat.
    eapply Forall_inv in HwellStrat.
    destruct HwellStrat as [s' Htransition].
    (* Now, stratSucc s s' tr_s delta holds *)
    exists s'.
    unfold stratSucc.
    exists a.
    split.
    + (* a ∈ delta s tr_s *)
      rewrite Hdelta. simpl. left. reflexivity.
    + (* transition s a = Ok s' *)
      assumption.
    + eauto.
  Qed.

Lemma stratSucc_reachable_through:
  forall (s s' : ChainState) (tr_s : trace(s)) (delta : strat) ,
    chain_state_queue s = [] ->
    stratSucc s s' tr_s delta ->
    reachable_through s s'.
Proof.
  intros.
  unfold stratSucc in H4.
  destruct_and_split.
  assert(HReachable: trace( s)) by eauto.
  eapply trace_reachable in HReachable.
  eapply transition_reachable_through; eauto.
Qed.

Lemma transition_reachable_prev_next_trace : 
  forall (s s' : ChainState) (tr_s : trace(s)) a,
    reachable s ->
    s.(chain_state_queue) = [] ->
    transition s a = Ok s' ->
    ChainTrace s s'.
Proof.
  intros.
  unfold transition in H5.
  destruct_match in H5;try congruence.
  destruct_match in H5;try congruence.
  inversion H5. subst.
  apply clnil.
  destruct (add_block_exec depth_first s (get_valid_header s) [a]) eqn : H';try congruence.
  eapply add_block_reachable_through_aux in H';eauto.
  inversion H5. subst.
  eauto.
  (* inversion H5. subst.
  apply clnil. *)
Qed.


  Lemma activesc_stratSucc_activesc :
    forall (s s' : ChainState) (tr_s : trace(s)) caddr contract delta,
    activesc s caddr contract ->
    stratSucc s s' tr_s delta ->
    activesc s' caddr contract.
  Proof.
    intros.
    unfold activesc.
    split.
    eapply stratSucc_reachable_through in H4.
    eapply trace_reachable in tr_s.
    eauto.
    unfold activesc in H3.
    destruct_and_split.
    eauto.
    split.
    unfold stratSucc in H4.
    destruct_and_split.
    eapply transition_next_state_queue_empty in H5;eauto.
    unfold stratSucc in H4.
    eapply stratSucc_reachable_through in H4.
    unfold activesc in H3.
    destruct_and_split.
    eapply reachable_through_contract_deployed in H6;eauto.
    unfold activesc in H3.
    destruct_and_split.
    eauto.
  Qed.


  Lemma wellStrat_stratSucc_refl :
    forall s tr_s delta caddr contract,
      activesc s caddr contract ->
      wellStrat(delta) ->
      stratSucc s s tr_s delta.   
  Proof.
    intros.
    unfold stratSucc.
    unfold wellStrat in H4.
    specialize(H4 s tr_s).
    exists empty_action.
    split.
    eapply delta_actions_with_empty_include_empty_action.
    apply transition_emmpty_action.
    unfold activesc in H3.
    destruct_and_split.
    eauto.
  Qed.


  (* 证明 (0 > 0)%nat 等价于 False *)
  Lemma gt0_0_false : (0 > 0)%nat <-> False.
  Proof.
    unfold gt.
    split.
    - (* (0 > 0)%nat -> False *)
      intros H'.
      (* 在 Coq 中，Nat.lt_irrefl n 表示 n < n 不成立 *)
      apply Nat.lt_irrefl with (x := 0).
      assumption.
    - (* False -> (0 > 0)%nat *)
      intros H'.
      destruct H'.
  Qed.


  Definition greater_than (x y : nat) : bool :=
    if Nat.ltb y x then true else false.

  Infix ">?" := greater_than (at level 70, no associativity).

  Lemma greater_than_zero : forall n : nat, (n >? 0) = true -> n > 0.
  Proof.
    clear H.
    intros n H.
    unfold greater_than in H.
    destruct (Nat.ltb 0 n) eqn:Hlt.
    - apply Nat.ltb_lt in Hlt.
      exact Hlt.
    - discriminate H.
  Qed.


  (* 单纯的表示两个状态间的关系是策略引起的,且不是空 *)
  Definition nonEmptyStratSucc (s s' : ChainState)
                            (tr_s : trace(s))
                            (delta : strat)
                            : Prop :=
    exists (a : Action),
      (In a (delta_actions_with_empty delta s tr_s)) /\
      (is_empty_action a = false) /\ 
      transition s a = Ok s'.

  Lemma nonEmptyStratSucc_reachable_through:
    forall (s s' : ChainState) (tr_s : trace(s)) (delta : strat) ,
      chain_state_queue s = [] ->
      nonEmptyStratSucc s s' tr_s delta ->
      reachable_through s s'.
  Proof.
    intros.
    unfold nonEmptyStratSucc  in H4.
    destruct_and_split.
    assert(HReachable: trace( s)) by eauto.
    eapply trace_reachable in HReachable.
    eapply transition_reachable_through; eauto.
  Qed.

  Lemma activesc_nonEmptyStratSucc_activesc :
    forall (s s' : ChainState) (tr_s : trace(s)) caddr contract delta,
    activesc s caddr contract ->
    nonEmptyStratSucc s s' tr_s delta ->
    activesc s' caddr contract.
  Proof.
    intros.
    unfold activesc.
    split.
    eapply nonEmptyStratSucc_reachable_through in H4.
    eapply trace_reachable in tr_s.
    eauto.
    unfold activesc in H3.
    destruct_and_split.
    eauto.
    split.
    unfold nonEmptyStratSucc in H4.
    destruct_and_split.
    eapply transition_next_state_queue_empty in H6;eauto.
    unfold nonEmptyStratSucc in H4.
    eapply nonEmptyStratSucc_reachable_through in H4.
    unfold activesc in H3.
    destruct_and_split.
    eapply reachable_through_contract_deployed in H6;eauto.
    unfold activesc in H3.
    destruct_and_split.
    eauto.
  Qed.

  (* 不包含非空动作的策略后继 *)
  Inductive multiNonEmptyStratSucc (delta : strat): ChainState -> ChainState -> Prop :=
    | MNESS_refl : forall s,
      multiNonEmptyStratSucc delta s s
    | MNESS_step : forall s s' s'' tr_s,
      nonEmptyStratSucc s s' tr_s delta ->
      multiNonEmptyStratSucc delta  s' s'' ->
      multiNonEmptyStratSucc delta  s s''.

  Lemma multiNonEmptyStratSucc_reachable_through:
    forall (s s' : ChainState) (tr_s : trace(s)) (delta : strat) contract caddr,
      activesc s contract caddr ->
      multiNonEmptyStratSucc delta s s' ->
      reachable_through s s'.
  Proof.
    intros.
    assert(Hacs:activesc s contract caddr) by eauto.
    unfold activesc in H3.
    destruct_and_split.
    induction H4.
    subst.
    eapply reachable_through_refl;eauto.
    assert (reachable_through s s').
    {
      eapply nonEmptyStratSucc_reachable_through.
      eauto.
      eauto.    
    }
    assert(Hsss:nonEmptyStratSucc s s' tr_s0 delta) by eauto.
    unfold nonEmptyStratSucc in H4.
    destruct H4.
    destruct_and_split.
    assert(ChainTrace s s').
    {
      eapply transition_reachable_prev_next_trace;eauto.    
    }
    set(t_trace := clist_app tr_s X).
    assert(tr_s':trace(s')) by eauto.
    assert(reachable s') by eauto.
    assert(activesc s' contract caddr).
    {
      eapply activesc_nonEmptyStratSucc_activesc;eauto.
    }
    assert(Hasc':activesc s' contract caddr) by eauto.
    unfold activesc in H12.
    destruct_and_split.
    specialize(IHmultiNonEmptyStratSucc tr_s' H11 H13 H14 Hasc').
    eauto.
  Qed.

  Lemma active_multiNonEmptyStratSucc_active:
    forall (s s' : ChainState) (tr_s : trace(s)) (delta : strat) contract caddr,
      activesc s contract caddr ->
      multiNonEmptyStratSucc delta s s' ->
      activesc s' contract caddr.
  Proof.
    intros.
    induction H4.
    - eauto.
    - assert(activesc s' contract caddr).
      {
        eapply activesc_nonEmptyStratSucc_activesc in H4;eauto.
      }
      unfold nonEmptyStratSucc in H4.
      destruct H4.
      destruct_and_split.
      eapply transition_reachable_prev_next_trace in H8;eauto.
      set(tr := clist_app tr_s H8).
      specialize(IHmultiNonEmptyStratSucc tr H6).
      eauto.
      eapply trace_reachable in tr_s;eauto.
      unfold activesc in H3.
      destruct_and_split.
      eauto.
  Qed.
  

  Definition maxStratExec (delta : strat) (caddr : Address) s s': Prop :=
    multiNonEmptyStratSucc delta s s' /\
    (forall a tr_s', In a (delta_actions_with_empty delta s' tr_s') -> is_empty_action a = true).

  Lemma maxStratExec_terminal :
    forall (delta : strat) (caddr : Address) s s',
      maxStratExec delta caddr s s' ->
      (forall s'', multiNonEmptyStratSucc delta s' s'' -> s'' = s').
  Proof.
    clear H H0 H1 H2.
    intros delta caddr s s' [Hsucc Hmax].
    intros s'' Hmulti.
    induction Hmulti.
    - reflexivity.
    - destruct H as [a [Hin Htrans]].
      specialize (Hmax a tr_s).
      apply Hmax in Hin.
      destruct_and_split.
      congruence.
  Qed.

  Lemma maxStratExec_reachable_through:
    forall (s s' : ChainState) (tr_s : trace(s)) (delta : strat) contract (caddr:Address),
      activesc s caddr contract ->
      maxStratExec delta caddr s s' -> 
      reachable_through s s'.
  Proof.
    intros.
    unfold maxStratExec in H4.
    destruct_and_split.
    eapply multiNonEmptyStratSucc_reachable_through in H3;eauto.
  Qed.




  
  (* 表示前缀 usr和env混合的前缀 *)
  Inductive InteractionSuccessionEnv (delta_env delta_usr : strat) : ChainState -> ChainState -> Prop :=
  | ISE_End : forall s,
      InteractionSuccessionEnv delta_env delta_usr s s
  (* 这个环境中不需要forall了 *)
  | ISE_Step : forall s s1 s2 (tr_s:trace(s)),
      multiNonEmptyStratSucc delta_env s s1 ->
      InteractionSuccessionUsr delta_env delta_usr s1 s2 ->
      InteractionSuccessionEnv delta_env delta_usr s s2
  with InteractionSuccessionUsr (delta_env delta_usr : strat) : ChainState -> ChainState -> Prop :=
  | ISU_End : forall s,
      InteractionSuccessionUsr delta_env delta_usr s s
  | ISU_Step : forall s s1 s2 (tr_s:trace(s)),
      stratSucc s s1 tr_s delta_usr ->
      InteractionSuccessionEnv delta_env delta_usr s1 s2 ->
      InteractionSuccessionUsr delta_env delta_usr s s2.

  Scheme ise_mut := Induction for InteractionSuccessionEnv Sort Prop
  with isu_mut := Induction for InteractionSuccessionUsr Sort Prop.

  Lemma interactionSuccessionEnv_reachable_through delta_env delta_usr contract caddr:
    forall s (tr_s:trace(s)) s' ,
      activesc s  caddr contract ->
      InteractionSuccessionEnv delta_env delta_usr s s' ->
      reachable_through s s'.
  Proof.
    intros s tr_s s' Hactive Hinteraction.
    apply (ise_mut delta_env delta_usr
    (* P : For InteractionSuccessionEnv *)
    (fun s0 s'0 (_ : InteractionSuccessionEnv delta_env delta_usr s0 s'0) =>
        activesc s0  caddr contract -> reachable_through s0 s'0)
    (* P0 : For InteractionSuccessionUsr *)
    (fun s0 s'0 (_ : InteractionSuccessionUsr delta_env delta_usr s0 s'0) =>
        activesc s0  caddr contract -> reachable_through s0 s'0)
    ).
    - intros.
      unfold activesc in H3.
      destruct_and_split.
      eauto.
    - intros.
      assert(reachable_through s0 s1).
      {
        eapply multiNonEmptyStratSucc_reachable_through in m;eauto.
      }
      eapply active_multiNonEmptyStratSucc_active in m;eauto.
    - intros.
      unfold activesc in H3.
      destruct_and_split;eauto.
    - intros.
      assert(reachable_through s0 s1).
      {
        unfold activesc in H4.
        destruct_and_split.
        eapply stratSucc_reachable_through in H5;eauto.
      }
      assert(activesc s1  caddr contract).
      {
      eapply activesc_stratSucc_activesc in s3;eauto.     
      }
      specialize(H3 H6).
      eauto.
    - eauto.
    - eauto.
  Qed.


  Lemma activesc_InteractionSuccessionEnv_activesc delta_env delta_usr contract caddr:
    forall s (tr_s:trace(s)) s' ,
      activesc s  caddr contract->
      InteractionSuccessionEnv delta_env delta_usr s s' ->
      activesc s' caddr contract.
  Proof.
    intros s tr_s s' Hactive Hinteraction.
    eapply (ise_mut delta_env delta_usr
    (* Predicate P for InteractionSuccessionEnv *)
    (fun s0 s'0 _ => activesc s0  caddr  contract-> activesc s'0  caddr contract)
    (* Predicate P0 for InteractionSuccessionUsr *)
    (fun s0 s'0 _ => activesc s0  caddr contract -> activesc s'0  caddr contract)
    );eauto.
    - intros.
      eapply active_multiNonEmptyStratSucc_active in m;eauto.
    - intros.
      eapply activesc_stratSucc_activesc in s3;eauto.
  Qed.
  
  (* 这个表示流动性要求 *)
  Inductive UserLiquidatesInNSteps (delta_env delta_usr : strat) (caddr : Address) :
  nat -> ChainState -> ChainState -> Prop :=
  | UL_Base : forall s n (tr_s : trace(s)),
      (funds s caddr = 0)%Z ->
      UserLiquidatesInNSteps delta_env delta_usr caddr n s s
  | UL_Step : forall n s (tr_s : trace(s)) s' s'',
      (funds s caddr > 0)%Z ->
      n > 0 ->
      stratSucc s s' tr_s delta_usr ->
      envProgress delta_env delta_usr caddr (n - 1) s' s'' ->
      UserLiquidatesInNSteps delta_env delta_usr caddr n s s''
  with envProgress (delta_env delta_usr : strat) (caddr : Address) :
  nat -> ChainState -> ChainState -> Prop :=
  | Env_Base : forall n s (tr_s : trace(s)),
      (funds s caddr = 0)%Z ->
      envProgress delta_env delta_usr caddr n s s
  | Env_Step : forall n s (tr_s : trace(s)) s'',
      (funds s caddr > 0)%Z ->
      (forall s',
        multiNonEmptyStratSucc delta_env s s' ->
        UserLiquidatesInNSteps delta_env delta_usr caddr n s' s'' ) ->
      envProgress delta_env delta_usr caddr n s s''.

  Scheme ul_mut := Induction for envProgress Sort Prop
  with env_mut := Induction for UserLiquidatesInNSteps Sort Prop.
  
  Lemma envProgress_reachable_through delta_env delta_usr contract caddr:
    forall s (tr_s:trace(s)) s' n ,
      activesc s caddr contract ->
      envProgress delta_env delta_usr caddr n s s' ->
      reachable_through s s'.
  Proof.
    intros s tr_s s' n Hactive Hinteraction.
    eapply (ul_mut delta_env delta_usr caddr
    (* P : For InteractionSuccessionEnv *)
    (fun n s0 s'0 (_ : envProgress delta_env delta_usr caddr n s0 s'0) =>
        activesc s0 caddr contract -> reachable_through s0 s'0)
    (* P0 : For InteractionSuccessionUsr *)
    (fun n s0 s'0 (_ : UserLiquidatesInNSteps delta_env delta_usr caddr n s0 s'0) =>
        activesc s0  caddr contract -> reachable_through s0 s'0)
    ).
    - intros.
      unfold activesc in H3.
      destruct_and_split.
      eauto.
    - intros.
      specialize(H3 s0).
      destruct H3.
      + eapply MNESS_refl.
      + eauto.
      + econstructor;eauto.
    - intros.
      unfold activesc in H3.
      destruct_and_split;eauto.
    - intros.
      assert(activesc s'0 caddr contract).
      {
        eapply activesc_stratSucc_activesc in s1;eauto.
      }
      eapply H3 in H5.
      unfold activesc in H4.
      destruct_and_split.
      eapply stratSucc_reachable_through in s1;eauto.
    - eauto.
    - eauto.
  Qed.

  Lemma userLiquidatesInNSteps_reachable_through delta_env delta_usr contract caddr:
  forall s (tr_s:trace(s)) s' n ,
    activesc s caddr contract ->
    UserLiquidatesInNSteps delta_env delta_usr caddr n s s' ->
    reachable_through s s'.
  Proof.
    intros.
    induction H4.
    - unfold activesc in H3.
      destruct_and_split.
      eauto.
    - assert(reachable_through s s').
      {
        eapply stratSucc_reachable_through in H6.
        eauto.
        unfold activesc in H3.
        destruct_and_split.
        eauto.
      }
      assert( activesc s' caddr contract).
      {
        eapply activesc_stratSucc_activesc in H6.
        eauto.
        eauto.
      }
      assert( stratSucc s s' tr_s0 delta_usr) by eauto.
      unfold stratSucc in H10.
      destruct H10.
      destruct_and_split.
      assert(trace(s')).
      {
        eapply transition_reachable_prev_next_trace in H11.
        set(tr_s' := clist_app tr_s H11).
        eauto.
        eauto.
        eapply trace_reachable in tr_s.
        eauto.
        unfold activesc in H3.
        destruct_and_split.
        eauto.
      }
      eapply envProgress_reachable_through in H7;eauto.
  Qed.

  Lemma activesc_envProgress_activesc delta_env delta_usr contract caddr:
    forall s n (tr_s:trace(s)) s',
      activesc s caddr contract ->
      envProgress delta_env delta_usr caddr n s s' ->
      activesc s' caddr contract .
  Proof.
    intros s tr_s s' n Hactive Hinteraction.
    eapply (ul_mut delta_env delta_usr caddr
    (* Predicate P for InteractionSuccessionEnv *)
    (fun n s0 s'0 _ => activesc s0  caddr contract-> activesc s'0  caddr contract)
    (* Predicate P0 for InteractionSuccessionUsr *)
    (fun n s0 s'0 _ => activesc s0  caddr contract-> activesc s'0  caddr contract)
    );eauto.
    - intros.
      specialize(H3 s0).
      destruct H3.
      eapply MNESS_refl.
      eauto.
      unfold activesc.
      split.
      eauto.
      destruct_and_split;eauto.
    - intros.
      assert(activesc s'0 caddr contract).
      {
        eapply activesc_stratSucc_activesc in s1;eauto.
      }
      apply H3 in H5.
      eauto. 
  Qed.

  Lemma activesc_userLiquidatesInNSteps_activesc delta_env delta_usr contract caddr:
  forall s n (tr_s:trace(s)) s',
    activesc s caddr contract ->
    UserLiquidatesInNSteps delta_env delta_usr caddr n s s' ->
    activesc s' caddr contract.
  Proof.
    intros.
    induction H4.
    - eauto.
    - assert(stratSucc s s' tr_s0 delta_usr) by eauto.
      unfold stratSucc in H8.
      destruct H8.
      destruct_and_split.
      assert(tr_s' : trace(s')).
      {
        eapply transition_reachable_prev_next_trace in H9;eauto.
        eapply (clist_app tr_s  H9).
        unfold activesc in H3;
        destruct_and_split;eauto.
        unfold activesc in H3;
        destruct_and_split;eauto.
      }
      eapply activesc_envProgress_activesc in H7;eauto.
      eapply activesc_stratSucc_activesc;eauto.
  Qed.

  Lemma userLiquidatesInNSteps_zero delta_env delta_usr contract caddr:
  forall s n (tr_s:trace(s)) s',
    activesc s caddr contract ->
    UserLiquidatesInNSteps delta_env delta_usr caddr n s s' ->
    (funds s' caddr = 0)%Z.
  Proof.
    intros.
    eapply (env_mut delta_env delta_usr caddr
    (* Predicate P for InteractionSuccessionEnv *)
    (fun n s0 s'0 _ => activesc s0  caddr contract-> (funds s'0 caddr = 0)%Z)
    (* Predicate P0 for InteractionSuccessionUsr *)
    (fun n s0 s'0 _ => activesc s0  caddr contract-> (funds s'0 caddr = 0)%Z)
    );eauto.
    - intros.
      specialize(H5 s0).
      destruct H5.
      eapply MNESS_refl.
      eauto.
      eauto.
    - intros.
      eapply activesc_stratSucc_activesc in s1;eauto.
  Qed.

  Lemma envProgress_zero delta_env delta_usr contract caddr:
  forall s n (tr_s:trace(s)) s',
    activesc s caddr contract ->
    envProgress delta_env delta_usr caddr n s s' ->
    (funds s' caddr = 0)%Z.
  Proof.
    intros.
    inversion H4.
    - lia.
    - specialize(H6 s).
      assert(multiNonEmptyStratSucc delta_env s s) by eapply MNESS_refl.
      eapply H6 in H10.
      eapply userLiquidatesInNSteps_zero in H10;eauto.
  Qed.


  Definition delta_empty : strat :=
    fun s tr_s => [].

  Lemma multiNonEmptyStratSucc_no_progree_delta_empty:
    forall s s' (tr_s : trace(s)),
      multiNonEmptyStratSucc delta_empty s s' ->
      s = s'.
  Proof.
    intros.
    unfold delta_empty in H3.
    inversion H3.
    eauto.
    unfold nonEmptyStratSucc in H4.
    destruct H4.
    destruct_and_split.
    unfold delta_actions_with_empty in H4.
    simpl in H4.
    destruct H4.
    - unfold is_empty_action in H8.
      rewrite <-H4 in H8.
      simpl in H8.
      destruct_address_eq;try congruence.
      simpl in H8.
      congruence.
    - inversion H4.
  Qed.

(* transition_through *)


Inductive TransitionStep (prev_bstate : ChainState) (next_bstate : ChainState) :=
| step_trans :
    forall (a :Action),
      transition prev_bstate a = Ok next_bstate ->
      TransitionStep prev_bstate next_bstate.

Definition TransitionTrace := ChainedList ChainState TransitionStep.

Definition is_init_bstate (contract : Contract Setup Msg State Error) (init_bstate : ChainState) :=
  exists caddr,
  reachable init_bstate /\
  chain_state_queue init_bstate = [] /\
  env_contracts init_bstate caddr = Some (contract : WeakContract) /\
  let env := init_bstate.(chain_state_env) in
  exists ctx setup state,
    env_contract_states init_bstate caddr = Some (serialize state) /\
    init contract env ctx setup = Ok state.

Definition transition_reachable (contract : Contract Setup Msg State Error)  (state : ChainState) :=
  exists init_bstate,
  is_init_bstate contract init_bstate /\
  inhabited (TransitionTrace init_bstate state).

Definition transition_through contract mid to := transition_reachable contract mid /\ inhabited (TransitionTrace mid to).

Definition activesc_transition (bstate : ChainState)
                                (caddr : Address) 
                                (contract : Contract Setup Msg State Error)
                                : Prop :=
  transition_reachable contract bstate /\
  chain_state_queue bstate = [].
(* 
  尝试证明： todo
  三个策略流动性的关系 delta_all --> delta --> delta_empty --> BitMl
  基础流动性：与这三者的关联。
*)
  
(* 普通的策略流动性 *)
(* 在满足一定条件下，合约地址 caddr 所关联的智能合约会在若干步内被用户清算。 *)
(* 写出为什么分两段，并举出例子，指出他们的本质不同，
  并且对原本的基础流动性定义好结合，结合框架 *)
Definition delta_liquidate
            (delta_env delta_usr : strat)
            (caddr : Address)
            (contract : Contract Setup Msg State Error)
            : Prop :=
  forall s0 s (tr_s:trace(s)),
    wellStrat delta_env ->
    wellStrat delta_usr ->
    is_init_bstate contract s0  ->
    InteractionSuccessionEnv delta_env delta_usr s0 s -> 
    (funds s caddr > 0)%Z ->
    (exists s' n,
      UserLiquidatesInNSteps delta_env delta_usr caddr n s s').

  Definition NonStratLiquid_t (contract : Contract Setup Msg State Error) (caddr:Address) : Prop :=
    forall bstate (trace : ChainTrace empty_state bstate),
      activesc bstate caddr contract ->
      (funds bstate caddr > 0)%Z ->
      exists bstate',
        transition_through contract bstate bstate' /\
        (funds bstate' caddr = 0)%Z.

  
(* bitml表现得性质 *)
Definition delta_bitml_liquidate
            (delta_env delta_usr : strat)
            (caddr : Address)
            (contract : Contract Setup Msg State Error)
            : Prop :=
  forall s0 s (tr_s:trace(s)),
    wellStrat delta_env ->
    wellStrat delta_usr ->
    initial_contract_state s0 caddr contract ->
    InteractionSuccessionEnv delta_env delta_usr  s0 s -> 
    (funds s caddr > 0)%Z ->
    (exists n s',
      UserLiquidatesInNSteps delta_empty delta_usr caddr n s s').

(* 最强环境的策略流动性 *)
Definition delta_all_liquidate
            (delta_usr : strat)
            (caddr : Address)
            (contract : Contract Setup Msg State Error)
            : Prop :=
  forall s0 s (tr_s:trace(s)),
    wellStrat delta_usr ->
    initial_contract_state s0 caddr contract ->
    InteractionSuccessionEnv delta_all delta_usr s0 s -> 
    (funds s caddr > 0)%Z ->
    (exists n s',
      UserLiquidatesInNSteps delta_all delta_usr caddr n s s').

(* retrieves the previous and next state of a ChainStep *)
Definition chainstep_states {prev_bstate next_bstate}
                            (step : ChainStep prev_bstate next_bstate) :=
  (prev_bstate, next_bstate).


Definition isb_contract (bstate:ChainState)
                        (caddr:Address)
                        (contract : Contract Setup Msg State Error)
                        :bool :=
  match env_contracts bstate caddr with
  | Some contract => true
  | _ => false
  end.


Fixpoint deployment_state
           {from to : ChainState}
           (trace : ChainTrace from to)
           (caddr : Address)
           : option ChainState :=
  match trace with
  | snoc trace' step =>
    match step with
    | step_action _ _ _ _ _ _ (eval_deploy origin from to amount _ _ _ _ _ _ _ _ _ _ _) _ =>
        let '(prev_bstate, next_bstate) := chainstep_states step in
        if (to =? caddr)%address then
          Some next_bstate
        else
          deployment_state trace' caddr 
    | _ => deployment_state trace' caddr 
    end
  | clnil => None
  end.

(* 最强环境的策略流动性 *)
Definition delta_all_liquidate_1
            (delta_usr : strat)
            (caddr : Address)
            (contract : Contract Setup Msg State Error)
            : Prop :=
  forall s0 s (tr_s:trace(s)),
    wellStrat delta_usr ->
    initial_contract_state s0 caddr contract ->
    InteractionSuccessionEnv delta_all delta_usr s0 s -> 
    (funds s caddr > 0)%Z ->
    (exists n s',
      UserLiquidatesInNSteps delta_all delta_usr caddr n s s').

  Definition NonStratLiquid_1 (contract : Contract Setup Msg State Error) (caddr:Address) : Prop :=
    forall s0 bstate (trace : ChainTrace empty_state bstate),
      initial_contract_state s0 caddr contract ->
      reachable_through s0 bstate ->
      (funds bstate caddr > 0)%Z ->
      exists bstate',
        reachable_through bstate bstate' /\
        (funds bstate' caddr = 0)%Z.

  (* Lemma i_to_r :
    forall delta_usr s0 bstate,
      reachable_through s0 bstate ->
      InteractionSuccessionEnv delta_all delta_usr s0 bstate.
  Proof.
    intros.
    
  Qed. *)
  



Definition ChainTrace_Action := ChainedList ChainState ChainStep.

Definition reachable (state : ChainState) : Prop :=
  inhabited (ChainTrace empty_state state).

  Lemma delta_all_liquidate_implies_basic_liquidity:
    forall delta_usr caddr (contract : Contract Setup Msg State Error) ,
      wellStrat delta_usr ->
      delta_all_liquidate_1 delta_usr caddr contract ->
      NonStratLiquid_1 contract caddr.
  Proof.
    intros.
    unfold delta_all_liquidate_1 in H4.
    unfold NonStratLiquid_1.
    intros.
    specialize(H4 s0 bstate trace H3 H5).
    destruct H4;eauto.
    - eapply interactionSuccessionEnv_reachable_through in H4.
      assert()
    - 

    assert(reachable_through s0 bstate).
    {
      
    }
    
  Qed.



(* 环境为空的策略流动性 --> bitML *)
Definition delta_empty_liquidate
            (delta_usr : strat)
            (caddr : Address)
            (contract : Contract Setup Msg State Error)
            : Prop :=
  forall s0 s (tr_s:trace(s)),
    wellStrat delta_usr ->
    initial_contract_state s0 caddr contract ->
    InteractionSuccession delta_empty delta_usr s0 s -> 
    (funds s caddr > 0)%Z ->
    (exists n s',
      UserLiquidatesInNSteps delta_empty delta_usr caddr n s s').

