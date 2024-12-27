Require Import Purchase.
Require Import BuildUtils.
Require Import Automation.
From Coq Require Import ZArith.
Require Import Serializable.
Require Import Blockchain.
Require Import Containers.
Require Import Extras.
Require Import RecordUpdate.
From Coq Require Import Bool.
From Coq Require Import Lia.
From Coq Require Import List.
Import ListNotations.
From Coq Require Import Permutation.
Require Import ChainedList.
Require Import Strat.
Require Import FMapList.
Require Import ResultMonad.

Section Theories.

Context {BaseTypes : ChainBase}.
Set Primitive Projections.
Set Nonrecursive Elimination Schemes.
Context {AddrSize : N}.
Context {DepthFirst : bool}.

Arguments hash_bid : simpl never.
Arguments hash_purchaseId : simpl never.

Ltac destruct_message :=
  match goal with
  | receive_some : context[receive _ _ _ _ ?msg = Ok (_, _)] |- _ => destruct msg as [?m|]; try discriminate; destruct m
  | receive_some : context[Purchase.receive _ _ _ ?msg = Ok (_, _)] |- _ => destruct msg as [?m|]; try discriminate; destruct m
  end.

Ltac receive_simpl_step g :=
  match type of g with
  | context[find_purchase] => unfold find_purchase in g; cbn in g
  | context[find_item] => unfold find_item in g; cbn in g
  | context[purchase_exists] => unfold purchase_exists in g; cbn in g
  | context[FMap.find _ ?v] => destruct (FMap.find _ v) eqn:?; cbn in g
  | context[required_true ?cond] => destruct cond eqn:?E; inversion E; cbn in g
  | context[required_false ?cond] => destruct cond eqn:?E; inversion E; cbn in g
  | context[required_amount_zero _] => unfold required_amount_zero in g; cbn in g
  | context[required_no_self_call _] => unfold required_no_self_call in g; cbn in g
  end. 

Tactic Notation "receive_simpl" constr(g) := cbn in g; repeat (receive_simpl_step g); try discriminate.
Ltac receive_simpl_goal_step :=
  match goal with
  | |- context[find_purchase] => unfold find_purchase
  | |- context[find_item] => unfold find_item
  | |- context[purchase_exists] => unfold purchase_exists
  | |- context[purchase_state_eq] => unfold purchase_state_eq
  | |- context[required_amount_zero _] => unfold required_amount_zero
  | |- context[required_no_self_call _] => unfold required_no_self_call
  end. 

  Tactic Notation "receive_simpl_goal" := cbn; repeat (receive_simpl_goal_step; cbn).


  Ltac reduce_init :=
    match goal with
    | H : Purchase.init ?chain ?ctx ?setup = Ok ?res |- _ =>
        (* 1. 展开 init 的定义 *)
        unfold Purchase.init in H;
        (* 2. 检查 required_no_self_call ctx *)
        destruct (required_no_self_call ctx) eqn:ESelfCall in H; try discriminate;
        (* 3. 检查 0 <? setup_timeout setup *)
        destruct (0 <? setup_timeout setup)%nat eqn:ETimeout in H; try discriminate;
        (* 4. 检查 required_amount_zero ctx *)
        destruct (required_amount_zero ctx) eqn:EAmountZero in H; try discriminate;
        destruct (address_not_contract (setup_fair setup )) eqn:EFairEoa in H; try discriminate
    end.

Ltac reduce_buyer_abort_action :=
  match goal with
  | H : buyer_abort_action ?ctx ?state ?purchaseId = Ok (?ns, ?acts) |- _ =>
      (* 展开目标函数定义 *)
      unfold buyer_abort_action in H;
      (* 检查 required_amount_zero *)
      destruct (required_amount_zero ctx) eqn:EAmtZero in H; try discriminate;
      (* 查找购买记录 *)
      destruct (find_purchase purchaseId (purchases state)) as [purchase|] eqn:EFindPurchase in H; try discriminate;
      (* 检查购买状态是否为 requested *)
      destruct (purchase_state_eq (purchase_state purchase) requested) eqn:EStateEq in H; try discriminate;
      (* 检查调用者是否为买家 *)
      destruct ((ctx_from ctx) =? purchase.(buyer))%address eqn:EBuyerEq in H; try discriminate
  end.
Ltac reduce_buyer_request_purchase_action :=
  match goal with
  | H : buyer_request_purchase_action ?chain ?ctx ?state ?itemId ?notes = _ |- _ =>
      unfold buyer_request_purchase_action in H;
      (* 检查是否为自调用 *)
      destruct (required_no_self_call ctx) eqn:ESelfCall in H; try discriminate;
      destruct (find_item itemId (listings state)) eqn:EFindItem in H; try discriminate;
      destruct (item_value _ =? ctx_amount ctx)%Z eqn:EAmount in H; try discriminate;
      destruct (negb (purchase_exists (hash_purchaseId (current_slot chain) (ctx_from ctx)) (purchases state))) eqn:EPurchaseExists in H; try discriminate
      (* 查找商品 *)
  end.
Ltac reduce_buyer_open_commitment_action :=
  match goal with
  | H : buyer_open_commitment_action ?ctx ?state ?purchaseId ?buyer_bit ?nonce = Ok (?ns, ?acts) |- _ =>
      (* 展开目标函数定义 *)
      unfold buyer_open_commitment_action in H;
      (* 检查 required_amount_zero *)
      destruct (required_amount_zero ctx) eqn:EAmtZero in H; try discriminate;
      (* 查找购买记录 *)
      destruct (find_purchase purchaseId (purchases state)) as [purchase|] eqn:EFindPurchase in H; try discriminate;
      (* 查找商品记录 *)
      destruct (find_item (itemId purchase) (listings state)) as [item|] eqn:EFindItem in H; try discriminate;
      (* 检查调用者是否为买家 *)
      destruct ((ctx_from ctx) =? purchase.(buyer))%address eqn:EBuyerEq in H; try discriminate;
      (* 检查购买状态是否为 counter *)
      destruct (purchase_state_eq (purchase_state purchase) counter) eqn:EStateEq in H; try discriminate;
      (* 验证提交的哈希值是否匹配 *)
      destruct (hash_bid purchaseId buyer_bit nonce =? purchase.(commit))%N eqn:EHashMatch in H; try discriminate
  end.


  

Ltac reduce_buyer_confirm_delivery_action :=
    match goal with
    | H : buyer_confirm_delivery_action ?ctx ?state ?purchaseId = Ok (?ns, ?acts) |- _ =>
        (* 展开目标函数定义 *)
        unfold buyer_confirm_delivery_action in H;
        (* 检查 required_amount_zero ctx *)
        destruct (required_amount_zero ctx) eqn:EAmtZero in H; try discriminate;
        (* 查找购买记录 *)
        destruct (find_purchase purchaseId (purchases state)) as [p|] eqn:EFindPurchase in H; try discriminate;
        (* 检查购买状态是否为 delivered *)
        destruct (purchase_state_eq (purchase_state p) delivered) eqn:EStateEq in H; try discriminate;
        (* 检查调用者是否为买家 *)
        destruct ((ctx_from ctx) =? buyer p)%address eqn:EBuyerEq in H; try discriminate
    end.


Ltac reduce_buyer_dispute_delivery_action :=
  match goal with
  | H : buyer_dispute_delivery_action ?ctx ?state ?chain ?purchaseId ?commitment
         = Ok (?ns, ?acts) |- _ =>
      (* 1. 展开函数定义 *)
      unfold buyer_dispute_delivery_action in H;
      (* 2. 解构 find_purchase purchaseId (purchases state) *)
      destruct (find_purchase purchaseId (purchases state)) as [p|] eqn:EFindPurchase in H;
        try discriminate;
      (* 3. 解构 find_item p.(itemId) (listings state) *)
      destruct (find_item (itemId p) (listings state)) as [i|] eqn:EFindItem in H;
        try discriminate;
      (* 4. 检查 (ctx_amount ctx) =? i.(item_value) *)
      destruct ((ctx_amount ctx) =? (item_value i))%Z eqn:EAmount in H; try discriminate;
      (* 5. purchase_state_eq (purchase_state p) delivered *)
      destruct (purchase_state_eq (purchase_state p) delivered) eqn:EPurchState in H;
        try discriminate;
      (* 6. (ctx_from ctx) =? p.(buyer) *)
      destruct ((ctx_from ctx) =? (buyer p))%address eqn:EBuyerEq in H;
        try discriminate
  end.

Ltac reduce_buyer_call_timeout_action :=
  match goal with
  | H : buyer_call_timeout_action ?ctx ?state ?chain ?purchaseId = Ok (?ns, ?acts) |- _ =>
      (* 展开目标函数定义 *)
      unfold buyer_call_timeout_action in H;
      (* 检查 required_amount_zero ctx *)
      destruct (required_amount_zero ctx) eqn:EAmtZero in H; try discriminate;
      (* 查找购买记录 *)
      destruct (find_purchase purchaseId (purchases state)) as [p|] eqn:EFindPurchase in H; try discriminate;
      (* 检查购买状态是否为 dispute 或 accepted *)
      destruct (purchase_state_eq (purchase_state p) dispute || purchase_state_eq (purchase_state p) accepted)%bool eqn:EStateEq in H; try discriminate;
      (* 检查调用者是否为买家 *)
      destruct ((ctx_from ctx) =? buyer p)%address eqn:EBuyerEq in H; try discriminate;
      (* 检查是否超过超时 *)
      destruct (last_block p + timeout state <? current_slot chain)%nat eqn:ETimeoutCheck in H; try discriminate
  end.


  

Ltac reduce_seller_call_timeout_action :=
  match goal with
  | H : seller_call_timeout_action ?ctx ?state ?chain ?purchaseId = Ok (?ns, ?acts) |- _ =>
      (* 展开目标函数定义 *)
      unfold seller_call_timeout_action in H;
      (* 检查 required_amount_zero ctx *)
      destruct (required_amount_zero ctx) eqn:EAmtZero in H; try discriminate;
      (* 查找购买记录 *)
      destruct (find_purchase purchaseId (purchases state)) as [p|] eqn:EFindPurchase in H; try discriminate;
      (* 检查购买状态是否为 delivered 或 counter *)
      destruct (purchase_state_eq (purchase_state p) delivered 
                || purchase_state_eq (purchase_state p) counter)%bool eqn:EStateEq in H; try discriminate;
      (* 检查调用者是否为卖家 *)
      destruct ((ctx_from ctx) =? seller state)%address eqn:ESellerEq in H; try discriminate;
      (* 检查是否超过超时 *)
      destruct (last_block p + timeout state <? current_slot chain)%nat eqn:ETimeoutCheck in H; try discriminate
  end.

Ltac reduce_seller_reject_contract_action :=
  match goal with
  | H : seller_reject_contract_action ?ctx ?state ?purchaseId = Ok (?ns, ?acts) |- _ =>
      (* 展开目标函数定义 *)
      unfold seller_reject_contract_action in H;
      (* 检查 required_amount_zero ctx *)
      destruct (required_amount_zero ctx) eqn:EAmtZero in H; try discriminate;
      (* 查找购买记录 *)
      destruct (find_purchase purchaseId (purchases state)) as [p|] eqn:EFindPurchase in H; try discriminate;
      (* 检查购买状态是否为 requested *)
      destruct (purchase_state_eq (purchase_state p) requested) eqn:EStateEq in H; try discriminate;
      (* 检查调用者是否为卖家 *)
      destruct ((ctx_from ctx) =? seller state)%address eqn:ESellerEq in H; try discriminate
  end.

Ltac reduce_seller_accept_contract_action :=
  match goal with
  | H : seller_accept_contract_action ?ctx ?state ?chain ?purchaseId = Ok (?ns, ?acts) |- _ =>
      (* 展开目标函数定义 *)
      unfold seller_accept_contract_action in H;
      (* 检查 required_amount_zero ctx *)
      destruct (required_amount_zero ctx) eqn:EAmtZero in H; try discriminate;
      (* 查找购买记录 *)
      destruct (find_purchase purchaseId (purchases state)) as [p|] eqn:EFindPurchase in H; try discriminate;
      (* 检查购买状态是否为 requested *)
      destruct (purchase_state_eq (purchase_state p) requested) eqn:EStateEq in H; try discriminate;
      (* 检查调用者是否为卖家 *)
      destruct ((ctx_from ctx) =? seller state)%address eqn:ESellerEq in H; try discriminate
  end.

Ltac reduce_seller_item_was_delivered_action :=
  match goal with
  | H : seller_item_was_delivered_action ?ctx ?state ?chain ?purchaseId = Ok (?ns, ?acts) |- _ =>
      (* 展开目标函数定义 *)
      unfold seller_item_was_delivered_action in H;
      (* 检查 required_amount_zero ctx *)
      destruct (required_amount_zero ctx) eqn:EAmtZero in H; try discriminate;
      (* 查找购买记录 *)
      destruct (find_purchase purchaseId (purchases state)) as [p|] eqn:EFindPurchase in H; try discriminate;
      (* 检查购买状态是否为 accepted *)
      destruct (purchase_state_eq (purchase_state p) accepted) eqn:EStateEq in H; try discriminate;
      (* 检查调用者是否为卖家 *)
      destruct ((ctx_from ctx) =? seller state)%address eqn:ESellerEq in H; try discriminate
  end.

Ltac reduce_seller_forfeit_dispute_action :=
  match goal with
  | H : seller_forfeit_dispute_action ?ctx ?state ?purchaseId = Ok (?ns, ?acts) |- _ =>
      (* 展开目标函数定义 *)
      unfold seller_forfeit_dispute_action in H;
      (* 检查 required_amount_zero ctx *)
      destruct (required_amount_zero ctx) eqn:EAmtZero in H; try discriminate;
      (* 查找购买记录 *)
      destruct (find_purchase purchaseId (purchases state)) as [p|] eqn:EFindPurchase in H; try discriminate;
      (* 检查购买状态是否为 dispute *)
      destruct (purchase_state_eq (purchase_state p) dispute) eqn:EStateEq in H; try discriminate;
      (* 检查调用者是否为卖家 *)
      destruct ((ctx_from ctx) =? seller state)%address eqn:ESellerEq in H; try discriminate
  end.

Ltac reduce_seller_counter_dispute_action :=
  match goal with
  | H : seller_counter_dispute_action ?ctx ?state ?chain ?purchaseId ?random_bit = Ok (?ns, ?acts) |- _ =>
      (* 展开目标函数定义 *)
      unfold seller_counter_dispute_action in H;
      (* 查找购买记录 *)
      destruct (find_purchase purchaseId (purchases state)) as [p|] eqn:EFindPurchase in H; try discriminate;
      (* 检查购买状态是否为 dispute *)
      destruct (purchase_state_eq (purchase_state p) dispute) eqn:EStateEq in H; try discriminate;
      (* 检查调用者是否为卖家 *)
      destruct ((ctx_from ctx) =? seller state)%address eqn:ESellerEq in H; try discriminate;
      (* 查找商品记录 *)
      destruct (find_item (itemId p) (listings state)) as [i|] eqn:EFindItem in H; try discriminate;
      (* 检查发送金额是否匹配商品价值 *)
      destruct (ctx_amount ctx =? item_value i)%Z eqn:EAmountEq in H; try discriminate
  end.

Ltac reduce_seller_update_listings_action :=
  match goal with
  | H : seller_update_listings_action ?ctx ?state ?itemId ?descr ?value = Ok (?ns, ?acts) |- _ =>
      (* 展开目标函数定义 *)
      unfold seller_update_listings_action in H;
      (* 检查 required_amount_zero ctx *)
      destruct (required_amount_zero ctx) eqn:EAmtZero in H; try discriminate;
      (* 检查 value 是否非负 *)
      destruct (0 <=? value)%Z eqn:EValueNonNeg in H; try discriminate;
      (* 检查调用者是否为卖家 *)
      destruct ((ctx_from ctx) =? seller state)%address eqn:ESellerEq in H; try discriminate;
      (* 检查是否没有活跃购买记录 *)
      destruct (no_active_purchase_for_itemId state itemId) eqn:ENoActivePurchase in H; try discriminate
  end.

Ltac reduce_required_true :=
  match goal with
  | H : required_true ?b = Some ?u |- _ =>
      unfold required_true in H;
      destruct b eqn:EB in H; [ | discriminate H ]
      (* 如果需要注入 tt，可用 injection ；不过通常直接 clear 就够了 *)
  end.

  Ltac reduce_required_false :=
    match goal with
    | H : required_false ?b = Some ?u |- _ =>
        unfold required_false in H;
        destruct b eqn:EB in H; [ discriminate H | ]
    end.
    
Ltac reduce_required_amount_zero :=
  match goal with
  | H : required_amount_zero ?ctx = Some ?u |- _ =>
      unfold required_amount_zero in H;
      unfold required_true in H;
      destruct (ctx_amount ctx =? 0)%Z eqn:EAmt in H; [ | discriminate H ]
  end.

  
  
  (* Goal forall ctx u ,
  required_amount_zero ctx = Some u -> True.
  Proof.
  intros.
  reduce_required_amount_zero.
  Qed. *)

  Ltac reduce_required_no_self_call :=
    match goal with
    | H : required_no_self_call ?ctx = Some ?u |- _ =>
        unfold required_no_self_call in H;
        unfold required_false in H;
        destruct ((ctx_from ctx) =? (ctx_contract_address ctx))%address eqn:ESelf in H;
        [ discriminate H | ]
    end.



Ltac reduce_find_item :=
  match goal with
  | H : find_item ?itemId ?listings = Some ?it |- _ =>
      unfold find_item in H;
      destruct (FMap.find itemId listings) eqn:EFind in H;
      [ 
      | discriminate H
      ]
  end.

Ltac reduce_find_purchase :=
  match goal with
  | H : find_purchase ?purchaseId ?purchases = Some ?pur |- _ =>
      unfold find_purchase in H;
      destruct (FMap.find purchaseId purchases) eqn:EFind in H;
      [ 
      | discriminate H
      ]
  end.

Ltac reduce_no_active_purchase_for_itemId :=
  match goal with
  | H : no_active_purchase_for_itemId ?st ?id = true |- _ =>
      unfold no_active_purchase_for_itemId in H;
      simpl in H
  end.


Open Scope Z.

Lemma address_eqb_eq : forall (addr1 addr2 : Address),
  (addr1 =? addr2)%address = true <-> addr1 = addr2.
Proof.
  intros *. split; intros H; destruct (address_eqb_spec addr1 addr2); easy.
Qed.

Lemma purchase_state_eq_correct : forall (state1 state2 : PurchaseState),
  state1 = state2 <-> purchase_state_eq state1 state2 = true.
Proof.
  intros *. split; intros; destruct state1; destruct state2; try discriminate; reflexivity.
Qed.


Lemma buyer_request_purchase_correct : forall chain ctx prev_state new_state new_acts _itemId _notes,
  Purchase.receive chain ctx prev_state (Some (buyer_request_purchase _itemId _notes)) = Ok (new_state, new_acts)
  <->
     (exists item,
         FMap.find _itemId prev_state.(listings) = Some item
      /\ FMap.find _itemId new_state.(listings) = Some item
      /\ item.(item_value) = ctx.(ctx_amount))
  /\ (exists purchaseId new_purchase,
         purchaseId = hash_purchaseId chain.(current_slot) (ctx.(ctx_from))
      /\ FMap.find purchaseId prev_state.(purchases) = None
      /\ new_state.(purchases) = FMap.add purchaseId new_purchase prev_state.(purchases)
      /\ new_purchase.(itemId) = _itemId
      /\ new_purchase.(pool) = ctx.(ctx_amount)
      /\ new_purchase.(last_block) = chain.(current_slot)
      /\ new_purchase.(purchase_state) = requested
      /\ new_purchase.(buyer) = ctx.(ctx_from)
      /\ new_purchase.(seller_bit) = false
      /\ new_purchase.(commit) = 0%N
      /\ new_purchase.(notes) = _notes)
  /\ ctx.(ctx_from) <> ctx.(ctx_contract_address)
  /\ prev_state.(listings) = new_state.(listings)
  /\ prev_state.(seller) = new_state.(seller)
  /\ prev_state.(timeout) = new_state.(timeout)
  /\ prev_state.(fair) = new_state.(fair)
  /\ new_acts = []
  .
Proof.
  intros * . split.
  - intros receive_some.
    receive_simpl receive_some.
    remember ({|
      commit := 0;
      last_block := current_slot chain;
      itemId := _itemId;
      seller_bit := false;
      notes := _notes;
      purchase_state := requested;
      buyer := ctx_from ctx;
      pool := ctx_amount ctx|})
    as new_purchase.
    reduce_buyer_request_purchase_action.
    repeat split; try now inversion receive_some .
    + exists i. repeat split; try now inversion receive_some.
      propify.
      intuition.
    + remember (hash_purchaseId chain.(current_slot) ctx.(ctx_from)) as new_purchaseId.
      exists new_purchaseId, new_purchase.
      repeat split; try now inversion Heqnew_purchase;
      inversion receive_some;propify;intuition.
      unfold purchase_exists  in EPurchaseExists.
      destruct (find_purchase new_purchaseId (purchases prev_state)) eqn : H';try congruence;intuition.
    +
      reduce_required_no_self_call.
      destruct_address_eq; eauto.
  - intros ([item (prev_item & new_item & amount_sent)] &
            (purchaseId & new_purchase & purchaseId_hash & not_found_purchase & purchase_added & purchase_itemId & purchase_pool & purchase_last_block &
             ppurchase_state & purchase_buyer & purchase_seller_bit & purchase_commit & purchase_notes ) &
             not_caddr & const_listings & const_seller & const_timeout & const_fair & empty_acts).
    receive_simpl_goal.
    apply address_eq_ne in not_caddr.
    unfold buyer_request_purchase_action.
    unfold required_no_self_call.
    rewrite not_caddr; cbn.
    setoid_rewrite prev_item.
    apply Z.eqb_eq in amount_sent. rewrite amount_sent; cbn.
    rewrite <- purchaseId_hash.
    unfold purchase_exists.
    setoid_rewrite not_found_purchase; cbn.
    rewrite <- purchase_last_block, <- purchase_commit, <- purchase_itemId, <- purchase_pool, <- purchase_seller_bit,
            <- purchase_notes, <- ppurchase_state, <- purchase_buyer.   
    destruct new_purchase; destruct new_state; cbn in *.
    rewrite empty_acts.
    rewrite <- const_listings.
    rewrite <-const_seller.
    rewrite <- const_timeout.
    rewrite <- const_fair.
    now setoid_rewrite <- purchase_added. 
Qed.

Lemma seller_accept_contract_correct : forall chain ctx prev_state new_state new_acts id,
  Purchase.receive chain ctx prev_state (Some (seller_accept_contract id)) = Ok (new_state, new_acts)
  <->
     (exists purchase updated_purchase,
        FMap.find id prev_state.(purchases) = Some purchase
      /\ purchase.(purchase_state) = requested
      /\ FMap.find id new_state.(purchases) = Some updated_purchase
      /\ updated_purchase.(purchase_state) = accepted
      /\ updated_purchase.(last_block) = chain.(current_slot)
      /\ updated_purchase.(commit) = purchase.(commit)
      /\ updated_purchase.(itemId) = purchase.(itemId)
      /\ updated_purchase.(seller_bit) = purchase.(seller_bit)
      /\ updated_purchase.(notes) = purchase.(notes)
      /\ updated_purchase.(buyer) = purchase.(buyer)
      /\ updated_purchase.(pool) = purchase.(pool)
      /\ new_state.(purchases) = FMap.add id updated_purchase prev_state.(purchases))
  /\ ctx.(ctx_from) = prev_state.(seller)
  /\ ctx.(ctx_amount) = 0
  /\ prev_state.(listings) = new_state.(listings)
  /\ prev_state.(seller) = new_state.(seller)
  /\ prev_state.(timeout) = new_state.(timeout)
  /\ prev_state.(fair) = new_state.(fair)
  /\ new_acts = [].
Proof.
  intros *. split.
  - intros receive_some. cbn in *.
    receive_simpl receive_some.
    reduce_seller_accept_contract_action.
    (* set(p <| purchase_state := accepted |> <| last_block := current_slot chain |>) as updated_purchase'. *)
    remember ({|
      commit := commit p;
      last_block := current_slot chain;
      itemId := itemId p;
      seller_bit := seller_bit p;
      notes := notes p;
      purchase_state := accepted;
      buyer := buyer p;
      pool := pool p|})
    as updated_purchase.
    inversion receive_some; clear receive_some. cbn. repeat split.
    exists p, updated_purchase. repeat split; try now inversion Hequpdated_purchase.
    + now apply purchase_state_eq_correct in EStateEq.
    + rewrite Hequpdated_purchase.
      apply FMap.find_add.
    + now apply address_eqb_eq.
    + reduce_required_amount_zero.
      intuition.
  - intros ([purchase [updated_purchase (purchase_found & state_requested & updated_purchase_found &
                updated_state_accepted & block_current & commit_constant & item_constant &
                seller_bit_constant & notes_constant & buyer_constant & pool_constant &  purchase_added)]] &
             ctx_from_seller & amount_zero & listings_constant & seller_constant & timeout_constant & fair_constant & no_acts).
    receive_simpl_goal.
    unfold seller_accept_contract_action.
    unfold required_amount_zero.
    rewrite amount_zero; cbn.
    setoid_rewrite purchase_found.
    rewrite state_requested; cbn.
    apply address_eqb_eq in ctx_from_seller. rewrite ctx_from_seller; cbn.
    rewrite no_acts; cbn.
    destruct updated_purchase; destruct new_state;destruct prev_state; cbn in *.
    rewrite seller_constant, listings_constant, timeout_constant, fair_constant.
    rewrite purchase_added. 
    rewrite <- updated_state_accepted, <- block_current, <- commit_constant, <- item_constant,
            <- seller_bit_constant, <- notes_constant, <- buyer_constant, <- pool_constant.
            auto.
Qed.

Lemma buyer_dispute_delivery_correct : forall chain ctx prev_state new_state new_acts id commitment,
Purchase.receive chain ctx prev_state (Some (buyer_dispute_delivery id commitment)) = Ok (new_state, new_acts)
  <->
  (exists purchase updated_purchase item,
     FMap.find id prev_state.(purchases) = Some purchase
  /\ FMap.find purchase.(itemId) prev_state.(listings) = Some item
  /\ ctx.(ctx_from) = purchase.(buyer)
  /\ purchase.(purchase_state) = delivered
  /\ updated_purchase.(purchase_state) = dispute
  /\ updated_purchase.(pool) = purchase.(pool) + item.(item_value)
  /\ updated_purchase.(last_block) = chain.(current_slot)
  /\ new_state.(purchases) = FMap.add id updated_purchase prev_state.(purchases)
  /\ commitment = updated_purchase.(commit)
  (* These fields should stay constant *)
  /\ purchase.(itemId) = updated_purchase.(itemId)
  /\ purchase.(seller_bit) = updated_purchase.(seller_bit)
  /\ purchase.(notes) = updated_purchase.(notes)
  /\ purchase.(buyer) = updated_purchase.(buyer)
  /\ ctx.(ctx_amount) = item.(item_value))
  /\ prev_state.(listings) = new_state.(listings)
  /\ prev_state.(seller) = new_state.(seller)
  /\ prev_state.(timeout) = new_state.(timeout)
  /\ prev_state.(fair) = new_state.(fair)
  /\ new_acts = []
  .
Proof.
  intros *. split.
  - intros receive_some.
    receive_simpl receive_some.
    reduce_buyer_dispute_delivery_action.
    remember ({|
    commit := commitment;
    last_block := current_slot chain;
    itemId := itemId p;
    seller_bit := seller_bit p;
    notes := notes p;
    purchase_state := dispute;
    buyer := buyer p;
    pool := pool p + i.(item_value)|})
    as updated_purchase.
    repeat split; try now inversion receive_some.
    exists p, updated_purchase, i.
    repeat split; try now inversion Hequpdated_purchase.
    + now apply address_eqb_eq.
    + now apply purchase_state_eq_correct in EPurchState.
    + now inversion receive_some.
    + now apply Z.eqb_eq in EAmount.
  - intros ([purchase [updated_purchase [item
            (purchase_found & item_found & purchase_from & state_delivered & upd_state_dispute & upd_pool & block_current &
             upd_purchases & com & const_item & const_seller_bit & const_notes & const_buyer & amount_item_value)
            ]]] & (const_listings & const_seller & const_timeout &  const_fair & acts_empty)).
  receive_simpl_goal.
  unfold buyer_dispute_delivery_action.
  setoid_rewrite purchase_found.
  setoid_rewrite item_found.
  apply Z.eqb_eq in amount_item_value; rewrite amount_item_value; cbn.
  rewrite state_delivered; cbn.
  apply address_eqb_eq in purchase_from; rewrite purchase_from; cbn.
  rewrite acts_empty.
  destruct updated_purchase; destruct new_state;destruct prev_state; cbn in *.
  rewrite const_item, const_seller_bit, const_notes, const_buyer,
           const_listings, const_seller, const_timeout,const_fair,
          com, <- upd_state_dispute, <- block_current, <- upd_pool.
  now setoid_rewrite <- upd_purchases.
Qed.

Lemma buyer_open_commitment_correct : forall chain ctx prev_state new_state new_acts id buyer_bit nonce,
Purchase.receive chain ctx prev_state (Some (buyer_open_commitment id buyer_bit nonce)) = Ok (new_state, new_acts)
  <->
  (exists purchase updated_purchase item,
     FMap.find id prev_state.(purchases) = Some purchase
  /\ FMap.find purchase.(itemId) prev_state.(listings) = Some item
  /\ FMap.find id new_state.(purchases) = Some updated_purchase
  /\ new_state.(purchases) = FMap.add id updated_purchase prev_state.(purchases)
  /\ failed = updated_purchase.(purchase_state)
  /\ 0 = updated_purchase.(pool)
  /\ purchase.(last_block) = updated_purchase.(last_block)
  /\ purchase.(commit) = updated_purchase.(commit)
  /\ purchase.(itemId) = updated_purchase.(itemId)
  /\ purchase.(seller_bit) = updated_purchase.(seller_bit)
  /\ purchase.(notes) = updated_purchase.(notes)
  /\ purchase.(buyer) = updated_purchase.(buyer)
  /\ purchase.(purchase_state) = counter
  /\ hash_bid id buyer_bit nonce = purchase.(commit)
  /\ ctx.(ctx_from) = purchase.(buyer)
  /\ (eqb purchase.(seller_bit) buyer_bit = true
     -> new_acts = [act_transfer purchase.(buyer) (purchase.(pool) - item.(item_value)); act_transfer prev_state.(fair) item.(item_value)])
  /\ (eqb purchase.(seller_bit) buyer_bit = false
     -> new_acts = [act_transfer prev_state.(seller) (purchase.(pool) - item.(item_value));act_transfer prev_state.(fair) item.(item_value)])
  )
  /\ ctx.(ctx_amount) = 0
  /\ prev_state.(listings) = new_state.(listings)
  /\ prev_state.(seller) = new_state.(seller)
  /\ prev_state.(timeout) = new_state.(timeout)
  /\ prev_state.(fair) = new_state.(fair)
  .
  intros *. split.
  - intros receive_some.
    receive_simpl receive_some.
    reduce_buyer_open_commitment_action.
    rename purchase into p.
    remember ({|
    commit := commit p;
    last_block := last_block p;
    itemId := itemId p;
    seller_bit := seller_bit p;
    notes := notes p;
    purchase_state := failed;
    buyer := buyer p;
    pool := 0 |})
    as updated_purchase.
    repeat split; try now inversion Hequpdated_purchase; try now inversion receive_some.
    rename item into i.
    exists p, updated_purchase, i.
    repeat split; try now inversion Hequpdated_purchase.
    + inversion receive_some; cbn. apply FMap.find_add.
    + now inversion receive_some.
    + now apply purchase_state_eq_correct in EStateEq.
    + now apply N.eqb_eq in EHashMatch.
    + now apply address_eqb_eq.
    + intros eq_bits. inversion receive_some. rewrite eq_bits. eauto.
    + intros neq_bits. inversion receive_some. now rewrite neq_bits.
    + reduce_required_amount_zero. propify. eauto.
  - intros ([purchase [updated_purchase [item 
            (purchase_found & item_found & updated_purchase_found & purchases_updated & upd_purchase_failed & pool_zero &
             const_block & const_commit & const_itemId & const_seller_bit & const_notes & const_buyer &
             purchase_counter & correct_hash & ctx_from_buyer & eq_bits & neq_bits)]]] &
             (amount_zero & const_listings & const_seller & const_timeout & const_fair)).
    receive_simpl_goal.
    unfold buyer_open_commitment_action.
    unfold required_amount_zero.
    rewrite amount_zero; cbn.
    setoid_rewrite purchase_found.
    setoid_rewrite item_found.
    apply address_eqb_eq in ctx_from_buyer.
    rewrite ctx_from_buyer; cbn. 
    rewrite purchase_counter; cbn.
    apply N.eqb_eq in correct_hash; rewrite correct_hash; cbn.
    destruct updated_purchase; destruct new_state;destruct prev_state; cbn in *.

    rewrite const_seller, const_listings, const_timeout,const_fair.
    rewrite const_commit, const_block,
            const_seller_bit,const_notes, const_itemId, const_buyer.
    rewrite upd_purchase_failed.
    rewrite pool_zero.
    setoid_rewrite <- purchases_updated.  
    rewrite const_seller_bit in eq_bits, neq_bits.
    destruct (eqb seller_bit buyer_bit) eqn:E.
    + rewrite eq_bits. rewrite const_buyer. rewrite const_fair. eauto.  easy.
    + rewrite neq_bits. rewrite const_seller. rewrite const_fair. eauto. eauto.
Qed.

Lemma seller_item_was_delivered_correct : forall chain ctx prev_state new_state new_acts id,
  Purchase.receive chain ctx prev_state (Some (seller_item_was_delivered id)) = Ok (new_state, new_acts)
  <->
  (exists purchase updated_purchase,
      FMap.find id prev_state.(purchases) = Some purchase
   /\ FMap.find id new_state.(purchases) = Some updated_purchase
   /\ new_state.(purchases) = FMap.add id updated_purchase prev_state.(purchases)
   /\ purchase.(purchase_state) = accepted
   /\ updated_purchase.(purchase_state) = delivered
   /\ updated_purchase.(last_block) = chain.(current_slot)
   (* These should remain constant *)
   /\ purchase.(commit) = updated_purchase.(commit)
   /\ purchase.(itemId) = updated_purchase.(itemId)
   /\ purchase.(seller_bit) = updated_purchase.(seller_bit)
   /\ purchase.(notes) = updated_purchase.(notes)
   /\ purchase.(buyer) = updated_purchase.(buyer)
   /\ purchase.(pool) = updated_purchase.(pool))
  /\ ctx.(ctx_amount) = 0
  /\ prev_state.(listings) = new_state.(listings)
  /\ prev_state.(seller) = new_state.(seller)
  /\ prev_state.(timeout) = new_state.(timeout)
  /\ prev_state.(fair) = new_state.(fair)
  /\ ctx.(ctx_from) = prev_state.(seller)
  /\ new_acts = []
  .
Proof.
  intros *. split.
  - intros receive_some.
    receive_simpl receive_some.
    reduce_seller_item_was_delivered_action. 
    repeat split; try now inversion receive_some.
    remember ({|
    commit := commit p;
    last_block := current_slot chain;
    itemId := itemId p;
    seller_bit := seller_bit p;
    notes := notes p;
    purchase_state := delivered;
    buyer := buyer p;
    pool := pool p |})
    as updated_purchase.
    exists p, updated_purchase.
    repeat split; try now inversion Hequpdated_purchase; try now inversion receive_some.
    + inversion receive_some; cbn. apply FMap.find_add.
    + now inversion receive_some.
    + now apply purchase_state_eq_correct in EStateEq.
    + reduce_required_amount_zero .
      propify. eauto.
    + now apply address_eqb_eq.
  - intros ([purchase [updated_purchase
            (found_purchase & found_upd_purchase & purchases_updated & purchase_accepted & upd_purchase_delivered & upd_purchase_block &
             const_commit & const_item & const_seller_bit & const_notes & const_buyer & const_pool)]] &
            amount_zero & const_listings & const_seller & const_timeout & const_fair & from_seller & empty_acts).
    receive_simpl_goal.
    unfold seller_item_was_delivered_action.
    unfold required_amount_zero.
    rewrite amount_zero; cbn.
    setoid_rewrite found_purchase.
    rewrite purchase_accepted; cbn.
    apply address_eqb_eq in from_seller; rewrite from_seller; cbn. 
    destruct updated_purchase; destruct new_state;destruct prev_state; cbn in *.
    rewrite const_seller, const_listings, const_timeout , const_fair.
    rewrite const_commit, const_item, const_notes, const_seller_bit, const_buyer, const_pool.
    rewrite <- upd_purchase_delivered, <- upd_purchase_block, empty_acts.
    now setoid_rewrite purchases_updated.
Qed.

Lemma seller_counter_dispute_correct : forall chain ctx prev_state new_state new_acts id random_bit,
  Purchase.receive chain ctx prev_state (Some (seller_counter_dispute id random_bit)) = Ok (new_state, new_acts)
  <->
  (exists purchase updated_purchase item,
      FMap.find id prev_state.(purchases) = Some purchase
   /\ FMap.find id new_state.(purchases) = Some updated_purchase
   /\ FMap.find purchase.(itemId) prev_state.(listings) = Some item
   /\ new_state.(purchases) = FMap.add id updated_purchase prev_state.(purchases)
   /\ purchase.(purchase_state) = dispute
   /\ updated_purchase.(seller_bit) = random_bit
   /\ updated_purchase.(purchase_state) = counter
   /\ updated_purchase.(last_block) = chain.(current_slot)
   /\ ctx.(ctx_amount) = item.(item_value)
   /\ purchase.(pool) + item.(item_value) = updated_purchase.(pool)
   (* These should remain constant *)
   /\ purchase.(commit) = updated_purchase.(commit)
   /\ purchase.(itemId) = updated_purchase.(itemId)
   /\ purchase.(notes) = updated_purchase.(notes)
   /\ purchase.(buyer) = updated_purchase.(buyer))
  /\ prev_state.(listings) = new_state.(listings)
  /\ prev_state.(seller) = new_state.(seller)
  /\ prev_state.(timeout) = new_state.(timeout)
  /\ prev_state.(fair) = new_state.(fair)
  /\ ctx.(ctx_from) = prev_state.(seller)
  /\ new_acts = []
.
Proof.
  intros *. split.
  - intros receive_some.
    receive_simpl receive_some.
    reduce_seller_counter_dispute_action.
    repeat split; try now inversion receive_some.
    remember ({|
    commit := commit p;
    last_block := current_slot chain;
    itemId := itemId p;
    seller_bit := random_bit;
    notes := notes p;
    purchase_state := counter;
    buyer := buyer p;
    pool := pool p + ctx_amount ctx |})
    as updated_purchase.
    exists p, updated_purchase, i.
    repeat split; try now inversion Hequpdated_purchase.
    + inversion receive_some; cbn.
      rewrite Hequpdated_purchase.
      apply FMap.find_add.
    + now inversion receive_some.
    + now apply purchase_state_eq_correct in EStateEq.
    + now apply Z.eqb_eq in EAmountEq.
    + inversion Hequpdated_purchase; cbn. apply Z.eqb_eq in EAmountEq.
      lia.
    + now apply address_eqb_eq.
  - intros ([purchase [updated_purchase [item (
             found_purchase & found_upd_purchase & found_item & updated_purchases & purchase_dispute &
             seller_bit_rand & upd_purchase_counter & upd_purchase_block & amount_as_item & upd_pool &
             const_commit & const_item & const_notes & const_buyer
            )]]] &
            const_listings & const_seller & const_timeout & const_fair &
             from_seller & empty_acts).
    receive_simpl_goal.
    unfold seller_counter_dispute_action .
    setoid_rewrite found_purchase.
    rewrite purchase_dispute; cbn.
    apply address_eqb_eq in from_seller; rewrite from_seller; cbn.
    rewrite empty_acts.
    setoid_rewrite found_item.
    (* pose proof (Z.eqb_eq _ _ amount_as_item). *)
    (* pose proof not working for some reason, therefore applying twice. *)
    apply Z.eqb_eq in amount_as_item; rewrite amount_as_item; cbn.
    apply Z.eqb_eq in amount_as_item; rewrite amount_as_item; cbn.
    destruct updated_purchase; destruct new_state;destruct prev_state; cbn in *.
    rewrite const_seller, const_listings, const_timeout,const_fair .
    rewrite const_commit, <- upd_purchase_block, <- seller_bit_rand, <- upd_purchase_counter,
            const_item, const_notes, const_buyer, upd_pool.
    now setoid_rewrite <- updated_purchases. 
Qed.

Lemma buyer_abort_correct : forall chain ctx prev_state new_state new_acts purchaseId,
  Purchase.receive chain ctx prev_state (Some (buyer_abort purchaseId)) = Ok (new_state, new_acts)
  <->
     (exists purchase updated_purchase,
        FMap.find purchaseId prev_state.(purchases) = Some purchase
     /\ FMap.find purchaseId new_state.(purchases) = Some updated_purchase
     /\ ctx.(ctx_from) = purchase.(buyer)
     /\ new_acts = [act_transfer purchase.(buyer) purchase.(pool)]
     /\ purchase.(purchase_state) = requested
     /\ updated_purchase.(purchase_state) = failed
     /\ updated_purchase.(pool) = 0
     /\ updated_purchase.(commit) = purchase.(commit)
     /\ updated_purchase.(last_block) = purchase.(last_block)
     /\ updated_purchase.(itemId) = purchase.(itemId)
     /\ updated_purchase.(seller_bit) = purchase.(seller_bit)
     /\ updated_purchase.(notes) = purchase.(notes)
     /\ updated_purchase.(buyer) = purchase.(buyer)
     /\ new_state.(purchases) = FMap.add purchaseId updated_purchase prev_state.(purchases)
     )
  /\ ctx.(ctx_amount) = 0
  /\ prev_state.(listings) = new_state.(listings)
  /\ prev_state.(seller) = new_state.(seller)
  /\ prev_state.(timeout) = new_state.(timeout)
  /\ prev_state.(fair) = new_state.(fair)
  .
Proof.
  intros *. split.
  - intros receive_some.
    receive_simpl receive_some.
    reduce_buyer_abort_action.
    rename purchase into p.
    repeat split; try now inversion receive_some.
    remember ({|
    commit := commit p;
    last_block := last_block p;
    itemId := itemId p;
    seller_bit := seller_bit p;
    notes := notes p;
    purchase_state := failed;
    buyer := buyer p;
    pool := 0 |})
    as updated_purchase.
    exists p, updated_purchase.
    repeat split; try now inversion Hequpdated_purchase.
    + inversion receive_some; cbn. apply FMap.find_add.
    + now apply address_eqb_eq. 
    + inversion receive_some; cbn. eauto.
    + now apply purchase_state_eq_correct in EStateEq.
    + now inversion receive_some.
    + reduce_required_amount_zero.
      propify. eauto.
  - intros ([purchase [updated_purchase
            (found_purchase & upd_found_purchase & from_buyer & acts_transfer & purchase_req & upd_purchase_fail & upd_pool_zero &
             const_commit & const_block & const_itemId & const_seller_bit & const_notes & const_buyer  & updated_purchases)
            ]] & (amount_zero & const_listings & const_seller & const_timeout & const_fair)).
    receive_simpl_goal.
    unfold buyer_abort_action.
    unfold required_amount_zero.
    rewrite amount_zero; cbn.
    setoid_rewrite found_purchase.
    rewrite purchase_req; cbn.
    apply address_eqb_eq in from_buyer; rewrite from_buyer; cbn.
    rewrite acts_transfer.
    rewrite <- upd_purchase_fail, <- upd_pool_zero.
    destruct updated_purchase; destruct new_state;destruct prev_state; cbn in *.
    rewrite const_seller, const_listings, const_timeout, const_fair.
    rewrite <- const_commit, <- const_block, <- const_itemId, <- const_seller_bit,
            <- const_notes, <- const_buyer.
    now setoid_rewrite <- updated_purchases.
Qed.

Lemma buyer_confirm_delivery_correct : forall chain ctx prev_state new_state new_acts purchaseId,
  Purchase.receive chain ctx prev_state (Some (buyer_confirm_delivery purchaseId)) = Ok (new_state, new_acts)
  <->
     (exists purchase updated_purchase,
        FMap.find purchaseId prev_state.(purchases) = Some purchase
     /\ FMap.find purchaseId new_state.(purchases) = Some updated_purchase
     /\ ctx.(ctx_from) = purchase.(buyer)
     /\ new_acts = [act_transfer prev_state.(seller) purchase.(pool)]
     /\ purchase.(purchase_state) = delivered
     /\ updated_purchase.(purchase_state) = completed
     /\ updated_purchase.(pool) = 0
     /\ updated_purchase.(commit) = purchase.(commit)
     /\ updated_purchase.(last_block) = purchase.(last_block)
     /\ updated_purchase.(itemId) = purchase.(itemId)
     /\ updated_purchase.(seller_bit) = purchase.(seller_bit)
     /\ updated_purchase.(notes) = purchase.(notes)
     /\ updated_purchase.(buyer) = purchase.(buyer)
     /\ new_state.(purchases) = FMap.add purchaseId updated_purchase prev_state.(purchases)
     )
  /\ ctx.(ctx_amount) = 0
  /\ prev_state.(listings) = new_state.(listings)
  /\ prev_state.(seller) = new_state.(seller)
  /\ prev_state.(timeout) = new_state.(timeout)
  /\ prev_state.(fair) = new_state.(fair)
  .
Proof.
  intros *. split.
  - intros receive_some.
    receive_simpl receive_some.
    reduce_buyer_confirm_delivery_action.
    repeat split; try now inversion receive_some.
    remember ({|
    commit := commit p;
    last_block := last_block p;
    itemId := itemId p;
    seller_bit := seller_bit p;
    notes := notes p;
    purchase_state := completed;
    buyer := buyer p;
    pool := 0 |})
    as updated_purchase.
    exists p, updated_purchase.
    repeat split; try now inversion Hequpdated_purchase.
    + inversion receive_some; cbn. apply FMap.find_add.
    + now apply address_eqb_eq.
    + now inversion receive_some.
    + now apply purchase_state_eq_correct in EStateEq.
    + now inversion receive_some.
    + reduce_required_amount_zero.
      propify. eauto.
  - intros ([purchase [updated_purchase
            (found_purchase & upd_found_purchase & from_buyer & acts_transfer & purchase_delivered & upd_purchase_completed & upd_pool_zero &
             const_commit & const_block & const_itemId & const_seller_bit & const_notes & const_buyer & updated_purchases)
            ]] & (amount_zero & const_listings & const_seller & const_timeout & const_fair)).
    receive_simpl_goal.
    unfold buyer_confirm_delivery_action.
    unfold required_amount_zero .
    rewrite amount_zero; cbn.
    setoid_rewrite found_purchase.
    rewrite purchase_delivered; cbn.
    apply address_eqb_eq in from_buyer; rewrite from_buyer; cbn.
    rewrite acts_transfer.
    destruct updated_purchase; destruct new_state;destruct prev_state; cbn in *.
    rewrite <- upd_purchase_completed, <- upd_pool_zero.
    rewrite const_seller, const_listings, const_timeout, const_fair.
    rewrite <- const_commit, <- const_block, <- const_itemId, <- const_seller_bit,
            <- const_notes, <- const_buyer.
    now setoid_rewrite <- updated_purchases.
Qed.


Lemma buyer_call_timeout_correct : forall chain ctx prev_state new_state new_acts purchaseId,
  Purchase.receive chain ctx prev_state (Some (buyer_call_timeout purchaseId)) = Ok (new_state, new_acts)
  <->
     (exists purchase updated_purchase,
        FMap.find purchaseId prev_state.(purchases) = Some purchase
     /\ FMap.find purchaseId new_state.(purchases) = Some updated_purchase
     /\ ctx.(ctx_from) = purchase.(buyer)
     /\ new_acts = [act_transfer purchase.(buyer) purchase.(pool)]

     /\ (purchase.(purchase_state) = dispute \/ purchase.(purchase_state) = accepted)
     /\ (purchase.(last_block) + prev_state.(timeout) < chain.(current_slot))%nat
     /\ updated_purchase.(pool) = 0
     /\ updated_purchase.(purchase_state) = failed
     /\ updated_purchase.(commit) = purchase.(commit)
     /\ updated_purchase.(last_block) = purchase.(last_block)
     /\ updated_purchase.(itemId) = purchase.(itemId)
     /\ updated_purchase.(seller_bit) = purchase.(seller_bit)
     /\ updated_purchase.(notes) = purchase.(notes)
     /\ updated_purchase.(buyer) = purchase.(buyer)
     /\ new_state.(purchases) = FMap.add purchaseId updated_purchase prev_state.(purchases)
     )
  /\ ctx.(ctx_amount) = 0
  /\ prev_state.(listings) = new_state.(listings)
  /\ prev_state.(seller) = new_state.(seller)
  /\ prev_state.(timeout) = new_state.(timeout)
  /\ prev_state.(fair) = new_state.(fair)
  .
Proof.
  intros *. split.
  - intros receive_some.
    receive_simpl receive_some.
    reduce_buyer_call_timeout_action.
    repeat split; try now inversion receive_some.
    
    remember ({|
    commit := commit p;
    last_block := last_block p;
    itemId := itemId p;
    seller_bit := seller_bit p;
    notes := notes p;
    purchase_state := failed;
    buyer := buyer p;
    pool := 0 |})
    as updated_purchase.
    exists p, updated_purchase.
    repeat split; try now inversion Hequpdated_purchase.
    + inversion receive_some; cbn. apply FMap.find_add.
    + now apply address_eqb_eq.
    + now inversion receive_some.
    + apply orb_true_iff in EStateEq. destruct EStateEq as [purchase_st | purchase_st].
      apply purchase_state_eq_correct in purchase_st. eauto.
      apply purchase_state_eq_correct in purchase_st. eauto.
    + now apply Nat.ltb_lt in ETimeoutCheck.
    + now inversion receive_some.
    + reduce_required_amount_zero.
      propify. eauto.
  - intros ([purchase [updated_purchase
            (found_purchase & upd_found_purchase & from_buyer & acts_transfer & purchase_states & slot_gt_timeout & upd_pool_zero & upd_purchase_fail &
             const_commit & const_block & const_itemId & const_seller_bit & const_notes & const_buyer  & updated_purchases)
            ]] & (amount_zero & const_listings & const_seller & const_timeout & const_fair)).
    receive_simpl_goal.
    unfold buyer_call_timeout_action.
    unfold required_amount_zero.
    rewrite amount_zero; cbn.
    setoid_rewrite found_purchase.
    apply address_eqb_eq in from_buyer; rewrite from_buyer; cbn.
    assert(H_purchase_state_eq :  purchase_state_eq (purchase_state purchase) dispute
    || purchase_state_eq (purchase_state purchase) accepted = true).
    {
      propify.
      destruct purchase_states.
      rewrite H.
      eauto.
      rewrite H.
      eauto.
    }
    rewrite H_purchase_state_eq.
    destruct (current_slot chain)%nat eqn : Htime.
    lia.
    assert ((last_block purchase + timeout prev_state <=? n)%nat = true).
    {
      propify.
      lia.
    }
    rewrite H.
    destruct updated_purchase; destruct new_state;destruct prev_state; cbn in *.
    destruct purchase_states as [p_state | p_state];
    rewrite acts_transfer;
    rewrite <- upd_purchase_fail, <- upd_pool_zero;
    rewrite const_seller, const_listings, const_timeout, const_fair;
    rewrite <- const_commit, <- const_block, <- const_itemId, <- const_seller_bit,
            <- const_notes, <- const_buyer;
    now setoid_rewrite <- updated_purchases.
Qed.


Lemma seller_call_timeout_correct : forall chain ctx prev_state new_state new_acts purchaseId,
  Purchase.receive chain ctx prev_state (Some (seller_call_timeout purchaseId)) = Ok (new_state, new_acts)
  <->
     (exists purchase updated_purchase,
        FMap.find purchaseId prev_state.(purchases) = Some purchase
     /\ FMap.find purchaseId new_state.(purchases) = Some updated_purchase
     /\ new_acts = [act_transfer prev_state.(seller) purchase.(pool)]

     /\ (purchase.(purchase_state) = delivered \/ purchase.(purchase_state) = counter)
     /\ (purchase.(last_block) + prev_state.(timeout) < chain.(current_slot))%nat
     /\ updated_purchase.(purchase_state) = completed
     /\ updated_purchase.(pool) = 0
     /\ updated_purchase.(commit) = purchase.(commit)
     /\ updated_purchase.(last_block) = purchase.(last_block)
     /\ updated_purchase.(itemId) = purchase.(itemId)
     /\ updated_purchase.(seller_bit) = purchase.(seller_bit)
     /\ updated_purchase.(notes) = purchase.(notes)
     /\ updated_purchase.(buyer) = purchase.(buyer)
     /\ new_state.(purchases) = FMap.add purchaseId updated_purchase prev_state.(purchases)
     )
  
  /\ ctx.(ctx_from) = prev_state.(seller)
  /\ ctx.(ctx_amount) = 0
  /\ prev_state.(listings) = new_state.(listings)
  /\ prev_state.(seller) = new_state.(seller)
  /\ prev_state.(timeout) = new_state.(timeout)
  /\ prev_state.(fair) = new_state.(fair)
  .
Proof.
  intros *. split.
  - intros receive_some.
    receive_simpl receive_some.
    reduce_seller_call_timeout_action.
    repeat split; try now inversion receive_some.
    remember ({|
    commit := commit p;
    last_block := last_block p;
    itemId := itemId p;
    seller_bit := seller_bit p;
    notes := notes p;
    purchase_state := completed;
    buyer := buyer p;
    pool := 0 |})
    as updated_purchase.
    exists p, updated_purchase.
    repeat split; try now inversion Hequpdated_purchase.
    + inversion receive_some; cbn. apply FMap.find_add.
    + now inversion receive_some.
    + apply orb_true_iff in EStateEq. destruct EStateEq as [purchase_st | purchase_st];
      apply purchase_state_eq_correct in purchase_st;eauto. 
    + now apply Nat.ltb_lt in ETimeoutCheck.
    + now inversion receive_some.
    + now apply address_eqb_eq.
    + reduce_required_amount_zero.
      propify. eauto.
  - intros ([purchase [updated_purchase
            (found_purchase & upd_found_purchase & acts_transfer & purchase_states & slot_gt_timeout & upd_purchase_completed & upd_pool_zero &
             const_commit & const_block & const_itemId & const_seller_bit & const_notes & const_buyer & updated_purchases)
            ]] & (from_buyer & amount_zero & const_listings & const_seller & const_timeout & const_fair)).
    receive_simpl_goal.
    unfold seller_call_timeout_action.
    unfold required_amount_zero .
    rewrite amount_zero; cbn.
    setoid_rewrite found_purchase.
    apply address_eqb_eq in from_buyer; rewrite from_buyer; cbn.
    assert (H : purchase_state_eq (purchase_state purchase) delivered
    || purchase_state_eq (purchase_state purchase) counter  = true).
    {
      propify.
      destruct purchase_states;
      rewrite H;
      eauto.
    }
    rewrite H.
    destruct (current_slot chain)%nat eqn : Htime.
    lia.
    assert ((last_block purchase + timeout prev_state <=? n)%nat = true).
    {
      propify.
      lia.
    }
    rewrite H0.
    destruct updated_purchase; destruct new_state;destruct prev_state; cbn in *.
    rewrite acts_transfer;
    rewrite <- upd_purchase_completed, <- upd_pool_zero;
    rewrite const_seller, const_listings, const_timeout, const_fair;
    rewrite <- const_commit, <- const_block, <- const_itemId, <- const_seller_bit,
            <- const_notes, <- const_buyer;
    now setoid_rewrite <- updated_purchases.
Qed.

Lemma seller_reject_contract_correct : forall chain ctx prev_state new_state new_acts purchaseId,
  Purchase.receive chain ctx prev_state (Some (seller_reject_contract purchaseId)) = Ok (new_state, new_acts)
  <->
     (exists purchase updated_purchase,
        FMap.find purchaseId prev_state.(purchases) = Some purchase
     /\ FMap.find purchaseId new_state.(purchases) = Some updated_purchase
     /\ new_acts = [act_transfer purchase.(buyer) purchase.(pool)]

     /\ purchase.(purchase_state) = requested
     /\ updated_purchase.(purchase_state) = rejected
     /\ updated_purchase.(pool) = 0
     /\ updated_purchase.(commit) = purchase.(commit)
     /\ updated_purchase.(last_block) = purchase.(last_block)
     /\ updated_purchase.(itemId) = purchase.(itemId)
     /\ updated_purchase.(seller_bit) = purchase.(seller_bit)
     /\ updated_purchase.(notes) = purchase.(notes)
     /\ updated_purchase.(buyer) = purchase.(buyer)

     /\ new_state.(purchases) = FMap.add purchaseId updated_purchase prev_state.(purchases)
     )
     
  /\ ctx.(ctx_from) = prev_state.(seller)
  /\ ctx.(ctx_amount) = 0
  /\ prev_state.(listings) = new_state.(listings)
  /\ prev_state.(seller) = new_state.(seller)
  /\ prev_state.(timeout) = new_state.(timeout)
  /\ prev_state.(fair) = new_state.(fair)
  .
Proof.
  intros *. split.
  - intros receive_some.
    receive_simpl receive_some.
    reduce_seller_reject_contract_action.
    repeat split; try now inversion receive_some.
    remember ({|
    commit := commit p;
    last_block := last_block p;
    itemId := itemId p;
    seller_bit := seller_bit p;
    notes := notes p;
    purchase_state := rejected;
    buyer := buyer p;
    pool := 0 |})
    as updated_purchase.
    exists p, updated_purchase.
    repeat split; try now inversion Hequpdated_purchase.
    + inversion receive_some; cbn. apply FMap.find_add.
    + now inversion receive_some.
    + now apply purchase_state_eq_correct in EStateEq.
    + now inversion receive_some.
    + now apply address_eqb_eq.
    + reduce_required_amount_zero.
      propify. eauto.
  - intros ([purchase [updated_purchase
            (found_purchase & upd_found_purchase & acts_transfer & purchase_requested & upd_purchase_rejected & upd_pool_zero &
             const_commit & const_block & const_itemId & const_seller_bit & const_notes & const_buyer  & updated_purchases)
            ]] & (from_buyer & amount_zero & const_listings & const_seller & const_timeout & const_fair)).
    receive_simpl_goal.
    unfold seller_reject_contract_action.
    unfold required_amount_zero.

    rewrite amount_zero; cbn.
    setoid_rewrite found_purchase.
    rewrite purchase_requested; cbn.
    apply address_eqb_eq in from_buyer; rewrite from_buyer; cbn.
    rewrite acts_transfer.
    rewrite <- upd_purchase_rejected, <- upd_pool_zero.
    destruct updated_purchase; destruct new_state;destruct prev_state; cbn in *.
    rewrite const_seller, const_listings, const_timeout, const_fair.
    rewrite <- const_commit, <- const_block, <- const_itemId, <- const_seller_bit,
            <- const_notes, <- const_buyer.
    now setoid_rewrite <- updated_purchases.
Qed.

Lemma seller_forfeit_dispute_correct : forall chain ctx prev_state new_state new_acts purchaseId,
  Purchase.receive chain ctx prev_state (Some (seller_forfeit_dispute purchaseId)) = Ok (new_state, new_acts)
  <->
     (exists purchase updated_purchase,
        FMap.find purchaseId prev_state.(purchases) = Some purchase
     /\ FMap.find purchaseId new_state.(purchases) = Some updated_purchase
     /\ new_acts = [act_transfer purchase.(buyer) purchase.(pool)]

     /\ purchase.(purchase_state) = dispute
     /\ updated_purchase.(purchase_state) = failed
     /\ updated_purchase.(pool) = 0
     /\ updated_purchase.(commit) = purchase.(commit)
     /\ updated_purchase.(last_block) = purchase.(last_block)
     /\ updated_purchase.(itemId) = purchase.(itemId)
     /\ updated_purchase.(seller_bit) = purchase.(seller_bit)
     /\ updated_purchase.(notes) = purchase.(notes)
     /\ updated_purchase.(buyer) = purchase.(buyer)

     /\ new_state.(purchases) = FMap.add purchaseId updated_purchase prev_state.(purchases)
     )
     
  /\ ctx.(ctx_from) = prev_state.(seller)
  /\ ctx.(ctx_amount) = 0
  /\ prev_state.(listings) = new_state.(listings)
  /\ prev_state.(seller) = new_state.(seller)
  /\ prev_state.(timeout) = new_state.(timeout)
  /\ prev_state.(fair) = new_state.(fair)
  .
Proof.
  intros *. split.
  - intros receive_some.
    receive_simpl receive_some.
    reduce_seller_forfeit_dispute_action.
    repeat split; try now inversion receive_some.
    remember ({|
    commit := commit p;
    last_block := last_block p;
    itemId := itemId p;
    seller_bit := seller_bit p;
    notes := notes p;
    purchase_state := failed;
    buyer := buyer p;
    pool := 0 |})
    as updated_purchase.
    exists p, updated_purchase.
    repeat split; try now inversion Hequpdated_purchase.
    + inversion receive_some; cbn. apply FMap.find_add.
    + now inversion receive_some.
    + now apply purchase_state_eq_correct in EStateEq.
    + now inversion receive_some.
    + now apply address_eqb_eq.
    + reduce_required_amount_zero.
      propify. eauto.
  - intros ([purchase [updated_purchase
            (found_purchase & upd_found_purchase & acts_transfer & purchase_dispute & upd_purchase_failed & upd_pool_zero &
             const_commit & const_block & const_itemId & const_seller_bit & const_notes & const_buyer & updated_purchases)
            ]] & (from_buyer & amount_zero & const_listings & const_seller & const_timeout & const_fair)).
    receive_simpl_goal.
    unfold seller_forfeit_dispute_action .
    unfold required_amount_zero.
    
    rewrite amount_zero; cbn.
    setoid_rewrite found_purchase.
    rewrite purchase_dispute; cbn.
    apply address_eqb_eq in from_buyer; rewrite from_buyer; cbn.
    rewrite acts_transfer.
    rewrite <- upd_purchase_failed, <- upd_pool_zero.
    destruct updated_purchase; destruct new_state;destruct prev_state; cbn in *.
    rewrite const_seller, const_listings, const_timeout , const_fair.
    rewrite <- const_commit, <- const_block, <- const_itemId, <- const_seller_bit,
            <- const_notes, <- const_buyer.
    now setoid_rewrite <- updated_purchases.
Qed.

Lemma cons_to_app : forall {A} (a : A) (l : list A),
  a::l = [a] ++ l.
Proof. easy. Qed.


(* Proving correct for aux. function used in [seller_update_listings] *)
Lemma no_active_purchase_for_itemId_correct : forall state _itemId,
  no_active_purchase_for_itemId state _itemId = true
  <->
  Forall (fun '(_, purchase) => 
               purchase.(itemId) <> _itemId
            \/ purchase.(purchase_state) = completed
            \/ purchase.(purchase_state) = rejected
            \/ purchase.(purchase_state) = failed)
       (FMap.elements state.(purchases)).
Proof.
  intros *. split.
  - intros * no_active_purchase.
    unfold no_active_purchase_for_itemId in *.
    induction (FMap.elements state.(purchases)) as [| [key' purchase'] purchases']; auto.
    rewrite cons_to_app in no_active_purchase.
    rewrite filter_app in no_active_purchase; cbn in *.
    apply Forall_cons; only 2 : apply IHpurchases';
    destruct ((purchase'.(itemId) =? _itemId)%nat) eqn:is_itemId;
    destruct (purchase_state_eq purchase'.(purchase_state) completed) eqn:state_completed;
    destruct (purchase_state_eq purchase'.(purchase_state) rejected) eqn:state_rejected;
    destruct (purchase_state_eq purchase'.(purchase_state) failed) eqn:state_failed;
    try (apply purchase_state_eq_correct in state_completed);
    try (apply purchase_state_eq_correct in state_rejected);
    try (apply purchase_state_eq_correct in state_failed); auto;
    try (apply andb_true_iff in no_active_purchase; destruct no_active_purchase as [_ H2]; assumption).
    * apply andb_true_iff in no_active_purchase.
    destruct no_active_purchase as [H1 _].
    destruct purchase'.(purchase_state); discriminate.
    * left. now apply Nat.eqb_neq.
  - intros forall_purchases.
    unfold no_active_purchase_for_itemId.
    induction (FMap.elements state.(purchases)) as [| [key' purchase'] purchases']; auto.
    rewrite cons_to_app in forall_purchases.
    apply Forall_app in forall_purchases.
    destruct ((purchase'.(itemId) =? _itemId)%nat) eqn:is_itemId;
    cbn in *; rewrite is_itemId.
    + rewrite cons_to_app. 
      rewrite forallb_app. cbn in *. apply andb_true_iff. split.
      * apply andb_true_iff. split; auto.
        destruct forall_purchases as [H _].
        apply Forall_inv in H. destruct H as [neq_itemId | [p_state | [p_state | p_state]]];
        try now rewrite p_state.
        apply Nat.eqb_eq in is_itemId. lia.
      * now apply IHpurchases'.
    + now apply IHpurchases'.
Qed.
    
(* If item exists for _itemId, then all purchases belonging to that item should be of status [completed], [rejected] or [failed] *)
Lemma seller_update_listings_correct : forall chain ctx prev_state new_state new_acts _itemId upd_description upd_value,
  Purchase.receive chain ctx prev_state (Some (seller_update_listings _itemId upd_description upd_value)) = Ok (new_state, new_acts)
  <->
  Forall (fun '(_, purchase) => 
               purchase.(itemId) <> _itemId
            \/ purchase.(purchase_state) = completed
            \/ purchase.(purchase_state) = rejected
            \/ purchase.(purchase_state) = failed)
       (FMap.elements prev_state.(purchases))
  /\ (ctx.(ctx_from) =? prev_state.(seller))%address = true
  /\ FMap.add _itemId {| item_value := upd_value; item_description := upd_description |} prev_state.(listings) = new_state.(listings)
  /\ 0 <= upd_value
  /\ new_state.(purchases) = prev_state.(purchases)
  /\ new_state.(seller) = prev_state.(seller)
  /\ new_state.(timeout) = prev_state.(timeout)
  /\ prev_state.(fair) = new_state.(fair)
  /\ ctx.(ctx_amount) = 0
  /\ new_acts = []
  .
Proof.
  intros *. split.
  - intros receive_some.
    receive_simpl receive_some.
    reduce_seller_update_listings_action.
    repeat split; try now inversion receive_some.
    + now apply no_active_purchase_for_itemId_correct.
    + now apply Z.leb_le in EValueNonNeg.
    + reduce_required_amount_zero.
      propify. eauto.
  - intros (forall_purchases & from_seller & item_add & value_gt_zero &
            const_purchases & const_seller & const_timeout & const_fair & amount_zero & empty_acts).
    receive_simpl_goal.
    unfold seller_update_listings_action.
    unfold required_amount_zero.
    rewrite amount_zero; cbn.
    apply Z.leb_le in value_gt_zero; rewrite value_gt_zero; cbn.
    rewrite from_seller; cbn.
    apply no_active_purchase_for_itemId_correct in forall_purchases.
    rewrite forall_purchases; cbn.
    destruct new_state;destruct prev_state; cbn in *.
    rewrite item_add, <- const_seller, <- const_purchases, <- const_timeout, <-const_fair, empty_acts.
    eauto.
Qed.



(* init correct *)
Lemma init_correct : forall state chain ctx setup,
  Purchase.init chain ctx setup = Ok (state) ->
       (0 < setup.(setup_timeout))%nat
    /\ ctx.(ctx_amount) = 0
    /\ state.(timeout) = (chain.(current_slot) + setup.(setup_timeout))%nat
    /\ state.(listings) = setup.(setup_listings)
    /\ state.(seller) = ctx.(ctx_from)
    /\ state.(purchases) = FMap.empty
    /\ state.(fair) = setup.(setup_fair)
    /\ ctx.(ctx_from) <> ctx.(ctx_contract_address)
    /\ address_not_contract (state.(fair)) = true.
Proof.
  intros * init_some.
  receive_simpl init_some. inversion init_some; cbn.
  reduce_init.
  propify.
  split.
  eauto.
  split.
  reduce_required_amount_zero.
  propify.
  eauto.
  inversion H0.
  repeat split; auto.
  eauto.
  reduce_required_no_self_call.
  destruct_address_eq; auto.
Qed.

Ltac apply_message_lemma H :=
  match type of H with
  | _ _ _ _ (Some (buyer_request_purchase _ _)) = Ok (_, _) =>
      apply buyer_request_purchase_correct in H
  | _ _ _ _ (Some (buyer_abort _)) = Ok (_, _) =>
      apply buyer_abort_correct in H
  | _ _ _ _ (Some (buyer_confirm_delivery _)) = Ok (_, _) =>
      apply buyer_confirm_delivery_correct in H
  | _ _ _ _ (Some (buyer_dispute_delivery _ _)) = Ok (_, _) =>
      apply buyer_dispute_delivery_correct in H
  | _ _ _ _ (Some (buyer_call_timeout _)) = Ok (_, _) =>
      apply buyer_call_timeout_correct in H
  | _ _ _ _ (Some (buyer_open_commitment _ _ _)) = Ok (_, _) =>
      apply buyer_open_commitment_correct in H
  | _ _ _ _ (Some (seller_call_timeout _)) = Ok (_, _) =>
      apply seller_call_timeout_correct in H
  | _ _ _ _ (Some (seller_reject_contract _)) = Ok (_, _) =>
      apply seller_reject_contract_correct in H
  | _ _ _ _ (Some (seller_accept_contract _)) = Ok (_, _) =>
      apply seller_accept_contract_correct in H
  | _ _ _ _ (Some (seller_item_was_delivered _)) = Ok (_, _) =>
      apply seller_item_was_delivered_correct in H
  | _ _ _ _ (Some (seller_forfeit_dispute _)) = Ok (_, _) =>
      apply seller_forfeit_dispute_correct in H
  | _ _ _ _ (Some (seller_counter_dispute _ _)) = Ok (_, _) =>
      apply seller_counter_dispute_correct in H
  | _ _ _ _ (Some (seller_update_listings _ _ _)) = Ok (_, _) =>
      apply seller_update_listings_correct in H
  end.

  Lemma seller_timeout_constant_on_receive : forall chain ctx msg prev_state new_state new_acts,
  Purchase.receive chain ctx prev_state msg = Ok (new_state, new_acts) ->
       prev_state.(seller) = new_state.(seller)
    /\ prev_state.(timeout) = new_state.(timeout).
Proof.
  intros * receive_some.
  destruct_message; now apply_message_lemma receive_some.
Qed.

Lemma sum_pool_add : forall (purchases : purchases_type) (id : N) (purchase1 purchase2 : Purchase),
  FMap.find id purchases = Some purchase1 ->
  sumZ (fun '(_, purchase) => purchase.(pool)) (FMap.elements (FMap.add id purchase2 purchases))=
  sumZ (fun '(_, purchase) => purchase.(pool) ) (FMap.elements purchases) - (purchase1.(pool)) + (purchase2.(pool)).
Proof.
  intros * p_found.
  assert (perm1 : Permutation (FMap.elements (FMap.add id purchase2 purchases)) ((id, purchase2)::(FMap.elements (FMap.remove id purchases))) ).
  { eapply FMap.elements_add_existing. eauto. }
  rewrite (sumZ_permutation perm1); cbn.
  assert (perm2 : Permutation (FMap.elements (FMap.add id purchase1 purchases)) ((id, purchase1)::(FMap.elements (FMap.remove id purchases))) ).
  { eapply FMap.elements_add_existing. eauto. }
  rewrite <- (FMap.add_id id purchase1 purchases p_found).
  setoid_rewrite (sumZ_permutation perm2); cbn.
  (* undo a rewrite *)
  rewrite (FMap.add_id id purchase1 purchases p_found).
  lia.
Qed.

Lemma seller_not_contract_addr bstate caddr:
  reachable bstate ->
  env_contracts bstate caddr = Some (Purchase.contract : WeakContract) ->
  exists cstate,
       contract_state bstate caddr = Some cstate
    /\ cstate.(seller) <> caddr.
Proof.
  contract_induction; intros; auto.
  - apply init_correct in init_some; auto. destruct_hyps. intuition.
  - destruct_message; apply_message_lemma receive_some; destruct_hyps; auto; congruence.
  - destruct_message; apply_message_lemma receive_some; destruct_hyps; auto; congruence.
  - solve_facts.
Qed. 

Lemma fair_not_contract_addr bstate caddr:
  reachable bstate ->
  env_contracts bstate caddr = Some (Purchase.contract : WeakContract) ->
  exists cstate,
       contract_state bstate caddr = Some cstate
    /\ address_not_contract cstate.(fair) = true
    /\ cstate.(fair) <> caddr.
Proof.
  contract_induction; intros; auto.
  - instantiate (DeployFacts := fun _ ctx => 
        address_is_contract  (ctx_contract_address ctx) = true).
    apply init_correct in init_some; auto. destruct_hyps. split. eauto.
    eapply address_not_contract_negb in H7.
    unfold not.
    intros.
    cbn in *.
    propify.
    unfold DeployFacts in *.
    rewrite <- H8 in *.
    intuition.
  - split; destruct_message; apply_message_lemma receive_some; destruct_hyps; auto; try congruence.
  - split;destruct_message; apply_message_lemma receive_some; destruct_hyps; auto; congruence.
  - solve_facts.
Qed. 


Lemma buyer_not_caddr_update : forall ctx id purchase1 purchase2 (purchases : purchases_type),
  purchase1.(buyer) <> ctx.(ctx_contract_address) ->
  purchase1.(buyer) = purchase2.(buyer) ->
  FMap.find id purchases = Some purchase1 ->
  Forall (fun '(_, p) => p.(buyer) <> ctx.(ctx_contract_address)) (FMap.elements purchases) ->
  Forall (fun '(_, p) => p.(buyer) <> ctx.(ctx_contract_address)) (FMap.elements (FMap.add id purchase2 purchases)).
Proof.
  intros * buyer_neq_caddr buyer_eq purchase_found forall_purchases.
  assert (perm1: Permutation (FMap.elements (FMap.add id purchase2 purchases)) ((id, purchase2)::(FMap.elements (FMap.remove id purchases))) ).
  { eapply FMap.elements_add_existing. eauto. }
  rewrite perm1. apply Forall_cons; auto.
  - now rewrite <- buyer_eq. 
  - now apply FMap.Forall_elements_f_remove.
Qed.

Lemma buyers_not_contract_addr bstate caddr:
  reachable bstate ->
  env_contracts bstate caddr = Some (contract : WeakContract) ->
  exists cstate,
       contract_state bstate caddr = Some cstate
    /\ Forall (fun '(_, p) => p.(buyer) <> caddr) (FMap.elements cstate.(purchases)).
Proof.
  contract_induction; intros; auto.
  - apply init_correct in init_some; auto. destruct_hyps.
    rewrite H4. setoid_rewrite FMap.elements_empty. easy.
  - destruct_message; apply_message_lemma receive_some; destruct_hyps; auto;
    try(
        match goal with
        | [H : new_state.(purchases) = _ |- _] => rewrite H
        end
    ); cbn;
    try (eapply (buyer_not_caddr_update _ _ x x0); auto; now apply (FMap.Forall_elements_f _ _ id x) in IH); auto.
    (* request_purchase *)
    assert (perm : Permutation (FMap.elements (FMap.add x x0 (purchases prev_state))) ((x, x0)::(FMap.elements prev_state.(purchases)))). { now apply FMap.elements_add. }
    setoid_rewrite perm. apply Forall_cons; auto.
    now rewrite H13.
    (* almost identical to non-recursive calls *)
  - 
    destruct_message; apply_message_lemma receive_some; destruct_hyps; auto;
    try(
        match goal with
        | [H : new_state.(purchases) = _ |- _] => rewrite H
        end
    ); cbn;
    try (eapply (buyer_not_caddr_update _ _ x x0); auto; now apply (FMap.Forall_elements_f _ _ id x) in IH); auto.
    (* request_purchase *)
    assert (perm : Permutation (FMap.elements (FMap.add x x0 (purchases prev_state))) ((x, x0)::(FMap.elements prev_state.(purchases)))). { now apply FMap.elements_add. }
    setoid_rewrite perm. apply Forall_cons; auto.
  - solve_facts.
Qed.

Lemma no_self_calls bstate caddr :
  reachable bstate ->
  env_contracts bstate caddr = Some (Purchase.contract : WeakContract) ->
  Forall (fun act_body =>
    match act_body with
    | act_transfer to _ => (to =? caddr)%address = false
    | _ => False
    end) (outgoing_acts bstate caddr).
Proof.
  contract_induction; intros; auto.
  - now inversion IH.
  - instantiate (CallFacts := fun _ ctx state _ _ =>
      state.(seller) <> ctx_contract_address ctx /\ 
      Forall (fun '(_, p) => p.(buyer) <> ctx_contract_address ctx) (FMap.elements state.(purchases)) /\ 
      ctx_contract_address ctx <> state.(fair)).
    unfold CallFacts in facts.
    destruct facts as [f1 [f2 f3]].
    apply address_eq_ne in from_other.
    apply address_eq_ne in f1.
    apply Forall_app; split; auto.
    destruct_message; apply_message_lemma receive_some; destruct_hyps; auto;
    try(
      match goal with
      | [H : new_acts = _ |- _] => rewrite H
      end
    ); auto.
    + constructor; auto. now rewrite <- H6.
    + constructor; auto. now rewrite <- H6.
    + destruct (eqb (x.(seller_bit)) buyer_bit).
      * rewrite H19; auto. constructor; auto. now rewrite <- H18.
        apply Forall_forall;eauto.
        intros.
        destruct x2 eqn : Hx;try congruence.
        unfold In in H21.
        destruct H21;try congruence.
        assert (to = (fair prev_state)).
        {
          destruct_address_eq;eauto;try congruence.
        }
        rewrite H22.
        unfold not in f3.
        destruct_address_eq;eauto;try congruence.
        inversion H21.
        unfold In in H21.
        destruct H21;try congruence.
        unfold In in H21.
        destruct H21;try congruence.
      * rewrite H20; auto.
      apply Forall_forall;eauto.
      intros.
      destruct x2 eqn : Hx;try congruence.
      unfold In in H21.
      destruct H21;try congruence.
      destruct H21;try congruence.
      assert (to = (fair prev_state)).
      {
        destruct_address_eq;eauto;try congruence.
      }
      rewrite H22.
      unfold not in f3.
      destruct_address_eq;eauto;try congruence.
      inversion H21.
      unfold In in H21.
      destruct H21;try congruence.
      unfold In in H21.
      destruct H21;try congruence.
      unfold In in H21.
      destruct H21;try congruence.
      unfold In in H21.
      destruct H21;try congruence.
    + constructor; auto. apply (FMap.Forall_elements_f _ _ id x) in f2; auto; cbn in *.
      now apply address_eq_ne in f2.
    + constructor; auto. apply (FMap.Forall_elements_f _ _ id x) in f2; auto; cbn in *.
      now apply address_eq_ne in f2.
  - inversion_clear IH as [|? ? head_not_me tail_not_me].
    apply Forall_app. split; auto.
    destruct head; try contradiction.
    destruct action_facts as [? [? ?]].
    destruct_address_eq; congruence.
  - now rewrite <- perm.
  - instantiate (DeployFacts := fun _ _ => True).
    instantiate (AddBlockFacts := fun _ _ _ _ _ _ => True).
    unset_all; subst.
    destruct_chain_step; auto.
    destruct_action_eval; auto.
    intros * contract_dep ?. cbn. split.
    + apply seller_not_contract_addr in contract_dep.
      * destruct_hyps;eauto.
        intuition.
      * constructor;eauto.
    + pose proof contract_dep as contract_dep0.
     apply buyers_not_contract_addr in contract_dep.
      * destruct_hyps;eauto.
        intuition.
        eapply fair_not_contract_addr in contract_dep0.
        destruct_hyps;eauto.
        intuition.
        econstructor;eauto.
      * constructor;eauto.
Qed.

Lemma no_self_calls' : forall bstate origin from_addr to_addr amount msg acts,
  reachable bstate ->
  env_contracts bstate to_addr = Some (contract : WeakContract) ->
  chain_state_queue bstate = {|
    act_origin := origin;
    act_from := from_addr;
    act_body :=
      match msg with
      | Some msg => act_call to_addr amount msg
      | None => act_transfer to_addr amount
      end
  |} :: acts ->
  from_addr <> to_addr.
Proof.
  intros * reach deployed queue.
  apply no_self_calls in deployed as no_self_calls; auto.
  unfold outgoing_acts in no_self_calls.
  rewrite queue in no_self_calls.
  cbn in no_self_calls.
  destruct_address_eq; auto.
  inversion_clear no_self_calls as [|? ? hd _].
  destruct msg.
  * congruence.
  * now rewrite address_eq_refl in hd.
Qed.

Definition not_from_contract ctx := ctx_from ctx <> ctx_contract_address ctx.
Ltac no_self_calls_solve := now instantiate (CallFacts := fun _ ctx _ _ _ => ctx_from ctx <> ctx_contract_address ctx).
Ltac destruct_apply_msg receive_some := destruct_message; apply_message_lemma receive_some; destruct_hyps; auto.

Ltac request_purchase_permutation id purchase state :=
  assert (req_perm : Permutation (FMap.elements (FMap.add id purchase state.(purchases))) ((id, purchase)::(FMap.elements state.(purchases)))); try now apply FMap.elements_add.

Ltac rewrite_param to_rewrite :=
  match goal with
  | [H : to_rewrite = _ |- _] => rewrite H
  | [H : _ = to_rewrite |- _] => rewrite <- H
  end.

(* Definition purchases_discarded_zero_not_failed cstate :=
  Forall (fun '(_, purchase) => purchase.(purchase_state) <> failed -> purchase.(discarded_money) = 0) (FMap.elements cstate.(purchases)).
  
Lemma purchase_discarded_zero_when_not_failed : forall bstate contract_addr,
  reachable bstate ->
  env_contracts bstate contract_addr = Some (Purchase.contract : WeakContract) ->
  exists cstate,
       contract_state bstate contract_addr = Some cstate
    /\ purchases_discarded_zero_not_failed cstate.
Proof.
  unfold purchases_discarded_zero_not_failed. contract_induction; intros; auto.
  - apply init_correct in init_some; auto; destruct_hyps. rewrite H4. now setoid_rewrite FMap.elements_empty.
  - destruct_apply_msg receive_some; 
    tryif (rewrite_param new_state.(purchases);
         specialize (FMap.Forall_elements_f _ _ id x H IH) as prev_disc_zero;
         cbn in prev_disc_zero;
         apply FMap.Forall_elements_add; auto;
         intros
    ) then (try (rewrite_param x0.(discarded_money); now apply prev_disc_zero)) else idtac;try intuition.
    + rewrite_param new_state.(purchases).
      request_purchase_permutation x x0 prev_state.
      rewrite req_perm.
      eauto.
  - no_self_calls_solve.
  - instantiate (DeployFacts := fun _ _ => True).
    instantiate (AddBlockFacts := fun _ _ _ _ _ _ => True).
    unset_all; subst.
    destruct_chain_step; auto.
    destruct_action_eval; auto.
    intros * contr_deployed ?. cbn.
    subst.
    eapply no_self_calls'; eauto.
    now constructor.
Qed. *)


Lemma contract_balance_eq_pool_sum : forall bstate contract_addr,
  reachable bstate ->
  env_contracts bstate contract_addr = Some (contract : WeakContract) ->
  exists cstate,
     contract_state bstate contract_addr = Some cstate
  /\ sumZ (fun '(_, purchase) => purchase.(pool)) (FMap.elements cstate.(purchases)) = env_account_balances bstate contract_addr - (sumZ (fun act => act_body_amount act) (outgoing_acts bstate contract_addr)). 
Proof.
  contract_induction; intros; auto; only 1-4 : cbn in *.
  - apply init_correct in init_some; auto. destruct_hyps. now rewrite H4, H0.
  - rewrite IH. lia.
  - instantiate (CallFacts := fun _ ctx cstate _ _ => not_from_contract ctx).
    unfold CallFacts, not_from_contract in *.
    rename facts into not_from_contract.
    destruct_message; apply_message_lemma receive_some; destruct_hyps; auto;
    try(rewrite_param new_state.(purchases)); 
    try(rewrite_param new_acts); cbn;
    try (rewrite (sum_pool_add prev_state.(purchases) id x x0) by auto;
    subst; cbn; rewrite IH; lia).
    + request_purchase_permutation x x0 prev_state.
      rewrite (sumZ_permutation req_perm); cbn.
      setoid_rewrite IH.
      intuition.
    + cbn in *.
      destruct (eqb (x.(seller_bit)) (buyer_bit));
      rewrite (sum_pool_add prev_state.(purchases) id x x0) by auto;
      try(rewrite H19 by auto); try(rewrite H20 by auto).
      * rewrite IH.
        rewrite_param ctx.(ctx_amount).
        rewrite_param x0.(pool).
        simpl.
        lia.
      * rewrite IH.
        rewrite_param ctx.(ctx_amount).
        rewrite_param x0.(pool).
        simpl.
        lia.
    + rewrite IH.
      rewrite_param ctx.(ctx_amount).
      intuition.
  - now unfold CallFacts in *.
  - now rewrite <- perm.
  - instantiate (DeployFacts := fun _ _ => True).
    instantiate (AddBlockFacts := fun _ _ _ _ _ _ => True).
    unset_all; subst.
    destruct_chain_step; auto.
    destruct_action_eval; auto.
    intros * contr_deployed ?. cbn; subst.
    + unfold not_from_contract; cbn.
      eapply no_self_calls'; eauto.  constructor;eauto.
Qed.


Lemma contract_balance_eq_pool_sum' : forall bstate contract_addr,
  reachable bstate ->
  outgoing_acts bstate contract_addr = [] ->
  env_contracts bstate contract_addr = Some (contract : WeakContract) ->
  exists cstate,
     contract_state bstate contract_addr = Some cstate
  /\ sumZ (fun '(_, purchase) => purchase.(pool)) (FMap.elements cstate.(purchases)) = env_account_balances bstate contract_addr. 
Proof.
  intros.
  specialize contract_balance_eq_pool_sum as (cstate & balance); eauto.
  destruct_and_split.
  exists cstate.
  split.
  eauto.
  rewrite H0 in H3.
  simpl in *.
  lia.
Qed.

Lemma contract_balance_eq_pool_sum_forall :
  forall bstate contract_addr cstate,
    reachable bstate ->
    env_contracts bstate contract_addr = Some (contract : WeakContract) ->
    outgoing_acts bstate contract_addr = [] ->
    contract_state bstate contract_addr = Some cstate ->
    sumZ (fun '(_, purchase) => purchase.(pool)) (FMap.elements cstate.(purchases)) = env_account_balances bstate contract_addr. 
Proof.
  intros.
  eapply contract_balance_eq_pool_sum' in H;eauto.
  destruct H;
  destruct_and_split.
  rewrite H2 in H.
  inversion H; subst;
  eauto.
Qed.

Definition purchase_is_finished purchase :=
  match purchase.(purchase_state) with
  | completed | failed | rejected => True
  | _ => False
  end.

  Lemma no_active_purchase_for_itemId_pool_zero : forall state _itemId,
  no_active_purchase_for_itemId state _itemId = true
  ->
  Forall (fun '(_, purchase) => 
               purchase.(itemId) <> _itemId
            \/ purchase.(purchase_state) = completed
            \/ purchase.(purchase_state) = rejected
            \/ purchase.(purchase_state) = failed)
       (FMap.elements state.(purchases)).


  Lemma contract_balance_is_zero_if_all_purchases_finished purchase :
  forall bstate contract_addr,
    reachable bstate ->
    env_contracts bstate contract_addr = Some (contract : WeakContract) ->
    exists cstate,
      contract_state bstate contract_addr = Some cstate /\
      ((Forall (fun '(_, purchase) => purchase_is_finished purchase) (FMap.elements cstate.(purchases))) ->
      (Forall (fun '(_, purchase) => purchase.(pool) = 0) (FMap.elements cstate.(purchases)))).
  Proof.
    contract_induction; intros; auto; only 1-4 : cbn in *.
    - apply init_correct in init_some; auto; destruct_hyps.
      rewrite H5 in *.
      setoid_rewrite FMap.elements_empty.
      eauto.
    - destruct_message; apply_message_lemma receive_some; destruct_hyps; auto;
      try(
          match goal with
          | [H : new_state.(purchases) = _ |- _] => rewrite H in *
          end
      ); cbn.
      +
      assert (perm : Permutation (FMap.elements (FMap.add x x0 (purchases prev_state))) ((x, x0)::(FMap.elements prev_state.(purchases)))). 
      { now apply FMap.elements_add. }
      setoid_rewrite perm. apply Forall_cons; auto.
      rewrite perm in H.
      assert (  Forall (fun '(_, purchase) => purchase_is_finished purchase)
          ((x, x0) :: FMap.elements (purchases prev_state)) ->
          purchase_is_finished x0 /\ 
          Forall (fun '(_, purchase) => purchase_is_finished purchase)
          (FMap.elements (purchases prev_state))).
      {
          intros.
          inversion H20 as [| (k, p) H21 H22]. eauto.
      }
      eapply H20 in H.
      destruct_and_split.
      unfold purchase_is_finished in H.
      rewrite H13 in H.
      inversion H.
      rewrite perm in H.
      assert (  Forall (fun '(_, purchase) => purchase_is_finished purchase)
          ((x, x0) :: FMap.elements (purchases prev_state)) ->
          purchase_is_finished x0 /\ 
          Forall (fun '(_, purchase) => purchase_is_finished purchase)
          (FMap.elements (purchases prev_state))).
      {
          intros.
          inversion H20 as [| (k, p) H21 H22]. eauto.
      }
      eapply H20 in H.
      destruct_and_split.
      eapply IH in H21.
      eauto.
      + 
      
      assert (perm1 : Permutation (FMap.elements (FMap.add id x0 (purchases prev_state))) ((id, x0)::(FMap.elements (FMap.remove id (purchases prev_state)))) ).
      { eapply FMap.elements_add_existing. eauto. }
      rewrite  perm1 in *; cbn in *.

      assert (   Forall (fun '(_, purchase) => purchase_is_finished purchase)
            ((id, x0)
       :: FMap.elements (FMap.remove id (purchases prev_state))) ->
          purchase_is_finished x0 /\ 
          Forall (fun '(_, purchase) => purchase_is_finished purchase)(FMap.elements (FMap.remove id (purchases prev_state)))).
      {
          intros.
          inversion H19 as [| (k, p) H21 H22]. eauto.
      }
      eapply H19 in H.
      destruct_and_split.
      unfold purchase_is_finished in H.
      rewrite H10 in H.
      inversion H.
      assert (perm1 : Permutation (FMap.elements (FMap.add id x0 x)) ((id, x0)::(FMap.elements (FMap.remove id x))) ).
      { now eapply FMap.elements_add_existing. }
      setoid_rewrite perm. apply Forall_cons; auto.
      rewrite perm in H.
      assert (  Forall (fun '(_, purchase) => purchase_is_finished purchase)
          ((x, x0) :: FMap.elements (purchases prev_state)) ->
          purchase_is_finished x0 /\ 
          Forall (fun '(_, purchase) => purchase_is_finished purchase)
          (FMap.elements (purchases prev_state))).
      {
          intros.
          inversion H20 as [| (k, p) H21 H22]. eauto.
      }
      eapply H20 in H.
      destruct_and_split.
      unfold purchase_is_finished in H.
      rewrite H13 in H.
      inversion H.
      rewrite perm in H.
      assert (  Forall (fun '(_, purchase) => purchase_is_finished purchase)
          ((x, x0) :: FMap.elements (purchases prev_state)) ->
          purchase_is_finished x0 /\ 
          Forall (fun '(_, purchase) => purchase_is_finished purchase)
          (FMap.elements (purchases prev_state))).
      {
          intros.
          inversion H20 as [| (k, p) H21 H22]. eauto.
      }
      eapply H20 in H.
      destruct_and_split.
      eapply IH in H21.
      eauto.
      ++ 
      eapply Forall_forall in H.

        destruct (FMap.find k (purchases prev_state)) eqn:H_find.

  Qed.

Lemma contract_balance_is_zero_if_all_purchases_finished :
  forall bstate contract_addr,
    reachable bstate ->
    env_contracts bstate contract_addr = Some (contract : WeakContract) ->
    exists cstate,
      contract_state bstate contract_addr = Some cstate /\
      (Forall (fun '(_, purchase) => purchase_is_finished purchase) 
                    (FMap.elements cstate.(purchases)) ->
      sumZ (fun '(_, purchase) => purchase.(pool)) (FMap.elements cstate.(purchases)) = 0).
  Proof.
    contract_induction; intros; auto; only 1-4 : cbn in *.
    - apply init_correct in init_some; auto; destruct_hyps.
      rewrite H5 in *.
      setoid_rewrite FMap.elements_empty.
      eauto.
    - destruct_message; apply_message_lemma receive_some; destruct_hyps; auto;
      try(rewrite_param new_state.(purchases)); 
      try(rewrite_param new_acts); cbn;
      try (rewrite (sum_pool_add prev_state.(purchases) id x x0) by auto;
      subst; cbn; rewrite IH; lia).
      

      
  Qed.
              
      




Definition purchase_is_timed_out chain state purchase :=
  (purchase.(last_block) + state.(timeout) < chain.(current_slot))%nat.




Lemma on_timeout_someone_can_always_end : forall chain purchaseId prev_state new_state new_acts,
  (exists purchase,
       FMap.find purchaseId prev_state.(purchases) = Some purchase
    /\ ~ purchase_is_finished purchase
    /\ purchase_is_timed_out chain prev_state purchase
  ) ->
  (exists msg,
    (exists ctx, Purchase.receive chain ctx prev_state msg = Ok (new_state, new_acts)) ->
      exists updated_purchase,
            FMap.find purchaseId new_state.(purchases) = Some updated_purchase
        /\ purchase_is_finished updated_purchase
  ).
Proof.
  intros * (purchase & found & not_finished & timed_out).
  unfold purchase_is_finished in *. 
  destruct purchase.(purchase_state) eqn:prev_purchase_state;
  try (now destruct not_finished);
  only 1 : exists (Some (seller_reject_contract purchaseId));
  only 2 : exists (Some (buyer_call_timeout purchaseId));
  only 3 : exists (Some (seller_call_timeout purchaseId));
  only 4 : exists (Some (buyer_call_timeout purchaseId));
  only 5 : exists (Some (seller_call_timeout purchaseId));
  intros (ctx & receive_some);
  apply_message_lemma receive_some; destruct_hyps;
  exists x0; now rewrite_param x0.(purchase_state).
Qed.




Section starat.
    Definition get_contract_state (state : ChainState) (addr : Address) : option State :=
      match env_contract_states state addr with
      | Some serialized_state =>
        deserialize serialized_state
      | None => None
      end.

  
  Context `{caddr : Address} `{miner : Address}.

  Variable s0 : ChainState.

  Hypothesis H_init: is_init_state Purchase.contract caddr s0.

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
  
  Variable init_cstate : Purchase.State.

  Hypothesis H_state : get_contract_state s0 caddr = Some init_cstate.

  (* Variable u_sender : Address.

  Variable pre_s : ChainState. *)

  (* Definition init_cstate := contract_state
  (set_contract_state caddr (serialize init_cstate)
     (add_contract caddr (contract:WeakContract) (transfer_balance u_sender caddr 0 s0)))
  caddr. *)

  Definition u_buyer := (init_cstate.(buyer)).

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
End starat.






End Theories.