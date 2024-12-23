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
  | receive_some : context[receive _ _ _ _ ?msg = Some (_, _)] |- _ => destruct msg as [?m|]; try discriminate; destruct m
  | receive_some : context[Purchase.receive _ _ _ ?msg = Some (_, _)] |- _ => destruct msg as [?m|]; try discriminate; destruct m
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
      destruct (required_amount_zero ctx) eqn:EAmountZero in H; try discriminate
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
      destruct b eqn:EB in H; [ | discriminate H ];
      (* 如果需要注入 tt，可用 injection ；不过通常直接 clear 就够了 *)
      injection H as ->;
      clear H
  end.

  Ltac reduce_required_false :=
    match goal with
    | H : required_false ?b = Some ?u |- _ =>
        unfold required_false in H;
        destruct b eqn:EB in H; [ discriminate H | ];
        injection H as ->;
        clear H
    end.
    
Ltac reduce_required_amount_zero :=
  match goal with
  | H : required_amount_zero ?ctx = Some ?u |- _ =>
      unfold required_amount_zero in H;
      unfold required_true in H;
      destruct (ctx_amount ctx =? 0) eqn:EAmt in H; [ | discriminate H ];
      injection H as ->;
      clear H
  end.

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
      (* 这里你可能需要对 filter 和 forallb 做进一步 destruct，
         但具体写法要看你下一步如何使用 H *)
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
      /\ new_purchase.(notes) = _notes
      /\ new_purchase.(discarded_money) = 0)
  /\ ctx.(ctx_from) <> ctx.(ctx_contract_address)
  /\ prev_state.(listings) = new_state.(listings)
  /\ prev_state.(seller) = new_state.(seller)
  /\ prev_state.(timeout) = new_state.(timeout)
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
      pool := ctx_amount ctx;
      discarded_money := 0 |})
    as new_purchase.
    reduce_buyer_request_purchase_action.
    repeat split; try now inversion receive_some .
    + exists i. repeat split; try now inversion receive_some.
      propify.
      intuition.
    + remember (hash_purchaseId chain.(current_slot) ctx.(ctx_from)) as new_purchaseId.
      exists new_purchaseId, new_purchase.
      repeat split; try now inversion Heqnew_purchase.
      inversion receive_some.
      propify.
      unfold purchase_exists  in EPurchaseExists.
      destruct (find_purchase new_purchaseId (purchases prev_state)) eqn : H';try congruence.
      unfold find_purchase in H'.
      eauto.
      simpl.
      inversion receive_some.
      simpl.
      intuition.
    + reduce_required_no_self_call.
      destruct_address_eq; eauto.
  - intros ([item (prev_item & new_item & amount_sent)] &
            (purchaseId & new_purchase & purchaseId_hash & not_found_purchase & purchase_added & purchase_itemId & purchase_pool & purchase_last_block &
             ppurchase_state & purchase_buyer & purchase_seller_bit & purchase_commit & purchase_notes & purchase_disc_money) &
             not_caddr & const_listings & const_seller & const_timeout & empty_acts).
    receive_simpl_goal.
Qed.
End Theories.