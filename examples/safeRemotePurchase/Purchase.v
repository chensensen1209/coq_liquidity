(* https://raw.githubusercontent.com/SSODelta/DecentralizedCommerce/main/Vendor.sol *)
(* An Incentive-Compatible Smart Contract for Decentralized Commerce *)

(* 

    none
      ↓ (buyer_request_purchase)
    requested
      ↓ (seller_accept_contract) → accepted
      ↓ (seller_reject_contract) → rejected
      ↓ (buyer_abort) → failed

    accepted
      ↓ (seller_item_was_delivered) → delivered
      ↓ (buyer_call_timeout) → failed
      ↓ (seller_call_timeout) → completed

    delivered
      ↓ (buyer_confirm_delivery) → completed
      ↓ (buyer_dispute_delivery) → dispute

    dispute
      ↓ (seller_counter_dispute) → counter
      ↓ (seller_forfeit_dispute) → failed
      ↓ (buyer_call_timeout) → failed

    counter
      ↓ (buyer_open_commitment) → failed

    completed
    rejected
    failed


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

Definition required_true (b: bool) := if b then Some tt else None.
Definition required_false (b: bool) := if b then None else Some tt.

Section EcommerceFixed.

Open Scope Z.
Context {BaseTypes : ChainBase}.
Set Primitive Projections.
Set Nonrecursive Elimination Schemes.
Context {AddrSize : N}.
Context {DepthFirst : bool}.

Definition Error : Type := nat.
Definition default_error : Error := 1%nat.

(* 定义购买状态 *)
Inductive PurchaseState :=
  | requested (* 买家已发起购买请求 *)
  | accepted (* 卖家已接受购买请求 *)
  | rejected (* 卖家已拒绝购买请求 *)
  | delivered (* 卖家已交付商品 *)
  | completed (* 交易已完成，资金已转移 *)
  | dispute (* 购买过程中产生的争议 *)
  | counter (* 卖家对争议提出反驳 *)
  | failed. (* 交易因某种原因失败，资金被退还或其他处理 *)

(* 定义购买状态比较函数 *)
Definition purchase_state_eq (s1 s2 : PurchaseState) : bool :=
  match s1, s2 with
  | requested, requested
  | accepted, accepted
  | rejected, rejected
  | delivered, delivered
  | completed, completed
  | dispute, dispute
  | counter, counter
  | failed,failed => true
  | _, _ => false
  end.

(* 定义商品记录 *)
Record Item :=
  build_item {
    item_value : Amount; (* 商品的价值（价格） *)
    item_description : string (* 商品的描述 *)
  }.


(* 定义购买记录 *)
Record Purchase :=
  build_purchase {
    commit : N; (* 用于承诺的哈希值，理论上应为 bytes32 *)
    last_block : nat; (* 交易相关的最新区块号 *)
    itemId : nat; (* 商品的标识符 *)
    seller_bit : bool; (* 卖家在争议中的一个布尔值，用于验证 *)
    notes : string; (* 买家附加的备注信息 *)
    purchase_state : PurchaseState; (* 当前购买的状态 *)
    buyer : Address; (* 买家的地址 *)
    pool : Amount; (* 购买池中的金额，即买家支付的金额 *)
    discarded_money : Amount; (* 被丢弃的金额，仅用于证明目的 *)
  }.

(* 设置可设置实例 *)

(* 定义商品列表的键类型 *)
Definition listings_key_type := nat.

(* 定义商品列表类型，使用键值映射（FMap）存储商品信息 *)
Definition listings_type := FMap listings_key_type Item.

(* 定义购买记录的键类型 *)
Definition purchase_key_type := N.

(* 定义购买记录类型，使用键值映射（FMap）存储购买信息 *)
Definition purchases_type := FMap purchase_key_type Purchase.

(* 定义合约状态 *)
Record State :=
  build_state {
    seller : Address; (* 卖家的地址 *)
    listings : listings_type; (* 商品列表，键为商品标识符（itemId） *)
    purchases : purchases_type; (* 购买记录，键为购买标识符（purchaseId） *)
    timeout : nat; (* 超时时间，用于控制购买和争议的时限 *)
  }.

(* 定义合约初始化设置 *)
Record Setup :=
  build_setup {
    setup_listings : FMap nat Item; (* 初始商品列表，键为商品标识符（itemId） *)
    setup_timeout : nat (* 初始的超时时间 *)
  }.

(* 定义合约可接收的消息类型 *)
Inductive Msg :=
  | buyer_request_purchase (itemId : nat) (notes : string) (* 买家发起购买请求 *)
  | buyer_abort (id : N) (* 买家取消购买请求 *)
  | buyer_confirm_delivery (id : N) (* 买家确认商品已交付 *)
  | buyer_dispute_delivery (id : N) (commitment : N) (* 买家对交付提出争议 *)
  | buyer_call_timeout (id : N) (* 买家在超时后取消购买 *)
  | buyer_open_commitment (id : N) (buyer_bit : bool) (nonce : N) (* 买家公开承诺以解决争议 *)
  
  | seller_call_timeout (id : N) (* 卖家在超时后确认交付 *)
  | seller_reject_contract (id : N) (* 卖家拒绝购买请求 *)
  | seller_accept_contract (id : N) (* 卖家接受购买请求 *)
  | seller_item_was_delivered (id : N) (* 卖家确认商品已交付 *)
  | seller_forfeit_dispute (id : N) (* 卖家放弃争议 *)
  | seller_counter_dispute (id : N) (random_bit : bool) (* 卖家提出反驳 *)
  | seller_update_listings (itemId : nat) (description : string) (value : Amount). (* 卖家更新商品列表 *)


(* 序列化 *)
Section Serialization.

Global Instance item_settable : Settable Item :=
settable! build_item <item_value;item_description>.

Global Instance purchase_settable : Settable Purchase :=
settable! build_purchase <commit; last_block; itemId; seller_bit; notes;purchase_state;buyer;pool;discarded_money>.

Global Instance state_settable : Settable State :=
settable! build_state <seller; listings; purchases;timeout>.

Global Instance setup_settable : Settable Setup :=
settable! build_setup <setup_listings; setup_timeout>.

  Global Instance Msg_serializable : Serializable Msg :=
    Derive Serializable Msg_rect<
      buyer_request_purchase,
      buyer_abort,
      buyer_confirm_delivery,
      buyer_dispute_delivery,
      buyer_call_timeout,
      buyer_open_commitment,
      seller_call_timeout,
      seller_reject_contract,
      seller_accept_contract,
      seller_item_was_delivered,
      seller_forfeit_dispute,
      seller_counter_dispute,
      seller_update_listings
    >.

  Global Instance Item_serializable : Serializable Item :=
    Derive Serializable Item_rect<build_item>.

  Global Instance Setup_serializable : Serializable Setup :=
    Derive Serializable Setup_rect<build_setup>.

  Global Instance PurchaseState_serializable : Serializable PurchaseState :=
    Derive Serializable PurchaseState_rect<
      requested, accepted, rejected, delivered,
      completed, dispute, counter, failed
    >.
  
  Global Instance Purchase_serializable : Serializable Purchase :=
    Derive Serializable Purchase_rect<build_purchase>.

  Global Instance State_serializable : Serializable State :=
    Derive Serializable State_rect<build_state>.

End Serialization.

(* 全局定义序列化函数 *)
Global Definition serializeMsg msg := (@serialize Msg _) msg.
Global Definition serializeState state := (@serialize State _) state.
Global Definition serializeSetup setup := (@serialize Setup _) setup.
Global Definition serializeItem item := (@serialize Item _) item.
Global Definition serializePurchase purchase := (@serialize Purchase _) purchase.
Global Definition serializePurchaseState purchaseState := (@serialize PurchaseState _) purchaseState.

(* 定义全局强制转换为 SerializedValue *)
Global Coercion serializeMsg : Msg >-> SerializedValue.
Global Coercion serializeState : State >-> SerializedValue.
Global Coercion serializeSetup : Setup >-> SerializedValue.
Global Coercion serializeItem : Item >-> SerializedValue.
Global Coercion serializePurchase : Purchase >-> SerializedValue.
Global Coercion serializePurchaseState : PurchaseState >-> SerializedValue.


(* 
 根据商品的唯一标识符 `itemId`，在商品列表 `listings` 中查找对应的商品。
  参 数:
  - itemId: 商品的唯一标识符，类型为 `nat`。
  - listings: 当前的商品列表，类型为 `listings_type`，即 `FMap nat Item`。
*)
Definition find_item itemId (listings : listings_type) := FMap.find itemId listings.

(* 
根据购买的唯一标识符 `purchaseId`，在购买记录 `purchases` 中查找对应的购买记录。
参数:
    - purchaseId: 购买的唯一标识符，类型为 `N`。
    - purchases: 当前的购买记录，类型为 `purchases_type`，即 `FMap N Purchase`。
*)
Definition find_purchase purchaseId (purchases : purchases_type) := FMap.find purchaseId purchases.

(* 检查调用者发送的金额是否为零 *)
Definition required_amount_zero ctx := required_true (ctx.(ctx_amount) =? 0).

(* 检查是否为合约自调用
    用于防止合约自身调用其自身，避免潜在的重入攻击等问题。 *)
Definition required_no_self_call ctx := required_false (ctx.(ctx_from) =? ctx.(ctx_contract_address))%address.

(* 
用于判断给定的 `purchaseId` 是否已经存在于购买记录中。
参数:
  - purchaseId: 购买的唯一标识符，类型为 `purchase_key_type`（即 `N`）。
  - purchases: 当前的购买记录，类型为 `purchases_type`，即 `FMap N Purchase`。
 *)
Definition purchase_exists purchaseId purchases :=
    match find_purchase purchaseId purchases with
    | Some _ => true
    | None => false
    end.

(* 
哈希购买ID函数
  生成一个唯一的购买ID，基于当前区块号 `n` 和买家的地址 `addr`。
*)
Definition hash_purchaseId (n : nat) (addr : Address) : N :=
    Npos (countable.encode (n, addr)).
    
(* 
哈希出价函数
  生成一个哈希值，用于买家在争议过程中提交的证明。
*)
Definition hash_bid (id : N) (buyer_bit : bool) (nonce : N) : N :=
    Npos (countable.encode (id, buyer_bit, nonce)).

Definition init (chain : Chain) 
               (ctx : ContractCallContext) 
               (setup : Setup)
  : result State Error :=
  (* 检查是否为自调用 *)
  if required_no_self_call ctx then
    let seller := ctx_from ctx in
    let listings := setup_listings setup in
    let timeout := setup_timeout setup in
    (* 检查 timeout 是否大于 0 *)
    if (0 <? timeout)%nat then
      (* 检查发送的金额是否为零 *)
      if required_amount_zero ctx then
        Ok {|
          seller := seller;
          listings := listings;
          purchases := FMap.empty;
          timeout := chain.(current_slot) + timeout;
        |}
      else
        Err default_error (* 错误：发送的金额不是零 *)
    else
      Err default_error (* 错误：timeout 不合法 *)
  else
    Err default_error. (* 错误：自调用不被允许 *)

(* 用于处理买家的购买请求 *)
(* 买家发送资金 *)
(* 状态变为request ： 买家请求购买 *)
Definition buyer_request_purchase_action (chain : Chain) 
                                        (ctx : ContractCallContext) 
                                        (state : State)
                                        (_itemId : nat) 
                                        (notes : string)
                                        : result (State * list ActionBody) Error :=
  (* 检查是否为自调用，防止合约自身调用此函数 *)
  if required_no_self_call ctx then
    (* 获取调用者地址，作为买家的地址 *)
    let _buyer := ctx_from ctx in
    (* 获取当前的商品列表 *)
    let current_listings := listings state in
    (* 根据 itemId 查找对应的商品 *)
    match find_item _itemId current_listings with
    | Some requested_item =>
        (* 检查调用者发送的金额是否与商品的价格一致 *)
        if (item_value requested_item) =? ctx.(ctx_amount) then
          (* 获取当前区块号 *)
          let _current_slot := chain.(current_slot) in
          (* 生成唯一的购买 ID，基于当前区块号和买家地址 *)
          let purchaseId := hash_purchaseId _current_slot _buyer in
          (* 检查生成的购买 ID 是否已存在，避免重复购买 *)
          if negb (purchase_exists purchaseId (purchases state)) then
            (* 创建一个新的购买记录 *)
            let purchase :=
              {|
                commit := 0; (* 初始承诺值，暂时设为 0 *)
                last_block := _current_slot; (* 记录当前区块号 *)
                itemId := _itemId; (* 商品标识符 *)
                seller_bit := false; (* 卖家的布尔值，初始为 false *)
                notes := notes; (* 买家附加的备注信息 *)
                purchase_state := requested; (* 设置购买状态为 requested *)
                buyer := _buyer; (* 记录买家的地址 *)
                pool := ctx.(ctx_amount); (* 记录购买池中的金额，即买家支付的金额 *)
                discarded_money := 0; (* 被丢弃的金额，初始为 0 *)
              |} in
            (* 将新的购买记录添加到购买映射中 *)
            let updated_purchases := FMap.add purchaseId purchase (purchases state) in
            (* 更新合约的状态，包含新的购买记录 *)
            let updated_state := state <| purchases := updated_purchases |> in
            (* 返回更新后的状态和空的动作列表，表示没有需要执行的额外动作 *)
            Ok (updated_state, [])
          else
            (* 错误：购买 ID 已存在，可能是重复购买 *)
            Err default_error
        else
          (* 错误：发送的金额与商品的价格不符 *)
          Err default_error
    | None =>
        (* 错误：未找到对应的商品，可能是无效的 itemId *)
        Err default_error
    end
  else
    (* 错误：自调用不被允许，防止合约自身进行调用 *)
    Err default_error.


(* 买家取消购买请求的操作 *)
(* 状态requested变为failed：交易失败 *)
Definition buyer_abort_action (ctx : ContractCallContext) 
                              (state : State) 
                              (purchaseId : purchase_key_type)
  : result (State * list ActionBody) Error :=
  (* 检查发送的金额是否为零 *)
  if required_amount_zero ctx then
    (* 获取当前的购买记录映射 *)
    let current_purchases := purchases state in
    (* 根据 purchaseId 查找对应的购买记录 *)
    match find_purchase purchaseId current_purchases with
    | Some purchase =>
        (* 检查购买状态是否为 'requested' *)
        if purchase_state_eq purchase.(purchase_state) requested then
          (* 检查调用者是否为该购买的买家 *)
          if ((ctx_from ctx) =? purchase.(buyer))%address then
            (* 更新购买记录的状态为 'failed'，并将池中的金额设为零 *)
            let updated_purchase := purchase <| purchase_state := failed |>
                                             <| pool := 0 |> in
            (* 将更新后的购买记录添加回购买记录映射中 *)
            let updated_purchases := FMap.add purchaseId updated_purchase current_purchases in
            (* 更新合约状态，包含更新后的购买记录 *)
            let updated_state := state <| purchases := updated_purchases |> in
            (* 定义需要执行的动作列表，这里是将资金转回买家 *)
            let actions := [act_transfer purchase.(buyer) purchase.(pool)] in
            (* 返回更新后的状态和动作列表，表示成功 *)
            Ok (updated_state, actions)
          else
            (* 错误：调用者不是买家 *)
            Err default_error
        else
          (* 错误：购买状态不是 'requested' *)
          Err default_error
    | None =>
        (* 错误：未找到对应的购买记录 *)
        Err default_error
    end
  else
    (* 错误：发送的金额不是零 *)
    Err default_error.

(* 于处理买家确认商品已交付的操作 *)
(* delivered:卖家已交付商品 *)
(* completed:交易已完成，资金已转移 *)
(* 状态delivered -》 completed ： 交易完成 *)
Definition buyer_confirm_delivery_action (ctx : ContractCallContext) 
                                         (state : State) 
                                         (purchaseId : purchase_key_type)
  : result (State * list ActionBody) Error :=
  (* 检查发送的金额是否为零 *)
  if required_amount_zero ctx then
    (* 获取当前的购买记录映射 *)
    let current_purchases := purchases state in
    (* 根据 purchaseId 查找对应的购买记录 *)
    match find_purchase purchaseId current_purchases with
    | Some purchase =>
        (* 检查购买状态是否为 'delivered' *)
        if purchase_state_eq purchase.(purchase_state) delivered then
          (* 检查调用者是否为买家 *)
          if ((ctx_from ctx) =? purchase.(buyer))%address then
            (* 更新购买记录的状态为 'completed'，并将池中的金额设为零 *)
            let updated_purchase := purchase <| purchase_state := completed |>
                                             <| pool := 0 |> in
            (* 将更新后的购买记录添加回购买记录映射中 *)
            let updated_purchases := FMap.add purchaseId updated_purchase current_purchases in
            (* 更新合约状态，包含更新后的购买记录 *)
            let updated_state := state <| purchases := updated_purchases |> in
            (* 定义需要执行的动作列表，这里是将资金转给卖家 *)
            let actions := [act_transfer state.(seller) purchase.(pool)] in
            (* 返回更新后的状态和动作列表，表示操作成功 *)
            Ok (updated_state, actions)
          else
            (* 错误：调用者不是买家 *)
            Err default_error
        else
          (* 错误：购买状态不是 'delivered' *)
          Err default_error
    | None =>
        (* 错误：未找到对应的购买记录 *)
        Err default_error
    end
  else
    (* 错误：发送的金额不是零 *)
    Err default_error.

(* 买家在商品交付后对交付提出争议 *)
(* delivered:卖家已交付商品 *)
(* dispute: 购买过程中产生的争议*)
(* delivered -》 dispute *)
Definition buyer_dispute_delivery_action (ctx : ContractCallContext) 
                                         (state : State) 
                                         (chain : Chain) 
                                         (purchaseId : purchase_key_type) 
                                         (commitment : N)
      : result (State * list ActionBody) Error :=
  let current_purchases := purchases state in
  (* 查找购买记录 *)
  match find_purchase purchaseId current_purchases with
  | Some purchase =>
      (* 查找对应的商品 *)
      match find_item purchase.(itemId) (listings state) with
      | Some item =>
          (* 检查发送的金额是否与商品价值一致 *)
          if (ctx.(ctx_amount) =? item.(item_value)) then
            (* 检查购买状态是否为 delivered *)
            if purchase_state_eq purchase.(purchase_state) delivered then
              (* 检查调用者是否为买家 *)
              if ((ctx_from ctx) =? purchase.(buyer))%address then
                (* 更新购买记录的状态为 dispute，记录承诺值和最新区块号，更新资金池 *)
                let updated_purchase := purchase <| purchase_state := dispute |>
                                                 <| commit := commitment |>
                                                 <| last_block := current_slot chain |>
                                                 <| pool := purchase.(pool) + item.(item_value) |> in
                (* 将更新后的购买记录添加回购买记录映射中 *)
                let updated_purchases := FMap.add purchaseId updated_purchase current_purchases in
                (* 更新合约状态，包含更新后的购买记录 *)
                let updated_state := state <| purchases := updated_purchases |> in
                (* 返回更新后的状态和空的动作列表，表示没有需要执行的额外动作 *)
                Ok (updated_state, [])
              else
                Err default_error (* 错误：调用者不是买家 *)
            else
              Err default_error (* 错误：购买状态不是 delivered *)
          else
            Err default_error (* 错误：发送的金额与商品价值不符 *)
      | None =>
          Err default_error (* 错误：未找到对应的商品 *)
      end
  | None =>
      Err default_error (* 错误：未找到对应的购买记录 *)
  end.

(* 允许买家在购买进入 dispute 或 accepted 状态后，等待超时后取消购买。 *)
(* accepted卖家已接受购买请求 *)
(* dispute购买过程中有争议 *)
(* dispute||accepted => failed *)
Definition buyer_call_timeout_action (ctx : ContractCallContext) 
                                    (state : State) 
                                    (chain : Chain) 
                                    (purchaseId : purchase_key_type)
      : result (State * list ActionBody) Error :=
  (* 检查发送的金额是否为零 *)
  if required_amount_zero ctx then
    (* 获取当前的购买记录映射 *)
    let current_purchases := purchases state in
    (* 根据 purchaseId 查找对应的购买记录 *)
    match find_purchase purchaseId current_purchases with
    | Some purchase =>
        (* 检查购买状态是否为 dispute 或 accepted *)
        if purchase_state_eq purchase.(purchase_state) dispute || purchase_state_eq purchase.(purchase_state) accepted then
          (* 检查调用者是否为买家 *)
          if ((ctx_from ctx) =? purchase.(buyer))%address then
            (* 检查是否超过超时 *)
            if (purchase.(last_block) + state.(timeout) <? chain.(current_slot))%nat then
              (* 更新购买记录的状态为 failed，清空资金池 *)
              let updated_purchase := purchase <| purchase_state := failed |>
                                               <| pool := 0 |> in
              (* 将更新后的购买记录添加回购买记录映射中 *)
              let updated_purchases := FMap.add purchaseId updated_purchase current_purchases in
              (* 更新合约状态，包含更新后的购买记录 *)
              let updated_state := state <| purchases := updated_purchases |> in
              (* 定义需要执行的动作列表，这里是将资金退还给买家 *)
              let actions := [act_transfer purchase.(buyer) purchase.(pool)] in
              (* 返回更新后的状态和动作列表，表示操作成功 *)
              Ok (updated_state, actions)
            else
              Err default_error (* 错误：尚未到达超时区块 *)
          else
            Err default_error (* 错误：调用者不是买家 *)
        else
          Err default_error (* 错误：购买状态不是 dispute 或 accepted *)
    | None =>
        Err default_error (* 错误：未找到对应的购买记录 *)
    end
  else
    Err default_error. (* 错误：发送的金额不是零 *)

(* 买家在争议过程中公开其承诺，以解决争议。 *)
Definition buyer_open_commitment_action (ctx : ContractCallContext) 
                                        (state : State) 
                                        (purchaseId : purchase_key_type) 
                                        (buyer_bit : bool) 
                                        (nonce : N)
      : result (State * list ActionBody) Error :=
  (* 检查调用时发送的金额是否为零 *)
  if required_amount_zero ctx then
    (* 获取当前的购买记录 *)
    let current_purchases := purchases state in
    (* 根据 purchaseId 查找对应的购买记录 *)
    match find_purchase purchaseId current_purchases with
    | Some purchase =>
        (* 根据购买记录中的 itemId 查找对应的商品 *)
        match find_item purchase.(itemId) (listings state) with
        | Some item =>
            (* 检查调用者是否为该购买的买家 *)
            if ((ctx_from ctx) =? purchase.(buyer))%address then
              (* 检查购买状态是否为 counter，即卖家已提出反驳 *)
              if purchase_state_eq purchase.(purchase_state) counter then
                (* 验证买家提交的哈希值是否与之前的 commit 匹配 *)
                if (hash_bid purchaseId buyer_bit nonce =? purchase.(commit))%N then
                  (* 计算需要发送给买家或卖家的金额，池中的金额减去商品价值 *)
                  let to_send := purchase.(pool) - item.(item_value) in
                  (* 更新购买记录：状态设为 failed，清空资金池，记录被丢弃的金额 *)
                  let updated_purchase := purchase <| purchase_state := failed |>
                                                   <| pool := 0 |>
                                                   <| discarded_money := item.(item_value) |> in
                  (* 将更新后的购买记录添加回购买记录映射中 *)
                  let updated_purchases := FMap.add purchaseId updated_purchase current_purchases in
                  (* 决定将资金转移给买家还是卖家，取决于 seller_bit 与 buyer_bit 的比较 *)
                  let target_transaction := if (Bool.eqb purchase.(seller_bit) buyer_bit) 
                                            then purchase.(buyer) 
                                            else state.(seller) in
                  (* 更新合约状态，包含新的购买记录 *)
                  let updated_state := state <| purchases := updated_purchases |> in
                  (* 定义需要执行的动作列表，这里是将计算出的金额转移给目标地址 *)
                  let actions := [act_transfer target_transaction to_send] in
                  (* 返回更新后的状态和动作列表，表示操作成功 *)
                  Ok (updated_state, actions)
                else
                  (* 错误：买家提交的哈希值不正确，可能是无效的证明 *)
                  Err default_error
              else
                (* 错误：购买状态不是 counter，无法进行承诺公开 *)
                Err default_error
            else
              (* 错误：调用者不是买家，无法公开承诺 *)
              Err default_error
        | None =>
            (* 错误：未找到对应的商品，可能是无效的 itemId *)
            Err default_error
        end
    | None =>
        (* 错误：未找到对应的购买记录，可能是无效的 purchaseId *)
        Err default_error
    end
  else
    (* 错误：调用时发送的金额不是零，违反了操作要求 *)
    Err default_error.


(* 卖家在购买进入 delivered 或 counter 状态后，等待超时后确认交付。 *)
(* delivered||counter -》 completed *)
Definition seller_call_timeout_action (ctx : ContractCallContext) 
                                      (state : State) 
                                      (chain : Chain) 
                                      (purchaseId : purchase_key_type)
      : result (State * list ActionBody) Error :=
  (* 检查调用时发送的金额是否为零 *)
  if required_amount_zero ctx then
    (* 获取当前的购买记录 *)
    let current_purchases := purchases state in
    (* 根据 purchaseId 查找对应的购买记录 *)
    match find_purchase purchaseId current_purchases with
    | Some purchase =>
        (* 检查购买状态是否为 'delivered' 或 'counter' *)
        if purchase_state_eq purchase.(purchase_state) delivered 
           || purchase_state_eq purchase.(purchase_state) counter then
          (* 检查调用者是否为卖家 *)
          if ((ctx_from ctx) =? state.(seller))%address then
            (* 检查是否已经超过超时区块 *)
            if (purchase.(last_block) + state.(timeout) <? chain.(current_slot))%nat then
              (* 更新购买记录的状态为 'completed'，并将资金池设为零 *)
              let updated_purchase := purchase <| purchase_state := completed |>
                                               <| pool := 0 |> in
              (* 将更新后的购买记录添加回购买记录映射中 *)
              let updated_purchases := FMap.add purchaseId updated_purchase current_purchases in
              (* 更新合约状态，包含更新后的购买记录 *)
              let updated_state := state <| purchases := updated_purchases |> in
              (* 定义需要执行的动作列表，这里是将资金转给卖家 *)
              let actions := [act_transfer state.(seller) purchase.(pool)] in
              (* 返回更新后的状态和动作列表，表示操作成功 *)
              Ok (updated_state, actions)
            else
              (* 错误：尚未到达超时区块，无法执行超时操作 *)
              Err default_error
          else
            (* 错误：调用者不是卖家，无法执行超时操作 *)
            Err default_error
        else
          (* 错误：购买状态不是 'delivered' 或 'counter'，无法执行超时操作 *)
          Err default_error
    | None =>
        (* 错误：未找到对应的购买记录，可能是无效的 purchaseId *)
        Err default_error
    end
  else
    (* 错误：调用时发送的金额不是零，违反了操作要求 *)
    Err default_error.

(* 卖家拒绝处于 requested 状态的购买请求 *)
(* requested -》 rejected *)
Definition seller_reject_contract_action (ctx : ContractCallContext) 
                                        (state : State) 
                                        (purchaseId : purchase_key_type)
      : result (State * list ActionBody) Error :=
  (* 检查调用时发送的金额是否为零 *)
  if required_amount_zero ctx then
    (* 获取当前的购买记录映射 *)
    let current_purchases := purchases state in
    (* 根据 purchaseId 查找对应的购买记录 *)
    match find_purchase purchaseId current_purchases with
    | Some purchase =>
        (* 检查购买记录的当前状态是否为 'requested' *)
        if purchase_state_eq purchase.(purchase_state) requested then
          (* 检查调用者是否为卖家 *)
          if ((ctx_from ctx) =? state.(seller))%address then
            (* 更新购买记录的状态为 'rejected'，并清空资金池 *)
            let updated_purchase := purchase <| purchase_state := rejected |>
                                             <| pool := 0 |> in
            (* 将更新后的购买记录添加回购买记录映射中 *)
            let updated_purchases := FMap.add purchaseId updated_purchase current_purchases in
            (* 更新合约状态，包含更新后的购买记录 *)
            let updated_state := state <| purchases := updated_purchases |> in
            (* 定义需要执行的动作列表，这里是将资金退还给买家 *)
            let actions := [act_transfer purchase.(buyer) purchase.(pool)] in
            (* 返回更新后的状态和动作列表，表示操作成功 *)
            Ok (updated_state, actions)
          else
            (* 错误：调用者不是卖家 *)
            Err default_error
        else
          (* 错误：购买状态不是 'requested'，无法拒绝合同 *)
          Err default_error
    | None =>
        (* 错误：未找到对应的购买记录，可能是无效的 purchaseId *)
        Err default_error
    end
  else
    (* 错误：调用时发送的金额不是零，违反了操作要求 *)
    Err default_error.


(* 允许卖家接受处于 requested 状态的购买请求。 *)
(* requested -》 accepted *)
Definition seller_accept_contract_action (ctx : ContractCallContext) 
                                        (state : State) 
                                        (chain : Chain) 
                                        (purchaseId : purchase_key_type)
      : result (State * list ActionBody) Error :=
  (* 检查调用时发送的金额是否为零 *)
  if required_amount_zero ctx then
    (* 获取当前的购买记录映射 *)
    let current_purchases := purchases state in
    (* 根据 purchaseId 查找对应的购买记录 *)
    match find_purchase purchaseId current_purchases with
    | Some purchase =>
        (* 检查购买记录的当前状态是否为 'requested' *)
        if purchase_state_eq purchase.(purchase_state) requested then
          (* 检查调用者是否为卖家 *)
          if ((ctx_from ctx) =? state.(seller))%address then
            (* 更新购买记录的状态为 'accepted'，并记录当前区块号 *)
            let updated_purchase := purchase <| purchase_state := accepted |>
                                             <| last_block := chain.(current_slot) |> in
            (* 将更新后的购买记录添加回购买记录映射中 *)
            let updated_purchases := FMap.add purchaseId updated_purchase current_purchases in
            (* 更新合约状态，包含更新后的购买记录 *)
            let updated_state := state <| purchases := updated_purchases |> in
            (* 定义需要执行的动作列表，这里没有需要执行的动作 *)
            Ok (updated_state, [])
          else
            (* 错误：调用者不是卖家 *)
            Err default_error
        else
          (* 错误：购买状态不是 'requested'，无法接受合同 *)
          Err default_error
    | None =>
        (* 错误：未找到对应的购买记录，可能是无效的 purchaseId *)
        Err default_error
    end
  else
    (* 错误：调用时发送的金额不是零，违反了操作要求 *)
    Err default_error.

(* 允许卖家将购买状态标记为已交付 (delivered) *)
(* accepted -》 delivered *)
Definition seller_item_was_delivered_action (ctx : ContractCallContext) 
                                            (state : State) 
                                            (chain : Chain) 
                                            (purchaseId : purchase_key_type)
          : result (State * list ActionBody) Error :=
      (* 检查调用时发送的金额是否为零 *)
      if required_amount_zero ctx then
        (* 获取当前的购买记录映射 *)
        let current_purchases := purchases state in
        (* 根据 purchaseId 查找对应的购买记录 *)
        match find_purchase purchaseId current_purchases with
        | Some purchase =>
            (* 检查购买记录的当前状态是否为 'accepted' *)
            if purchase_state_eq purchase.(purchase_state) accepted then
              (* 检查调用者是否为卖家 *)
              if ((ctx_from ctx) =? state.(seller))%address then
                (* 更新购买记录的状态为 'delivered'，并记录当前区块号 *)
                let updated_purchase := purchase <| purchase_state := delivered |>
                                                 <| last_block := chain.(current_slot) |> in
                (* 将更新后的购买记录添加回购买记录映射中 *)
                let updated_purchases := FMap.add purchaseId updated_purchase current_purchases in
                (* 更新合约状态，包含更新后的购买记录 *)
                let updated_state := state <| purchases := updated_purchases |> in
                (* 返回更新后的状态和空的动作列表，表示操作成功且无需执行额外动作 *)
                Ok (updated_state, [])
              else
                (* 错误：调用者不是卖家 *)
                Err default_error
            else
              (* 错误：购买状态不是 'accepted'，无法标记为已交付 *)
              Err default_error
        | None =>
            (* 错误：未找到对应的购买记录，可能是无效的 purchaseId *)
            Err default_error
        end
      else
        (* 错误：调用时发送的金额不是零，违反了操作要求 *)
        Err default_error.

(* 允许卖家在购买进入争议 (dispute) 状态时放弃争议。 *)
(* dispute -》 failed *)
Definition seller_forfeit_dispute_action (ctx : ContractCallContext) 
                                            (state : State) 
                                            (purchaseId : purchase_key_type)
          : result (State * list ActionBody) Error :=
      (* 检查调用时发送的金额是否为零 *)
      if required_amount_zero ctx then
        (* 获取当前的购买记录映射 *)
        let current_purchases := purchases state in
        (* 根据 purchaseId 查找对应的购买记录 *)
        match find_purchase purchaseId current_purchases with
        | Some purchase =>
            (* 检查购买记录的当前状态是否为 'dispute' *)
            if purchase_state_eq purchase.(purchase_state) dispute then
              (* 检查调用者是否为卖家 *)
              if ((ctx_from ctx) =? state.(seller))%address then
                (* 更新购买记录的状态为 'failed'，并清空资金池 *)
                let updated_purchase := purchase <| purchase_state := failed |>
                                                 <| pool := 0 |> in
                (* 将更新后的购买记录添加回购买记录映射中 *)
                let updated_purchases := FMap.add purchaseId updated_purchase current_purchases in
                (* 更新合约状态，包含更新后的购买记录 *)
                let updated_state := state <| purchases := updated_purchases |> in
                (* 定义需要执行的动作列表，这里是将资金退还给买家 *)
                let actions := [act_transfer purchase.(buyer) purchase.(pool)] in
                (* 返回更新后的状态和动作列表，表示操作成功 *)
                Ok (updated_state, actions)
              else
                (* 错误：调用者不是卖家 *)
                Err default_error
            else
              (* 错误：购买状态不是 'dispute'，无法放弃争议 *)
              Err default_error
        | None =>
            (* 错误：未找到对应的购买记录，可能是无效的 purchaseId *)
            Err default_error
        end
      else
        (* 错误：调用时发送的金额不是零，违反了操作要求 *)
        Err default_error.

(* 允许卖家在购买请求处于 dispute 状态时，通过提交一个随机位 (random_bit) 来提出反驳。 *)
Definition seller_counter_dispute_action (ctx : ContractCallContext) 
                                         (state : State) 
                                         (chain : Chain) 
                                         (purchaseId : purchase_key_type) 
                                         (random_bit : bool)
      : result (State * list ActionBody) Error :=
  let current_purchases := purchases state in
  (* 查找购买记录 *)
  match find_purchase purchaseId current_purchases with
  | Some purchase =>
      (* 检查购买状态是否为 'dispute' *)
      if purchase_state_eq purchase.(purchase_state) dispute then
        (* 检查调用者是否为卖家 *)
        if ((ctx_from ctx) =? state.(seller))%address then
          let money_sent := ctx.(ctx_amount) in
          (* 查找对应的商品 *)
          match find_item purchase.(itemId) (listings state) with
          | Some disputed_item =>
              (* 检查发送的金额是否与商品价值一致 *)
              if (money_sent =? disputed_item.(item_value)) then
                (* 更新购买记录：
                   - 将状态设置为 'counter'，表示卖家提出反驳
                   - 记录当前区块号
                   - 设置卖家的随机位
                   - 增加资金池中的金额 *)
                let updated_purchase := purchase <| purchase_state := counter |>
                                                 <| last_block := chain.(current_slot) |>
                                                 <| seller_bit := random_bit |>
                                                 <| pool := purchase.(pool) + money_sent |> in
                (* 将更新后的购买记录添加回购买记录映射中 *)
                let updated_purchases := FMap.add purchaseId updated_purchase current_purchases in
                (* 决定资金的去向：
                   - 如果卖家的随机位与提交的随机位相同，则将资金转移给买家
                   - 否则，将资金转移给卖家 *)
                let target_transaction := if Bool.eqb purchase.(seller_bit) random_bit 
                                          then purchase.(buyer) 
                                          else state.(seller) in
                (* 更新合约状态，包含新的购买记录 *)
                let updated_state := state <| purchases := updated_purchases |> in
                (* 定义需要执行的动作列表，这里是将资金转移给目标地址 *)
                let actions := [act_transfer target_transaction (purchase.(pool) + money_sent)] in
                (* 返回更新后的状态和动作列表，表示操作成功 *)
                Ok (updated_state, actions)
              else
                Err default_error (* 错误：发送的金额与商品价值不符 *)
          | None =>
              Err default_error (* 错误：未找到对应的商品 *)
          end
        else
          Err default_error (* 错误：调用者不是卖家 *)
      else
        Err default_error (* 错误：购买状态不是 'dispute' *)
  | None =>
      Err default_error (* 错误：未找到对应的购买记录 *)
  end.


(* 辅助函数：检查指定 itemId 是否没有活跃的购买记录 *)
Definition no_active_purchase_for_itemId state _itemId :=
  (* 获取所有购买记录 *)
  let all_key_purchases := FMap.elements state.(purchases) in 
  let key_purchases_for_itemId := filter (fun '(_, purchase) => 
      (* 过滤出指定 itemId 的购买记录 *)
      (purchase.(itemId) =? _itemId)%nat)  all_key_purchases in 
  forallb
    (fun '(_, purchase) =>
      match purchase.(purchase_state) with
      (* 购买状态为完成、拒绝或失败的视为无活跃购买 *)
      | completed | rejected | failed => true 
      (* 其他状态视为有活跃购买 *)
      | _ => false 
      end)
    key_purchases_for_itemId. (* 检查所有相关购买记录的状态 *)

(* 允许卖家更新商品列表中的某个商品信息，但前提是该商品没有任何活跃的购买记录。 *)
Definition seller_update_listings_action (ctx : ContractCallContext) 
                                         (state : State) 
                                         (itemId : nat) 
                                         (descr : string) 
                                         (value : Amount)
  : result (State * list ActionBody) Error :=
  (* 检查调用时发送的金额是否为零 *)
  if required_amount_zero ctx then
    (* 检查 value 是否非负 *)
    if (0 <=? value) then
      (* 检查调用者是否为卖家 *)
      if (ctx.(ctx_from) =? state.(seller))%address then
        (* 检查是否没有活跃的购买 *)
        if no_active_purchase_for_itemId state itemId then
          (* 获取当前的商品列表 *)
          let current_listings := listings state in
          (* 创建新的商品记录 *)
          let new_item := {|
            item_value := value;
            item_description := descr
          |} in 
          (* 将新的商品添加到商品列表中 *)
          let updated_listings := FMap.add itemId new_item current_listings in
          (* 更新合约状态，包含新的商品列表 *)
          let updated_state := state <| listings := updated_listings |> in
          (* 返回更新后的状态和空的动作列表，表示操作成功 *)
          Ok (updated_state, [])
        else
          (* 错误：存在活跃的购买，无法更新商品列表 *)
          Err default_error
      else
        (* 错误：调用者不是卖家，无法更新商品列表 *)
        Err default_error
    else
      (* 错误：value 不合法，必须为非负 *)
      Err default_error
  else
    (* 错误：调用时发送的金额不是零，违反了操作要求 *)
    Err default_error.


Definition receive (chain : Chain) 
                   (ctx : ContractCallContext)
                   (state : State) 
                   (msg : option Msg)
                   : result (State * list ActionBody) Error :=
  match msg with
  | Some msg_content =>
      match msg_content with
      | buyer_request_purchase itemId notes =>
          (* 处理买家发起购买请求 *)
          (* 状态转移：none → requested *)
          buyer_request_purchase_action chain ctx state itemId notes

      | buyer_abort id =>
          (* 处理买家取消购买请求 *)
          (* 状态转移：requested → failed *)
          buyer_abort_action ctx state id

      | buyer_confirm_delivery id =>
          (* 处理买家确认收货 *)
          (* 状态转移：delivered → completed *)
          buyer_confirm_delivery_action ctx state id

      | buyer_dispute_delivery id commitment =>
          (* 处理买家对交付提出争议 *)
          (* 状态转移：delivered → dispute *)
          buyer_dispute_delivery_action ctx state chain id commitment

      | buyer_call_timeout id =>
          (* 处理买家在争议或接受后调用超时 *)
          (* 状态转移：dispute 或 accepted → failed *)
          buyer_call_timeout_action ctx state chain id

      | buyer_open_commitment id buyer_bit nonce =>
          (* 处理买家公开承诺以解决争议 *)
          (* 状态转移：counter → failed *)
          buyer_open_commitment_action ctx state id buyer_bit nonce

      | seller_call_timeout id =>
          (* 处理卖家在交付或反驳后调用超时 *)
          (* 状态转移：delivered 或 counter → completed *)
          seller_call_timeout_action ctx state chain id

      | seller_reject_contract id =>
          (* 处理卖家拒绝购买请求 *)
          (* 状态转移：requested → rejected *)
          seller_reject_contract_action ctx state id

      | seller_accept_contract id =>
          (* 处理卖家接受购买请求 *)
          (* 状态转移：requested → accepted *)
          seller_accept_contract_action ctx state chain id

      | seller_item_was_delivered id =>
          (* 处理卖家标记商品为已交付 *)
          (* 状态转移：accepted → delivered *)
          seller_item_was_delivered_action ctx state chain id

      | seller_forfeit_dispute id =>
          (* 处理卖家放弃争议 *)
          (* 状态转移：dispute → failed *)
          seller_forfeit_dispute_action ctx state id

      | seller_counter_dispute id random_bit =>
          (* 处理卖家提出反驳 *)
          (* 状态转移：dispute → counter *)
          seller_counter_dispute_action ctx state chain id random_bit

      | seller_update_listings itemId description value =>
          (* 处理卖家更新商品列表 *)
          (* 状态转移：无 *)
          seller_update_listings_action ctx state itemId description value
      end
  | None =>
      (* 错误：未接收到消息 *)
      Err default_error
  end
.


Definition contract : Contract Setup Msg State Error := 
    build_contract init receive.

End EcommerceFixed.






