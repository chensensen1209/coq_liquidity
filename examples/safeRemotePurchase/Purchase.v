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

Inductive PurchaseState :=
  | requested
  | accepted
  | rejected
  | delivered
  | completed
  | dispute
  | counter
  | failed.

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

Record Item :=
  build_item {
    item_value : Amount;
    item_description : string
  }.

Record Purchase :=
  build_purchase {
    commit : N; (* Should be bytes32*)
    last_block : nat; (* slot in the Chain*)
    itemId : nat;
    seller_bit : bool;
    notes : string;
    purchase_state : PurchaseState;
    buyer : Address;
    pool : Amount;
    discarded_money : Amount; (* For proof purposes only. *)
  }.

(* 设置可设置实例 *)

Definition listings_key_type := nat.
Definition listings_type := FMap listings_key_type Item.

Definition purchase_key_type := N.
Definition purchases_type := FMap purchase_key_type Purchase.

Record State :=
  build_state {
    seller: Address;
    listings : listings_type; (* Key is the item identifier *)
    purchases : purchases_type; (* TODO N should be somethings that corresponds to [bytes32] in Solidity!!  *)
    timeout : nat;
  }.

Record Setup :=
  build_setup {
    setup_listings : FMap nat Item;
    setup_timeout : nat
  }.

Inductive Msg :=
  | buyer_request_purchase (itemId : nat) (notes : string)
  | buyer_abort (id : N) 
  | buyer_confirm_delivery (id : N)
  | buyer_dispute_delivery (id : N) (commitment : N)
  | buyer_call_timeout (id : N)
  | buyer_open_commitment (id : N) (buyer_bit : bool) (nonce : N)
  
  | seller_call_timeout (id : N)
  | seller_reject_contract (id : N)
  | seller_accept_contract (id : N)
  | seller_item_was_delivered (id : N)
  | seller_forfeit_dispute (id : N)
  | seller_counter_dispute (id : N) (random_bit : bool)
  | seller_update_listings (itemId : nat) (description : string) (value : Amount)
  .

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

Definition find_item itemId (listings : listings_type) := FMap.find itemId listings.

Definition find_purchase purchaseId (purchases : purchases_type) := FMap.find purchaseId purchases.

Definition required_amount_zero ctx := required_true (ctx.(ctx_amount) =? 0).

Definition required_no_self_call ctx := required_false (ctx.(ctx_from) =? ctx.(ctx_contract_address))%address.
Definition purchase_exists purchaseId purchases :=
    match find_purchase purchaseId purchases with
    | Some _ => true
    | None => false
    end.

(* TEMP HASH FUNCTION *)
Definition hash_purchaseId (n : nat) (addr : Address) : N :=
    Npos (countable.encode (n, addr)).
    
(* TEMP HASH FUNCTION *)
Definition hash_bid (id : N) (buyer_bit : bool) (nonce : N) : N :=
    Npos (countable.encode (id, buyer_bit, nonce)).

Definition buyer_request_purchase_action (chain : Chain) 
                                        (ctx : ContractCallContext) 
                                        (state : State)
                                        (_itemId : nat) 
                                        (notes : string)
                                        : result (State * list ActionBody) Error :=
  (* 检查是否为自调用 *)
  if required_no_self_call ctx then
    let _buyer := ctx_from ctx in
    let current_listings := listings state in
    (* 查找商品 *)
    match find_item _itemId current_listings with
    | Some requested_item =>
        (* 检查发送的金额是否与商品价格一致 *)
        if (item_value requested_item) =? ctx.(ctx_amount) then
          let _current_slot := chain.(current_slot) in
          let purchaseId := hash_purchaseId _current_slot _buyer in
          (* 检查购买 ID 是否已存在 *)
          if negb (purchase_exists purchaseId (purchases state)) then
            let purchase :=
              {|
                commit := 0;
                last_block := _current_slot;
                itemId := _itemId;
                seller_bit := false;
                notes := notes;
                purchase_state := requested;
                buyer := _buyer;
                pool := ctx.(ctx_amount);
                discarded_money := 0;
              |} in
            let updated_purchases := FMap.add purchaseId purchase (purchases state) in
            let updated_state := state <| purchases := updated_purchases |>
            in
            Ok (updated_state, [])
          else
            Err default_error (* 错误：购买 ID 已存在 *)
        else
          Err default_error (* 错误：发送金额与商品价格不符 *)
    | None =>
        Err default_error (* 错误：未找到对应的商品 *)
    end
  else
    Err default_error. (* 错误：自调用不被允许 *)


Definition buyer_abort_action (ctx : ContractCallContext) 
                              (state : State) 
                              (purchaseId : purchase_key_type)
  : result (State * list ActionBody) Error :=
  (* 检查发送的金额是否为零 *)
  if required_amount_zero ctx then
    let current_purchases := purchases state in
    (* 查找购买记录 *)
    match find_purchase purchaseId current_purchases with
    | Some purchase =>
        (* 检查购买状态是否为 requested *)
        if purchase_state_eq purchase.(purchase_state) requested then
          (* 检查调用者是否为买家 *)
          if ((ctx_from ctx) =? purchase.(buyer))%address then
            let updated_purchase := purchase <| purchase_state := failed |>
                                             <| pool := 0 |> in
            let updated_purchases := FMap.add purchaseId updated_purchase current_purchases in
            let updated_state := state <| purchases := updated_purchases |> in
            let actions := [act_transfer purchase.(buyer) purchase.(pool)] in
            Ok (updated_state, actions)
          else
            Err default_error (* 错误：调用者不是买家 *)
        else
          Err default_error (* 错误：购买状态不是 requested *)
    | None =>
        Err default_error (* 错误：未找到对应的购买记录 *)
    end
  else
    Err default_error (* 错误：发送的金额不是零 *)
.

Definition buyer_confirm_delivery_action (ctx : ContractCallContext) 
                                         (state : State) 
                                         (purchaseId : purchase_key_type)
  : result (State * list ActionBody) Error :=
  (* 检查发送的金额是否为零 *)
  if required_amount_zero ctx then
    let current_purchases := purchases state in
    (* 查找购买记录 *)
    match find_purchase purchaseId current_purchases with
    | Some purchase =>
        (* 检查购买状态是否为 delivered *)
        if purchase_state_eq purchase.(purchase_state) delivered then
          (* 检查调用者是否为买家 *)
          if ((ctx_from ctx) =? purchase.(buyer))%address then
            let updated_purchase := purchase <| purchase_state := completed |>
                                             <| pool := 0 |> in
            let updated_purchases := FMap.add purchaseId updated_purchase current_purchases in
            let updated_state := state <| purchases := updated_purchases |> in
            let actions := [act_transfer state.(seller) purchase.(pool)] in
            Ok (updated_state, actions)
          else
            Err default_error (* 错误：调用者不是买家 *)
        else
          Err default_error (* 错误：购买状态不是 delivered *)
    | None =>
        Err default_error (* 错误：未找到对应的购买记录 *)
    end
  else
    Err default_error (* 错误：发送的金额不是零 *)
.

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
                let updated_purchase := purchase <| purchase_state := dispute |>
                                                 <| commit := commitment |>
                                                 <| last_block := current_slot chain |>
                                                 <| pool := purchase.(pool) + item.(item_value) |> in
                let updated_purchases := FMap.add purchaseId updated_purchase current_purchases in
                let updated_state := state <| purchases := updated_purchases |> in
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
  end
.

Definition buyer_call_timeout_action (ctx : ContractCallContext) 
                                    (state : State) 
                                    (chain : Chain) 
                                    (purchaseId : purchase_key_type)
      : result (State * list ActionBody) Error :=
  (* 检查发送的金额是否为零 *)
  if required_amount_zero ctx then
    let current_purchases := purchases state in
    (* 查找购买记录 *)
    match find_purchase purchaseId current_purchases with
    | Some purchase =>
        (* 检查购买状态是否为 dispute 或 accepted *)
        if purchase_state_eq purchase.(purchase_state) dispute || purchase_state_eq purchase.(purchase_state) accepted then
          (* 检查调用者是否为买家 *)
          if ((ctx_from ctx) =? purchase.(buyer))%address then
            (* 检查是否超过超时 *)
            if (purchase.(last_block) + state.(timeout) <? chain.(current_slot))%nat then
              let updated_purchase := purchase <| purchase_state := failed |>
                                               <| pool := 0 |> in
              let updated_purchases := FMap.add purchaseId updated_purchase current_purchases in
              let updated_state := state <| purchases := updated_purchases |> in
              let actions := [act_transfer purchase.(buyer) purchase.(pool)] in
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
    Err default_error (* 错误：发送的金额不是零 *)
.

Definition buyer_open_commitment_action (ctx : ContractCallContext) 
                                        (state : State) 
                                        (purchaseId : purchase_key_type) 
                                        (buyer_bit : bool) 
                                        (nonce : N)
      : result (State * list ActionBody) Error :=
  (* 检查发送的金额是否为零 *)
  if required_amount_zero ctx then
    let current_purchases := purchases state in
    (* 查找购买记录 *)
    match find_purchase purchaseId current_purchases with
    | Some purchase =>
        (* 查找对应的商品 *)
        match find_item purchase.(itemId) (listings state) with
        | Some item =>
            (* 检查调用者是否为买家 *)
            if ((ctx_from ctx) =? purchase.(buyer))%address then
              (* 检查购买状态是否为 counter *)
              if purchase_state_eq purchase.(purchase_state) counter then
                (* 检查提交的哈希是否正确 *)
                if (hash_bid purchaseId buyer_bit nonce =? purchase.(commit))%N then
                  let to_send := purchase.(pool) - item.(item_value) in
                  let updated_purchase := purchase <| purchase_state := failed |>
                                                   <| pool := 0 |>
                                                   <| discarded_money := item.(item_value) |> in
                  let updated_purchases := FMap.add purchaseId updated_purchase current_purchases in
                  let target_transaction := if (Bool.eqb purchase.(seller_bit) buyer_bit) 
                                            then purchase.(buyer) 
                                            else state.(seller) in
                  let updated_state := state <| purchases := updated_purchases |> in
                  let actions := [act_transfer target_transaction to_send] in
                  Ok (updated_state, actions)
                else
                  Err default_error (* 错误：提交的哈希不正确 *)
              else
                Err default_error (* 错误：购买状态不是 counter *)
            else
              Err default_error (* 错误：调用者不是买家 *)
        | None =>
            Err default_error (* 错误：未找到对应的商品 *)
        end
    | None =>
        Err default_error (* 错误：未找到对应的购买记录 *)
    end
  else
    Err default_error (* 错误：发送的金额不是零 *)
.

Definition seller_call_timeout_action (ctx : ContractCallContext) 
                                      (state : State) 
                                      (chain : Chain) 
                                      (purchaseId : purchase_key_type)
      : result (State * list ActionBody) Error :=
  (* 检查发送的金额是否为零 *)
  if required_amount_zero ctx then
    let current_purchases := purchases state in
    (* 查找购买记录 *)
    match find_purchase purchaseId current_purchases with
    | Some purchase =>
        (* 检查购买状态是否为 delivered 或 counter *)
        if purchase_state_eq purchase.(purchase_state) delivered 
           || purchase_state_eq purchase.(purchase_state) counter then
          (* 检查调用者是否为卖家 *)
          if ((ctx_from ctx) =? state.(seller))%address then
            (* 检查是否超过超时 *)
            if (purchase.(last_block) + state.(timeout) <? chain.(current_slot))%nat then
              let updated_purchase := purchase <| purchase_state := completed |>
                                               <| pool := 0 |> in
              let updated_purchases := FMap.add purchaseId updated_purchase current_purchases in
              let updated_state := state <| purchases := updated_purchases |> in
              let actions := [act_transfer state.(seller) purchase.(pool)] in
              Ok (updated_state, actions)
            else
              Err default_error (* 错误：尚未到达超时区块 *)
          else
            Err default_error (* 错误：调用者不是卖家 *)
        else
          Err default_error (* 错误：购买状态不是 delivered 或 counter *)
    | None =>
        Err default_error (* 错误：未找到对应的购买记录 *)
    end
  else
    Err default_error (* 错误：发送的金额不是零 *)
.

Definition seller_reject_contract_action (ctx : ContractCallContext) 
                                        (state : State) 
                                        (purchaseId : purchase_key_type)
      : result (State * list ActionBody) Error :=
  (* 检查发送的金额是否为零 *)
  if required_amount_zero ctx then
    let current_purchases := purchases state in
    (* 查找购买记录 *)
    match find_purchase purchaseId current_purchases with
    | Some purchase =>
        (* 检查购买状态是否为 requested *)
        if purchase_state_eq purchase.(purchase_state) requested then
          (* 检查调用者是否为卖家 *)
          if ((ctx_from ctx) =? state.(seller))%address then
            let updated_purchase := purchase <| purchase_state := rejected |>
                                             <| pool := 0 |> in
            let updated_purchases := FMap.add purchaseId updated_purchase current_purchases in
            let updated_state := state <| purchases := updated_purchases |> in
            let actions := [act_transfer purchase.(buyer) purchase.(pool)] in
            Ok (updated_state, actions)
          else
            Err default_error (* 错误：调用者不是卖家 *)
        else
          Err default_error (* 错误：购买状态不是 requested *)
    | None =>
        Err default_error (* 错误：未找到对应的购买记录 *)
    end
  else
    Err default_error (* 错误：发送的金额不是零 *)
.

Definition seller_accept_contract_action (ctx : ContractCallContext) 
                                        (state : State) 
                                        (chain : Chain) 
                                        (purchaseId : purchase_key_type)
      : result (State * list ActionBody) Error :=
  (* 检查发送的金额是否为零 *)
  if required_amount_zero ctx then
    let current_purchases := purchases state in
    (* 查找购买记录 *)
    match find_purchase purchaseId current_purchases with
    | Some purchase =>
        (* 检查购买状态是否为 requested *)
        if purchase_state_eq purchase.(purchase_state) requested then
          (* 检查调用者是否为卖家 *)
          if ((ctx_from ctx) =? state.(seller))%address then
            let updated_purchase := purchase <| purchase_state := accepted |>
                                             <| last_block := chain.(current_slot) |> in
            let updated_purchases := FMap.add purchaseId updated_purchase current_purchases in
            let updated_state := state <| purchases := updated_purchases |> in
            Ok (updated_state, [])
          else
            Err default_error (* 错误：调用者不是卖家 *)
        else
          Err default_error (* 错误：购买状态不是 requested *)
    | None =>
        Err default_error (* 错误：未找到对应的购买记录 *)
    end
  else
    Err default_error (* 错误：发送的金额不是零 *)
.

Definition seller_item_was_delivered_action (ctx : ContractCallContext) 
                                            (state : State) 
                                            (chain : Chain) 
                                            (purchaseId : purchase_key_type)
      : result (State * list ActionBody) Error :=
  (* 检查发送的金额是否为零 *)
  if required_amount_zero ctx then
    let current_purchases := purchases state in
    (* 查找购买记录 *)
    match find_purchase purchaseId current_purchases with
    | Some purchase =>
        (* 检查购买状态是否为 accepted *)
        if purchase_state_eq purchase.(purchase_state) accepted then
          (* 检查调用者是否为卖家 *)
          if ((ctx_from ctx) =? state.(seller))%address then
            let updated_purchase := purchase <| purchase_state := delivered |>
                                             <| last_block := chain.(current_slot) |> in
            let updated_purchases := FMap.add purchaseId updated_purchase current_purchases in
            let updated_state := state <| purchases := updated_purchases |> in
            Ok (updated_state, [])
          else
            Err default_error (* 错误：调用者不是卖家 *)
        else
          Err default_error (* 错误：购买状态不是 accepted *)
    | None =>
        Err default_error (* 错误：未找到对应的购买记录 *)
    end
  else
    Err default_error (* 错误：发送的金额不是零 *)
.

Definition seller_forfeit_dispute_action (ctx : ContractCallContext) 
                                        (state : State) 
                                        (purchaseId : purchase_key_type)
      : result (State * list ActionBody) Error :=
  (* 检查发送的金额是否为零 *)
  if required_amount_zero ctx then
    let current_purchases := purchases state in
    (* 查找购买记录 *)
    match find_purchase purchaseId current_purchases with
    | Some purchase =>
        (* 检查购买状态是否为 dispute *)
        if purchase_state_eq purchase.(purchase_state) dispute then
          (* 检查调用者是否为卖家 *)
          if ((ctx_from ctx) =? state.(seller))%address then
            let updated_purchase := purchase <| purchase_state := failed |>
                                             <| pool := 0 |> in
            let updated_purchases := FMap.add purchaseId updated_purchase current_purchases in
            let updated_state := state <| purchases := updated_purchases |> in
            let actions := [act_transfer purchase.(buyer) purchase.(pool)] in
            Ok (updated_state, actions)
          else
            Err default_error (* 错误：调用者不是卖家 *)
        else
          Err default_error (* 错误：购买状态不是 dispute *)
    | None =>
        Err default_error (* 错误：未找到对应的购买记录 *)
    end
  else
    Err default_error (* 错误：发送的金额不是零 *)
.

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
      (* 检查购买状态是否为 dispute *)
      if purchase_state_eq purchase.(purchase_state) dispute then
        (* 检查调用者是否为卖家 *)
        if ((ctx_from ctx) =? state.(seller))%address then
          let money_sent := ctx.(ctx_amount) in
          (* 查找对应的商品 *)
          match find_item purchase.(itemId) (listings state) with
          | Some disputed_item =>
              (* 检查发送的金额是否与商品价值一致 *)
              if (money_sent =? disputed_item.(item_value)) then
                let updated_purchase := purchase <| purchase_state := counter |>
                                                 <| last_block := chain.(current_slot) |>
                                                 <| seller_bit := random_bit |>
                                                 <| pool := purchase.(pool) + money_sent |> in
                let updated_purchases := FMap.add purchaseId updated_purchase current_purchases in
                let target_transaction := if Bool.eqb purchase.(seller_bit) random_bit 
                                          then purchase.(buyer) 
                                          else state.(seller) in
                let updated_state := state <| purchases := updated_purchases |> in
                let actions := [act_transfer target_transaction (purchase.(pool) + money_sent)] in
                Ok (updated_state, actions)
              else
                Err default_error (* 错误：发送的金额与商品价值不符 *)
          | None =>
              Err default_error (* 错误：未找到对应的商品 *)
          end
        else
          Err default_error (* 错误：调用者不是卖家 *)
      else
        Err default_error (* 错误：购买状态不是 dispute *)
  | None =>
      Err default_error (* 错误：未找到对应的购买记录 *)
  end
.

(* 它确保所有与该 itemId 相关的购买状态都已完成、被拒绝或失败。 *)

Definition no_active_purchase_for_itemId state _itemId :=
  let all_key_purchases := FMap.elements state.(purchases) in
  let key_purchases_for_itemId := filter (fun '(_, purchase) => (purchase.(itemId) =? _itemId)%nat)
                              all_key_purchases in
  forallb
  (fun '(_, purchase) =>
    match purchase.(purchase_state) with
    | completed | rejected | failed => true
    | _ => false
    end)
  key_purchases_for_itemId.

Definition seller_update_listings_action (ctx : ContractCallContext) 
                                         (state : State) 
                                         (itemId : nat) 
                                         (descr : string) 
                                         (value : Amount)
  : result (State * list ActionBody) Error :=
  (* 检查发送的金额是否为零 *)
  if required_amount_zero ctx then
    (* 检查 value 是否非负 *)
    if (0 <=? value) then
      (* 检查调用者是否为卖家 *)
      if (ctx.(ctx_from) =? state.(seller))%address then
        (* 检查是否没有活跃的购买 *)
        if no_active_purchase_for_itemId state itemId then
          let current_listings := listings state in
          let new_item := {|
            item_value := value;
            item_description := descr
          |} in 
          let updated_listings := FMap.add itemId new_item current_listings in
          let updated_state := state <| listings := updated_listings |> in
          Ok (updated_state, [])
        else
          Err default_error (* 错误：存在活跃的购买 *)
      else
        Err default_error (* 错误：调用者不是卖家 *)
    else
      Err default_error (* 错误：value 不合法 *)
  else
    Err default_error (* 错误：发送的金额不是零 *)
.

Definition receive (chain : Chain) 
                   (ctx : ContractCallContext)
                   (state : State) 
                   (msg : option Msg)
                   : result (State * list ActionBody) Error :=
  match msg with
  | Some msg_content =>
      match msg_content with
      | buyer_request_purchase itemId notes             => buyer_request_purchase_action chain ctx state itemId notes
      | buyer_abort id                                  => buyer_abort_action ctx state id
      | buyer_confirm_delivery id                       => buyer_confirm_delivery_action ctx state id
      | buyer_dispute_delivery id commitment            => buyer_dispute_delivery_action ctx state chain id commitment
      | buyer_call_timeout id                           => buyer_call_timeout_action ctx state chain id
      | buyer_open_commitment id buyer_bit nonce        => buyer_open_commitment_action ctx state id buyer_bit nonce
      | seller_call_timeout id                          => seller_call_timeout_action ctx state chain id
      | seller_reject_contract id                       => seller_reject_contract_action ctx state id
      | seller_accept_contract id                       => seller_accept_contract_action ctx state chain id
      | seller_item_was_delivered id                    => seller_item_was_delivered_action ctx state chain id
      | seller_forfeit_dispute id                       => seller_forfeit_dispute_action ctx state id
      | seller_counter_dispute id random_bit            => seller_counter_dispute_action ctx state chain id random_bit
      | seller_update_listings itemId description value => seller_update_listings_action ctx state itemId description value
      end
  | None =>
      Err default_error (* 错误：未接收到消息 *)
  end
.

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
          timeout := timeout;
        |}
      else
        Err default_error (* 错误：发送的金额不是零 *)
    else
      Err default_error (* 错误：timeout 不合法 *)
  else
    Err default_error (* 错误：自调用不被允许 *)
.





