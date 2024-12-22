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
From Coq Require Import List.
From Coq Require Import Bool.
From Coq Require Import ZArith.
From Coq Require Import Arith.
From Coq Require Import String.
Require ResultMonad.
Import ListNotations.
Require Import Lia.
Import RecordSetNotations.
Require Import Blockchain.
Require Import Containers.
Require Import Serializable.
Require Import PArith.
Require Import ResultMonad.
From Coq Require Import ZArith.
From Coq Require Import List.
From Coq Require Import Permutation.
Import ListNotations.
Section Escrow.

  Context {BaseTypes : ChainBase}.
  Set Primitive Projections.
  Set Nonrecursive Elimination Schemes.
  Context {AddrSize : N}.

  Inductive EscrowState :=
  | AwaitingPayment          
  | AwaitingRefund           
  | Dispute                  
  | Finalized.              

  (* Escrow contract state *)
  Record State := build_state {
    buyer : Address;        
    seller : Address;       
    mediator : Address;     
    balance : Amount;        
    escrowState : EscrowState; 
    timeout : nat            
  }.

  (* Setup for the contract *)
  Record Setup := build_setup {
    buyer_addr : Address;
    seller_addr : Address;   
    mediator_addr : Address; 
    timeout_blocks : nat    
  }.

  Global Instance state_settable : Settable _ :=
    settable! build_state <buyer; seller; mediator; balance; escrowState; timeout>.
  
  Inductive Msg :=
  | BuyerPayToSeller 
  | BuyerRequestRefund
  | SellerRefundToBuyer 
  | ThridpartyResolvDispute 
  | BuyerRequestArbitration         
  | ForceFinalize.   

  (* Define EscrowState comparison function *)
  Definition eqb_EscrowState (s1 s2 : EscrowState) : bool :=
    match s1, s2 with
    | AwaitingPayment, AwaitingPayment => true
    | AwaitingRefund, AwaitingRefund => true
    | Dispute, Dispute => true
    (* | Resolved, Resolved => true *)
    | Finalized, Finalized => true
    | _, _ => false
    end.

  Section Serialization.

    Global Instance Msg_serializable : Serializable Msg :=
      Derive Serializable Msg_rect<BuyerPayToSeller,BuyerRequestRefund, SellerRefundToBuyer, ThridpartyResolvDispute, BuyerRequestArbitration, ForceFinalize>.

    Global Instance Setup_serializable : Serializable Setup :=
      Derive Serializable Setup_rect<build_setup>.

    Global Instance EscrowState_serializable : Serializable EscrowState :=
      Derive Serializable EscrowState_rect<AwaitingPayment, AwaitingRefund, Dispute,  Finalized>.

    Global Instance State_serializable : Serializable State :=
      Derive Serializable State_rect<build_state>.

  
  End Serialization.

  Definition serializeMsg msg := (@serialize Msg _) msg.
  Definition serializeState state := (@serialize State _) state.
  Definition serializeSetup setup := (@serialize Setup _) setup.

  Global Coercion serializeMsg : Msg >-> SerializedValue.
  Global Coercion serializeState : State >-> SerializedValue.
  Global Coercion serializeSetup : Setup >-> SerializedValue.

  Definition Error : Type := nat.
  Definition default_error: Error := 1%nat.
  Local Open Scope Z.

  (* Check if the address is not a contract *)
  Definition address_not_contract `{ChainBase} (x : Address) : bool :=
    negb (address_is_contract x).

  (* Check if B can claim funds due to timeout *)
  Definition is_timeout (chain : Chain) (state : State) : bool :=
    (state.(timeout) <=? chain.(current_slot))%nat.

  Definition init (chain : Chain) (ctx : ContractCallContext) (setup : Setup) : result State Error :=
    if ((ctx.(ctx_amount) <? 10)%Z || (setup.(timeout_blocks) <? 7)%nat
     || address_is_contract ctx.(ctx_from) ||  address_is_contract setup.(seller_addr) ||address_is_contract setup.(mediator_addr)) || address_is_contract setup.(buyer_addr)
    then Err default_error
    else Ok (build_state
               setup.(buyer_addr)   
               setup.(seller_addr)  
               setup.(mediator_addr) 
               ctx.(ctx_amount)     
               AwaitingPayment      
               (chain.(current_slot) + setup.(timeout_blocks))
            ).

  (* A pays B *)
  Definition buyer_pay_to_seller (ctx : ContractCallContext) (state : State) : result (State * list ActionBody) Error :=
    if (ctx.(ctx_from) =? state.(buyer))%address && (eqb_EscrowState state.(escrowState) AwaitingPayment) then
      let new_state := state <| escrowState := Finalized |>
                               <| balance := 0 |>
      in let actions := [act_transfer state.(seller) state.(balance)] (* Transfer 10b to B *)
      in Ok (new_state,actions) (* Transition to Finalized state *)
    else Err default_error.

  (* A request refund *)
  Definition buyer_request_refund (ctx : ContractCallContext) (state : State) : result (State * list ActionBody) Error :=
  if (ctx.(ctx_from) =? state.(buyer))%address && (eqb_EscrowState state.(escrowState) AwaitingPayment || eqb_EscrowState state.(escrowState) AwaitingRefund ) then
    let new_state := state <| escrowState := AwaitingRefund |> in
    Ok (new_state, [])
  else Err default_error.

  (* B refunds to A *)
  Definition seller_refund_to_buyer (ctx : ContractCallContext) (state : State) : result (State * list ActionBody) Error :=
    if (ctx.(ctx_from) =? state.(seller))%address && (eqb_EscrowState state.(escrowState) AwaitingRefund || eqb_EscrowState state.(escrowState) Dispute) then
      let new_state := state <| escrowState := Finalized |>
                               <| balance := 0 |>
      in let actions := [act_transfer state.(buyer) state.(balance)] (* Refund 10b to A *)
      in Ok (new_state,actions) (* Transition to Finalized state *)
    else Err default_error.


  (* Any user forces finalization after timeout *)
  Definition force_finalize (chain : Chain) (ctx : ContractCallContext) (state : State) : result (State * list ActionBody) Error :=
    if (is_timeout chain state && (eqb_EscrowState state.(escrowState) AwaitingPayment)) then
      let new_state := state <| escrowState := Finalized |>
                               <| balance := 0 |>
      in let actions := [act_transfer state.(seller) state.(balance)] (* Transfer funds to B *)
      in Ok (new_state,actions) (* Transition to Finalized state *)
    else Err default_error.

  (* A starts a dispute *)
  Definition buyer_request_arbitration (ctx : ContractCallContext) (state : State) : result (State * list ActionBody) Error :=
    if (ctx.(ctx_from) =? state.(buyer))%address && (eqb_EscrowState state.(escrowState) AwaitingRefund) then
      let new_state := state <| escrowState := Dispute |>
      in Ok (new_state, [])
    else Err default_error.

  (* Mediator M resolves the dispute *)
  Definition mediator_resolve_dispute_to_buyer (ctx : ContractCallContext) (state : State) : result (State * list ActionBody) Error :=
    if (ctx.(ctx_from) =? state.(mediator))%address && (eqb_EscrowState state.(escrowState) Dispute)%bool then
      let mediator_fee := state.(balance)/20 
      in let amount_to_buyer := state.(balance) - mediator_fee 
      in let new_state := state <| escrowState := Finalized  |>
                                 <| balance := 0 |>
      in let actions := [act_transfer state.(mediator) mediator_fee;
                         act_transfer state.(buyer) amount_to_buyer] 
      in Ok (new_state,actions) 
    else Err default_error.

    (* Mediator M resolves the dispute *)
  Definition mediator_resolve_dispute_to_seller (ctx : ContractCallContext) (state : State) : result (State * list ActionBody) Error :=
    if (ctx.(ctx_from) =? state.(mediator))%address && (eqb_EscrowState state.(escrowState) Dispute)%bool then
      let mediator_fee := state.(balance)/20 
      in let amount_to_seller := state.(balance) - mediator_fee 
      in let new_state := state <| escrowState := Finalized  |>
                                 <| balance := 0 |>
      in let actions := [act_transfer state.(mediator) mediator_fee;
                         act_transfer state.(seller) amount_to_seller] 
      in Ok (new_state,actions) 
    else Err default_error.

  (* Contract receive function *)
  Definition receive (chain : Chain) (ctx : ContractCallContext) (state : State) (msg : option Msg) : result (State * list ActionBody) Error :=
    if (negb (address_is_contract ctx.(ctx_from)) && (ctx.(ctx_amount) =? 0)) then
      match msg with
      | Some BuyerPayToSeller => buyer_pay_to_seller ctx state
      | Some BuyerRequestRefund => buyer_request_refund ctx state
      | Some SellerRefundToBuyer => seller_refund_to_buyer ctx state
      | Some BuyerRequestArbitration => buyer_request_arbitration ctx state
      | Some ThridpartyResolvDispute => mediator_resolve_dispute_to_buyer ctx state
      | Some ForceFinalize => force_finalize chain ctx state 
      | None => Err default_error
      end
      else  Err default_error.

    (* Define the contract *)
  Definition contract : Contract Setup Msg State Error :=
    build_contract init receive.
     
  Class EqDecision (A : Type) := eq_dec : forall x y : A, { x = y } + { x <> y }.

  Global Instance eq_dec_Msg : EqDecision Msg.
  Proof.
    intros x y.
    decide equality.
  Defined.

  Definition eqb_Msg (m1 m2 : Msg) : bool :=
    if eq_dec m1 m2 then true else false.

  Definition valid_msgs : list Msg := 
      [BuyerPayToSeller; BuyerRequestRefund; SellerRefundToBuyer; 
      ThridpartyResolvDispute; BuyerRequestArbitration; ForceFinalize].

  Definition is_escrow_msg (msg : SerializedValue) : bool :=
  match @deserialize Msg _ msg with
  | Some m => List.existsb (eqb_Msg m) valid_msgs
  | None => false
  end.

  Definition validate_escrow_action_msg (act : Action) : bool :=
    match act.(act_body) with
    | act_call _ _ msg => is_escrow_msg msg
    | _ => false
    end.
    
  Definition ForceFinalize_act caddr (any_user:Address) : Action :=
    build_act any_user any_user (act_call caddr 0 ForceFinalize).
  
  Definition BuyerPayToSeller_Act cstate caddr: Action :=
    build_act (buyer cstate) (buyer cstate) (act_call caddr 0 BuyerPayToSeller).

  Definition BuyerRequestRefund_Act cstate caddr: Action :=
    build_act (buyer cstate) (buyer cstate) (act_call caddr 0 BuyerRequestRefund).

  Definition SellerRefundToBuyer_Act cstate caddr: Action :=
    build_act (seller cstate) (seller cstate) (act_call caddr 0 SellerRefundToBuyer).

  Definition BuyerRequestArbitration_Act cstate caddr: Action :=
    build_act (buyer cstate) (buyer cstate) (act_call caddr 0 BuyerRequestArbitration).

  Definition ThridpartyResolvDispute_Act cstate caddr: Action :=
    build_act (mediator cstate) (mediator cstate) (act_call caddr 0 ThridpartyResolvDispute).

End Escrow.

Section Theories.



End Theories.

