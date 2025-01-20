// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract InstrumentEscrow {
    // 定义 Escrow 状态阶段
    enum EscrowPhase {
        AWAITING_SHIPMENT,
        AWAITING_ACCEPTANCE,
        COMPLETED,
        DISPUTED
    }

    // 合约的状态结构
    struct State {
        address buyer;
        address seller;
        uint256 depositAmount;
        bool itemShipped;
        bool itemAccepted;
        address arbitrator;
        EscrowPhase currentPhase;
        uint256 balance;
    }

    // 初始化时的设置结构
    struct Setup {
        address setup_seller;
        address setup_arbitrator;
    }

    // 合约状态
    State public state;

    // 错误类型
    uint public constant default_error = 1;

    // 事件声明
    event ItemShipped();
    event ItemAccepted();
    event ItemRejected();
    event Arbitration(address winner, uint256 amount);

    // 合约构造函数
    constructor(address _seller, address _arbitrator) payable {
        require(msg.value > 0, "Deposit must be greater than 0");
        state.buyer = msg.sender;
        state.seller = _seller;
        state.depositAmount = msg.value;
        state.arbitrator = _arbitrator;
        state.currentPhase = EscrowPhase.AWAITING_SHIPMENT;
        state.balance = msg.value;
    }

    // 检查合约阶段
    modifier requirePhase(EscrowPhase ph) {
        require(state.currentPhase == ph, "Incorrect phase");
        _;
    }

    // 检查调用者是买家
    modifier onlyBuyer() {
        require(msg.sender == state.buyer, "Not the buyer");
        _;
    }

    // 检查调用者是卖家
    modifier onlySeller() {
        require(msg.sender == state.seller, "Not the seller");
        _;
    }

    // 检查调用者是仲裁人
    modifier onlyArbitrator() {
        require(msg.sender == state.arbitrator, "Not the arbitrator");
        _;
    }

    // 1. 卖家标记已发货
    function markAsShipped() public onlySeller requirePhase(EscrowPhase.AWAITING_SHIPMENT) {
        state.itemShipped = true;
        state.currentPhase = EscrowPhase.AWAITING_ACCEPTANCE;
        emit ItemShipped();
    }

    // 2. 买家验收通过
    function acceptItem() public onlyBuyer requirePhase(EscrowPhase.AWAITING_ACCEPTANCE) {
        state.itemAccepted = true;
        state.currentPhase = EscrowPhase.COMPLETED;
        uint256 amountToSeller = state.balance;
        state.balance = 0;
        payable(state.seller).transfer(amountToSeller);
        emit ItemAccepted();
    }

    // 3. 买家拒绝商品
    function rejectItem() public onlyBuyer requirePhase(EscrowPhase.AWAITING_SHIPMENT) requirePhase(EscrowPhase.AWAITING_ACCEPTANCE) {
        state.currentPhase = EscrowPhase.DISPUTED;
        emit ItemRejected();
    }

    // 4. 仲裁处理
    function arbitrate(bool buyerWins) public onlyArbitrator requirePhase(EscrowPhase.DISPUTED) {
        address winner = buyerWins ? state.buyer : state.seller;
        uint256 amountToWinner = state.balance;
        state.balance = 0;
        payable(winner).transfer(amountToWinner);
        state.currentPhase = EscrowPhase.COMPLETED;
        emit Arbitration(winner, amountToWinner);
    }

}
