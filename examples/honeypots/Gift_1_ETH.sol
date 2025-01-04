// contract address: 0xd8993F49F372BB014fB088eaBec95cfDC795CBF6

// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract Gift_1_ETH {
    bool public passHasBeenSet = false;
    bytes32 public hashPass;

    // 1. 获取密码哈希
    function GetHash(bytes memory pass) public pure returns (bytes32) {
        return keccak256(pass);
    }

    // 2. 设置密码哈希（需要至少发送 1 ETH）
    function SetPass(bytes32 hash) public payable {
        require(!passHasBeenSet, "Password has already been set");
        require(msg.value >= 1 ether, "At least 1 ETH required");

        hashPass = hash;
        passHasBeenSet = true;
    }

    // 3. 获取礼物（如果密码正确，转账所有ETH）
    function GetGift(bytes memory pass) public returns (bytes32) {
        require(hashPass != 0, "Password not set yet");
        if (hashPass == keccak256(pass)) {
            uint256 amount = address(this).balance;
            payable(msg.sender).transfer(amount);
        }
        return keccak256(pass);
    }

    // 4. 验证密码是否已设置
    function PassHasBeenSet(bytes32 hash) public {
        if (hash == hashPass) {
            passHasBeenSet = true;
        }
    }

    // 5. 合约的余额（查询合约的余额）
    function contractBalance() public view returns (uint256) {
        return address(this).balance;
    }
}
