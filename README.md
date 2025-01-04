# Coq Liquidity Verification

### 研究生项目：Coq 流动性验证代码

#### 环境要求
- **操作系统**: Windows 11
- **Coq 版本**: 8.16.1


## Note
当前版本代码位于 **`no_time` 分支**，请切换至该分支以获取最新的代码更新和功能实现。



---

## **Concert 框架代码**

### 核心框架文件
以下文件是验证项目的基础组件：
- `theories/OptionMonad.v`
- `theories/LibTactics.v`
- `theories/Automation.v`
- `theories/Blockchain.v`
- `theories/BuildUtils.v`
- `theories/BoundedN.v`
- `theories/Circulation.v`
- `theories/Containers.v`
- `theories/ContractCommon.v`
- `theories/InterContractCommunication.v`
- `theories/ContractMonads.v`
- `theories/Extras.v`
- `theories/Finite.v`
- `theories/Monads.v`
- `theories/ResultMonad.v`
- `theories/Serializable.v`
- **`theories/ChainedList.v`**

### 代码改动
在 `theories/ChainedList.v` 中，新增了 **`prefixTrace`** 数据结构及其相关操作，同时建立了 `ChainedList` 与 `prefixTrace` 之间的双向转换关系，并证明了其转换的合法性。该定义主要是为了辅助 **流动性等价性** 的证明。

---

## **工作代码**

### 核心代码文件：`theories/Strat.v`
该文件包含了 **动作执行模型**、**策略模型** 的定义，以及 **基本流动性** 和 **策略流动性** 的性质定义、等价性证明等。同时提供了自动化证明工具和若干辅助引理。

#### 主要内容

- **`concert_exec_base`**: Concert 框架中自带的动作执行函数。
- **`exec_base_proof`**: 对这些函数的正确性进行验证，包括多个辅助证明引理。
- **`Monotonicity`**: 证明流动性的单调性性质。
- **`normal`**: 包含案例分析中常用的辅助引理。
- **`transition_trace`**: 定义了迁移轨迹、可达性以及 **基本流动性** (`base_liquidity`)。

#### 核心定义

- **基本流动性 (`base_liquidity`)**: 合约在策略交互下能否达到目标状态的基本定义。
- **完备策略 (`is_complete_strategy`)**: 能够驱动系统达到目标状态的策略。
- **空策略 (`is_empty_strat`)**: 不执行任何操作的策略。
- **单步策略驱动 (`stratDrive`)** 与 **多步策略驱动 (`multiStratDrive`)**。
- **有限策略 (`strat_finite`)**: 定义策略在有限步内终止。
- **用户与环境交错执行 (`interleavedExecution`)**: 定义用户与环境策略的交互。
- **用户环境互归纳定义**: 
  - `UserLiquidatesNSteps`: 用户在有限步内达成流动性。
  - `envProgress_Mutual`: 环境策略推动系统状态变化。
- **合法策略系统 (`wellDefinedSystem`)**: 确保用户和环境策略的合法性及终止性。
- **策略流动性 (`strat_liquidity`)**: 定义在策略驱动下的流动性。

#### 关键引理与性质

- **`strat_liquid_Mono_usr_unchanging`**: 证明在用户策略不变时，策略流动性的单调性。
- **`SL_equiv_BL_with_empty_env_and_complete_user`**: 证明策略流动性 (`strat_liquidity`) 与基本流动性 (`base_liquidity`) 的等价性，该引理包含两个辅助引理：
  - **`SL_implies_BL_with_empty_env_and_complete_user`**: 在用户策略完备且环境策略为空的情况下，策略流动性成立推出基本流动性成立。
  - **`BL_implies_SL_with_empty_env_and_complete_user`**: 在相同条件下，基本流动性成立推出策略流动性成立。

---

## **案例分析**

### 1. **托管合约 (`examples/instrumentEscrow/`)**
#### InstrumentEscrow.v
该文件形式化建模了托管合约，并证明了其流动性性质。
- **`escrow_satisfy_base_liqudity`**: 证明托管合约满足基本流动性。
- **`escrow_satisfy_strat_liquidity_with_good_buyer_bad_seller`**: 证明在托管合约中，诚实买家满足策略流动性。
- **`escrow_satisfy_strat_liquidity_with_good_seller_bad_buyer`**: 证明在托管合约中，诚实卖家满足策略流动性。
#### InstrumentEscrow.sol
与`InstrumentEscrow.v`中所定义合约具有相同逻辑的Solidity合约，可运行。

### 2. **蜜罐合约 (`examples/honeypots/`)**
#### Honeypots.v
该文件形式化建模了蜜罐合约，并验证了其流动性性质。
- **`honeypot_satisfy_base_liquidity`**: 证明蜜罐合约满足基本流动性。
- 不满足策略流动性
#### Gift_1_ETH.sol
`Honeypots.v` 中的合约由Gift_1_ETH建模而来
原始合约的部署地址：`contract address: 0xd8993F49F372BB014fB088eaBec95cfDC795CBF6`

---

通过以上代码与模型，项目为 Coq 框架下智能合约的 **流动性验证** 提供了系统化的分析和证明工具。
