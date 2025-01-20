# Coq 流动性验证项目

### 研究生项目：Coq 流动性验证代码

---

## 环境要求
- **操作系统**: Windows 11
- **Coq 版本**: 8.16.1 或 8.16.0

---

## 使用说明

1. **安装 Cygwin 和 Coq**  
   - 请确保已安装 Cygwin，并在其环境中安装 Coq，版本需为 8.16.1 或 8.16.0。
   - 配置 Cygwin，使其能够正常执行 Coq 相关命令。

2. **编译项目**  
   - 打开 Cygwin，并切换到包含项目代码的目录。
   - 执行以下命令以生成 `CoqMakefile` 文件：
     ```bash
     coq_makefile -f _CoqProject -o CoqMakefile
     ```
   - 使用 `make` 命令完成项目编译：
     ```bash
     make
     ```

3. **代码分支**  
   - 确保切换到最新的 **`main` 分支** 以获取最新代码和功能。

---

## 项目模块

### 1. ConCert 框架
以下文件为 ConCert 框架的源代码：
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
- `theories/ChainedList.v`

> **注意**: 在 `ChainedList.v` 文件中新增了定义 `prefixTrace`，该定义在等价性证明中会被使用。

---

### 2. 模型基础
- **文件**: `theories/ModelBase.v`  
  本文件基于 ConCert 框架，定义了执行层的动作评估函数，并证明了一些用于后续模型验证的引理。

---

### 3. 流动性验证模块

#### 3.1 StratModel.v
包含以下内容：
- **基本流动性** (`base_liquidity`): 定义合约在策略交互下是否能达到目标状态。
- **完备策略** (`is_complete_strategy`): 可推动系统达到目标状态的策略。
- **空策略** (`is_empty_strat`): 不执行任何操作的策略。
- **单步策略驱动** (`stratDrive`) 与 **多步策略驱动** (`multiStratDrive`)。
- **用户与环境交错执行** (`interleavedExecution`): 定义用户策略和环境策略的交互过程。
- **用户与环境的互归纳定义**:
  - `UserLiquidatesNSteps`: 用户在有限步内达成流动性。
  - `envProgress_Mutual`: 环境策略推动系统状态变化。
- **策略流动性** (`strat_liquidity`): 描述策略驱动下的流动性特性。

#### 3.2 Monotonicity.v
证明了在一定条件下，策略流动性具备单调性。

#### 3.3 Equivalence.v
证明了在特定条件下，策略流动性和基本流动性之间的等价性。

#### 3.4 示例代码
- **蜜罐合约** (`examples/honeypots/Honeypots.v`):  
  包含对典型蜜罐合约的建模及其基本流动性性质的证明。
- **托管合约** (`examples/instrumentEscrow/InstrumentEscrow.v`):  
  自定义托管合约的建模与基本流动性证明。文件还包括在特定用户-环境策略下的策略流动性证明及部分合约正确性验证。
- **以太坊游戏合约** (`examples/lucky7game/EtherGame.v`):  
  包含经典以太坊游戏合约的建模与基本流动性证明，以及在给定用户-环境策略下的策略流动性验证。

---

### 4. 时间扩展模块

#### 4.1 TimeStratModel.v
- 在 `transition` 函数中增加了时间处理能力。
- 新增 `timeDrive` 表示一次时间相关的动作迁移。
- 更新了以下定义以加入时间处理：
  - `interleavedExecution`
  - `UserLiquidatesNSteps`
  - `envProgress_Mutual`

#### 4.2 示例代码
- **单项支付渠道合约** (`examples/uniDirectionalPayChannel/UniDirectionalPayChannel.v`):  
  包含单项支付渠道合约的建模及流动性性质证明。文件还包括时间相关动作的用户-环境策略流动性证明。

---

