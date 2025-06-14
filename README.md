# Technical Development in the Coq Proof Assistant  
**For the Paper:**  
*Proving Strategy-aware Liquidity for Smart Contracts*  
**Authors:** Sensen Chen, Ximeng Li, Qianying Zhang, Guohui Wang, Zhiping Shi, Yong Guan  

---

## 🖥️ System Requirements

- **Operating System:** Preferably Windows 11  
- **Coq Version:** 8.16.1 or 8.16.0  

---

## ⚙️ Setup and Compilation Instructions

### 1. Install Cygwin and Coq

- Install **Coq** (version 8.16.1 or 8.16.0).
- Set up **Cygwin** so that the `make` and `coqc` commands are available.

### 2. Compile the Code

1. Open the **Cygwin terminal**.
2. Navigate (`cd`) to the **top-level directory** of the Coq project.
3. Generate the Makefile:

   ```bash
   coq_makefile -f _CoqProject -o Makefile
   ```

4. Compile the code using:

   ```bash
   make
   ```

---

## 📂 Main Coq Files in This Development

### 1.  ConCert Framework Dependencies  
*From:* [ConCert GitHub Repository](https://github.com/AU-COBRA/ConCert)

These files are located in the `theories/` directory:

- `LibTactics.v`
- `Automation.v`
- `Blockchain.v`
- `BuildUtils.v`
- `BoundedN.v`
- `Containers.v`
- `ContractCommon.v`
- `Extras.v`
- `Finite.v`
- `Monads.v`
- `ResultMonad.v`
- `Serializable.v`
- `ChainedList.v`  
  > 🔹 Includes an added definition: `prefixTrace`, used to connect strategy-aware liquidity and basic liquidity.

---

### 2.  Extension of ConCert’s Execution Model

- `ModelBase.v`  
  > Defines `evaluate_action`, the computational evaluation of a list of actions.  
  > Includes theoretical results about this execution model.

---

### 3.  Liquidity Properties, Meta-Theory, and Contract Verification

#### 3.1 `StratModel.v`

Defines key properties and predicates:

- `strategy_aware_liquidity` — the formal property definition.
- `basic_liquidity` — basic liquidity formalization.
- `is_complete_strategy`, `is_empty_strat` — predicates for strategy completeness.
- `stratDrive`, `multiStratDrive` — execution semantics of transactions under a strategy.
- `interleavedExecution` — execution with honest users and adversary actions.
- `userLiquidates`, `envProgress`, `usl`, `asl` — formal liquidity predicates.
- `strat_liquidity` — strategy-aware liquidity requiring contract balance to zero.
- `strat_liq_inst`, `basic_liq_inst` — show specialization relations between these properties.

#### 3.2 `Mono.v`

- Proves the **monotonicity** relation:  
  A stronger adversary strategy strengthens the implications of strategy-aware liquidity.

#### 3.3 `Equivalence.v`

- Establishes formal **equivalence** (or lack thereof) between strategy-aware liquidity and basic liquidity.

---

##  Liquidity Proofs for Example Smart Contracts

### 📁 `examples/fundsManagement`

#### 🔴 Flawed Version (`FundsManagement_error.v`)
- Demonstrates a contract with re-initialization vulnerability.
- Violates **strategy-aware liquidity** under adversarial re-initialization.
- Still satisfies **basic liquidity**.

####  Corrected Version (`FundsManagement_correct.v`)
- Removes re-initialization vulnerability.
- Satisfies **both** strategy-aware and basic liquidity under all adversary strategies.

---

###  `examples/lucky7game/EtherGame.v`

- Models a gaming contract.
- Proves strategy-aware liquidity holds even under self-destruct attack attempts.
- Satisfies basic liquidity.

---

###  `examples/honeypots/Honeypots.v`

- Models a honeypot contract.
- **Violates** strategy-aware liquidity.
- **Satisfies** basic liquidity.

---

## 👩‍💻 Code Contributors

**Main authors of this Coq development:**  
Sensen Chen and Ximeng Li

---
