# GroebnerTac
This repository contains Lean 4 tactics focused on the automated formal verification of Groebner Basis properties and computations. 

Our main goal is to create powerful tactics that can automatically prove theorems related to Groebner Basis or the application of Groebner Basis within the Lean 4 theorem prover. 

For the foundational definitions and theorems concerning Groebner Bases that underpin this work, please refer to our [groebner_proj](https://github.com/WuProver/groebner_proj). A significant challenge in Lean is that the standard `MvPolynomial` type is generally non-computable in the context of proof automation. To address this, we have developed a dedicated implementation of [computable polynomials](https://github.com/WuProver/MonomialOrderedPolynomial) suitable for execution and computation within Lean's kernel.

Both the library and its documents are still WIP.
## Introduction
### Lean To Sage

### Sage To Lean

### Sage Code

### Tactic


## Build
If you don't already have Lean 4 set up, please follow the official [Lean 4 installation instructions](https://leanprover-community.github.io/get_started.html).

Once Lean is installed, you can clone this repository and build the project:

```bash
git clone https://github.com/WuProver/GroebnerTactic.git
lake exe cache get
lake build
```

To utilize the full functionality of this project, you need to install SageMath, please follow the official [SageMath installation instructions](https://doc.sagemath.org/html/en/installation/index.html).


## WIP
1. clean up code;
2. solve problems related to the automatic determination of ideal intersection;
