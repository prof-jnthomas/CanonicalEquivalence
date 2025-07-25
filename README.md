# CanonicalEquivalence: A Syntactic Construction of Canonical Kripke Models

This Agda formalization demonstrates a constructive correspondence between derivability in a minimal intuitionistic propositional logic and canonical Kripke models. It includes a full syntactic proof of compactness and finitary derivability, and will ultimately construct a canonical Kripke model from syntactic data, establishing a form of soundness and completeness entirely within a syntactic setting.

The goal of this project is to show that canonical Kripke semantics *recapitulate syntactic structure*, and to make precise the sense in which model-theoretic notions in intuitionistic logic can be grounded constructively.

## ✨ Highlights

* **Formal system**: A minimal IPL with `⊥`, `→`, `∧`, and `∨`
* **Proof system**: Inductive derivability judgment `Γ ⊦ ϕ`
* **Compactness**: If `Γ ⊦ ⊥`, then some finite `Δ ⊆ Γ` has `Δ ⊦ ⊥`
* **Constructive completeness**: `∀Δ. Δ ⊆ Γ → Δ ⊦ ϕ` implies `Γ ⊦ ϕ`
* **Contrapositive**: If `¬- **Contrapositive**: If `\xac(Γ ⊦ ϕ)`, then ∃ finite `Δ ⊆ Γ`such that`¬`such that`\xac(Δ ⊦ ϕ)\`
* **Kripke models (in progress)**: Canonical construction of a Kripke frame from syntactic entailment and demonstration that forcing aligns with `⊦`

The project aims to show that even Kripke semantics—typically viewed as a model-theoretic or semantic tool—can be reconstructed from syntactic, constructive data alone.

---

## 📂 Project Structure

```
CanonicalEquivalence/
├── check.sh                           -- Shell script for checking the project
├── Makefile                           -- Alternative build interface
├── CanonicalEquivalence.agda          -- Top-level re-export ("barrel") file
├── CanonicalEquivalence.agda-lib      -- Agda project file
└── CanonicalEquivalence/
    ├── Syntax.agda                    -- Formula syntax, theory representation
    ├── Helpers.agda                   -- Subset and restoration lemmas
    ├── ProofSystem.agda               -- Derivation rules and lifting
    ├── Compactness.agda               -- Finitary derivability and compactness
    ├── Completeness.agda              -- Constructive completeness theorems
    └── Kripke/
      └── Canonical.agda               -- Canonical Kripke model construction (WIP)
```

---

## ✅ Checking the Project

You can type-check the entire project in two ways:

### Method 1: Shell script

```bash
./check.sh
```

### Method 2: Makefile

```bash
make
```

### Clean up `.agdai` cache files

```bash
make clean
```

---

## 🧠 Requirements

* [Agda](https://agda.readthedocs.io/en/v2.7.0.1/) (tested with version 2.7.0.1)
* No external libraries — this project uses only core Agda and the standard library modules

---

## 📚 Citation and Status

This repository accompanies ongoing research. If you reference this work, please cite the corresponding arXiv preprint (to be added).

---

## 👤 Author

James N. Thomas
*Professor of Computer Science*
Whatcom Community College

---

## 📜 License

MIT License (see LICENSE file)
