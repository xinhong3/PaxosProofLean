# Safety Proof of Basic Paxos in Lean 4

A mechanically-checked proof of the Basic Paxos consensus algorithm in Lean 4, translated from the TLA+ version:

> Chand, S. and Liu, Y. A. (2018).  
> **Simpler Specifications and Easier Proofs of Distributed Algorithms Using History Variables**  
> _arXiv preprint_ arXiv:1802.09687.  
> ↗︎ [https://arxiv.org/pdf/1802.09687](https://arxiv.org/pdf/1802.09687)

## Overview

This repository contains:

- The proof for safety of Basic Paxos, translated from Chand and Liu (2018).
- \[**Removed**\] A (partial) fork of [Lean-SMT](https://github.com/ufmg-smite/lean-smt)@1df3f3 for potential SMT-powered simplifications -- forking resolve the build failure from starting from a new lean project and adding Smt as a dependency. However, I still couldn't get Smt to work with the proof so it's not being used in the project currently.

The main theorem proved is the Safety Property (also called Agreement) of Basic Paxos in `Proof.lean`:

```lean
/-- THEOREM Agreement in CL. -/
theorem Agreement {σ : ℕ → Set Message}
    (hSpec : PaxosSpec Quorums σ) : ∀ n, Agree (σ n) Quorums := by
  have inv : ∀ n, MsgInv (σ n) Quorums := by
    intro n
    exact Invariant Quorums hSpec n
  exact fun n ↦ msginv_implies_agree (σ n) Quorums (inv n)
```

## Project Layout

```
.
├── Paxos/                 
│   ├── Spec.lean          ← Protocol specs (Phase1a, Phase1b, Phase2a, Phase2b & Next)
│   ├── Prop.lean          ← Invariant (MsgInv) defintion, defintions of other predicates used in the proof.
│   ├── ExtraLemmas.lean   ← Helper lemmas for easing the proof.
│   └── Proof.lean         ← Proof for the Safety Property, and inductiveness of invariant.
├── lakefile.lean
└── README.md
```

## Prerequisites

- Lean 4: recommended setup is to use VSCode. [Here](https://leanprover-community.github.io/get_started.html) is the official instuction. This project was written with Lean v4.16.0 but now it's bumpped to v4.22.0-rc3. See `./lean-toolchain` for the version used. See `lakefile.lean` for dependencies.
- After setting up Lean with VSCode, `elan --version` should work after restarting shell, if not, make sure to add `~/.elan/bin` to `PATH`.


## Building the Project

Paxos.lean is set to be the default build (see `lakefile.lean`), by running

```bash
lake build
```

It will build `./Paxos.lean` which imports the Spec, Lemmas and Proof from `./Paxos`. The expected output should be:

```
Build completed successfully.
```