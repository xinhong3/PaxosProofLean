# Proof of Basic Paxos in Lean 4

A mechanically-checked proof of the Basic Paxos consensus algorithm in Lean 4, translated from the TLA+ version:

> Chand, S. and Liu, Y. A. (2018).  
> **Simpler Specifications and Easier Proofs of Distributed Algorithms Using History Variables**  
> _arXiv preprint_ arXiv:1802.09687.  
> ↗︎ [https://arxiv.org/pdf/1802.09687](https://arxiv.org/pdf/1802.09687)

## Overview

This repository contains:

- A port of the Paxos proof from Chand & Liu’s history-variable approach into Lean 4.  
- A (partial) fork of [Lean-SMT](https://github.com/ufmg-smite/lean-smt)@1df3f3 for potential SMT-powered simplifications -- forking resolve the build failure from starting from a new lean project and adding Smt as a dependency. However, I still couldn't get Smt to work with the proof so it's not being used in the project currently.

---

## Project Layout

```
.
├── Paxos/                 
│   ├── Spec.lean          ← Protocol specs (Phase1a, Phase1b, Phase2a, Phase2b & Next)
│   ├── Prop.lean          ← Predicate definitions
│   ├── ExtraLemmas.lean   ← Helper lemmas (not in the paper) for easing the proof
│   └── Proof.lean         ← Main safety‐property proof
├── lakefile.lean          ← Lake build configuration
└── README.md              ← Project overview
```

## Prerequisites

- Lean 4: recommended setup is to use VSCode. [Here](https://leanprover-community.github.io/get_started.html) is the official instuction. This project is with Lean v4.16.0 (see `./lean-toolchain`), see `lakefile.lean` for dependencies.
- After setting up Lean with VSCode, `elan --version` should work after restarting shell, if not, make sure to add `~/.elan/bin` to `PATH`.

---

## Building the Project

Paxos.lean is set to be the default build (see `lakefile.lean`), by running

```bash
lake build
```

It will build `./Paxos.lean` which imports the Spec, Lemmas and Proof from `./Paxos`. By default, lean will give a warning if there's `sorry` in the proof:

```
warning: ././././Paxos/Proof.lean:164:8: declaration uses 'sorry'
```