import Mathlib.Tactic
import Smt
import Smt.Auto

set_option auto.native true

open Set
open Classical

-- Types Definition --
abbrev Acceptor := String   -- Acceptor
abbrev Value := Nat         -- Value
abbrev Ballot := Int        -- Ballot is defined to be Int to include -1 as empty ballot

-- We define Message as an inductive type --
inductive Message where
| onea  (bal : Ballot) : Message
| oneb  (bal : Ballot) (maxVBal : Ballot) (maxVal : Option Value) (acc : Acceptor) : Message -- maxVBal could be 0, and maxVal could be none
| twoa  (bal : Ballot) (val : Value) : Message
| twob  (bal : Ballot) (val : Option Value) (acc : Acceptor) : Message                       -- val is of Option becuase last_voted defintion

variable (sent sent': Set Message) -- sent' is added here to model the next state

def VotedForIn (a : Acceptor) (v : Value) (b : Ballot) : Prop :=
  ∃ m ∈ sent, m = Message.twob b v a

lemma votedForIn_monotonic (h1: sent ⊆ sent'): VotedForIn sent a v b → VotedForIn sent' a v b := by
  intro h1
  rcases h1 with ⟨m, hm, hmatch⟩
  use m
  refine (and_iff_right ?h.ha).mpr hmatch
  apply h1; exact hm

-- Can we use `smt` here?
lemma votedForIn_monotonic' (h1: sent ⊆ sent'): VotedForIn sent a v b → VotedForIn sent' a v b := by
  -- auto [h1] d[VotedForIn] -- Error: Auto.LamReif.reifTermCheckType :: LamTerm (∀ x0 : #1, (∀ x1 : #1, ((!7 (x0 =) x1) = (x0 = x1)))) is not type correct Lean 4
  smt_show [h1] -- Error: incorrect number of universe levels SetLean 4
  sorry


-- (Tomaz Mascarenhas) Hi Ethan, do this:


set_option auto.mono.mode "fol"
set_option auto.mono.ciInstDefEq.mode "reducible"
set_option auto.mono.termLikeDefEq.mode "reducible"

-- Can we use `smt` here?
lemma votedForIn_monotonic' (h1: sent ⊆ sent'): VotedForIn sent a v b → VotedForIn sent' a v b := by
  auto [Set.subset_def, h1] d[VotedForIn] -- OK!
