import Paxos.Spec
import Paxos.Prop
import Mathlib.Tactic
import Mathlib.Data.Set.Basic

namespace Paxos.ExtraLemma
open Paxos.Spec Paxos.Prop
open Set Classical

variable (Quorums: Set (Set Acceptor)) -- Reintroduce Quorums
variable (sent sent': Set Message) -- Reintroduce sent

/-- This lemma says we can pick something from the intersection of quorums, this is the immediate result of `QuorumAssumption`-/
@[simp]
lemma pick_from_quorum_int {Q₁: Set Acceptor} {Q₂: Set Acceptor} (h1: Q₁ ∈ Quorums) (h2: Q₂ ∈ Quorums): ∃a: Acceptor, a ∈ Q₁ ∩ Q₂ := by
  have hne := QuorumAssumption Quorums h1 h2

  rcases ((Iff.mpr nonempty_iff_ne_empty) hne) with ⟨aa, haa⟩ -- nonempty_iff_ne_empty took me some time to find
  exact Exists.intro aa haa

@[simp]
lemma option.some_succ_le_some_of_some_le_and_lt {n m k : Ballot}
  (h₁ : some n ≤ some m) (h₂ : m < k) :
  some (n + 1) ≤ some k := by
  apply Option.some_le_some.mp at h₁
  apply le_trans (Nat.succ_le_succ h₁) (Nat.succ_le_iff.mpr h₂)

/-- This is the immediate consequence of the definition of `Send`.
-/
@[simp]
lemma send_monotonic {sent sent': Set Message} {x: Message} (h: sent' = Send x sent) : sent ⊆ sent' := by
  unfold Send at h; intro X hX; rw [h]; exact mem_union_left {x} hX

/-- This lemma states the messages in max_prop are of type `twob`.
-/
@[simp]
theorem mem_max_prop_is_twob {m : Message} {a : Acceptor}:
  m ∈ max_prop sent a → ∃ (b : Option Ballot) (v : Option Value), m = Message.twob b v a := by
  dsimp [max_prop] at *
  split_ifs with h_nonempty
  · simp only [Set.mem_sep, Set.mem_setOf, exists_prop, and_assoc] at *
    intro hm; simp at hm
    simp [hm]
  · intro h_mem
    simp only [Set.mem_setOf, exists_prop, and_assoc] at h_mem
    rcases h_mem with ⟨_h_sent, ⟨b, v, rfl⟩, _⟩
    exact ⟨b, v, rfl⟩

@[simp]
theorem max_prop_not_empty_implies_voted_for {a : Acceptor} {b: Ballot} {v: Value} : Message.twob b (some v) a ∈ max_prop sent a → VotedForIn sent a v b := by
  intro h_mem
  unfold max_prop at h_mem
  simp [*] at *
  split_ifs at h_mem with h_nonempty
  · simp only [Set.mem_sep, Set.mem_setOf, exists_prop, and_assoc] at h_mem
    unfold VotedForIn
    simp [*] at *
  · exfalso
    simp at *

-- Effort: 20 min
/-- This lemma states that either one of ballot or value is empty, then the other one must also be empty

This is used in later proof when we need to do

`match rbal, rval with
| some rbal, none | none, some rval => `

and derives a contradiction because it can't be the case.
-/
@[simp]
lemma max_prop_empty_ballot_iff_empty_value {a : Acceptor} {m : Message}
  (hm : m ∈ max_prop sent a) :
  (∃ b, m = Message.twob (some b) none a) ↔ ∃ v, m = Message.twob none (some v) a := by
  dsimp [max_prop] at hm
  let twobs := { m | m ∈ sent ∧ ∃ b v, m = Message.twob (some b) (some v) a }
  split_ifs at hm with h_nonempty
  · simp at hm; simp [hm];
  · simp [*] at hm; have h_m_twob := hm.left.right; rcases h_m_twob with ⟨b, v, rfl⟩; simp;

@[simp]
theorem max_prop_implies_not_voted_for_greater_ballots {a: Acceptor} {b : Ballot} {v: Value} : Message.twob b (some v) a ∈ max_prop sent a → ∀ b' v', b' > b → ¬ VotedForIn sent a v' b' := by
  intro h_mem
  unfold max_prop at h_mem
  simp [*] at *
  let twobs := { m | m ∈ sent ∧ ∃ b v, m = Message.twob b v a }
  split_ifs at h_mem with h_nonempty
  · simp only [Set.mem_sep, Set.mem_setOf, exists_prop, and_assoc] at h_mem
    rcases h_mem with ⟨h1, h2, h3⟩
    by_contra h_neg
    unfold VotedForIn at *
    simp [*] at *
    obtain ⟨b', hb'_gt, v', hmem'⟩ := h_neg
    specialize h3 (Message.twob b' (some v') a)
    simp [*] at *
    exact Nat.le_lt_asymm h3 hb'_gt
  · exfalso
    simp at *

-- Effort: 20 min
/-- It states that if the message from `max_prop` has empty ballot and value, then the acceptor has not voted in any previous ballots.

Used in proving the case when both `rbal` and `rval` are empty in the proof of `Phase1b`.
-/
@[simp]
theorem max_prop_empty_implies_not_voted_in_prev_ballots {a: Acceptor} (hm: Message.twob none none a ∈ max_prop sent a) : ∀ b, ∀ (v: Value), ¬ VotedForIn sent a v b := by
  intro b' hb'_le h_voted
  unfold max_prop at hm
  simp [*] at *
  let twobs := { m | m ∈ sent ∧ ∃ b v, m = Message.twob b v a }
  split_ifs at hm with h_nonempty
  · simp only [Set.mem_sep, Set.mem_setOf, exists_prop, and_assoc] at hm
    simp at hm
  · unfold VotedForIn at h_voted
    obtain ⟨m, hm_sent, hm_two_b⟩ := h_voted
    rw [not_exists] at h_nonempty
    specialize h_nonempty m
    simp [hm_sent, hm_two_b] at h_nonempty
    simp [*] at *

/-- This lemma states that if `sent` is a subset of `sent'`, then `VotedForIn sent a v b` implies
    `VotedForIn sent' a v b`. This is used in the proof of `SafeAtStable`.
-/
@[simp]
lemma votedForIn_monotonic {a: Acceptor} {v: Value} {b: Ballot} (h1: sent ⊆ sent'): VotedForIn sent a v b → VotedForIn sent' a v b := by
  intro h1
  rcases h1 with ⟨m, hm, hmatch⟩
  use m
  refine (and_iff_right ?h.ha).mpr hmatch
  apply h1; exact hm

@[simp]
lemma phase1a_imp_mono_sent {b: Ballot} (hPhase1a: Phase1a sent sent' b) : sent ⊆ sent' := by
  unfold Phase1a at hPhase1a; exact send_monotonic hPhase1a

@[simp]
lemma phase1b_imp_mono_sent {a: Acceptor} (hPhase1b: Phase1b sent sent' a) : sent ⊆ sent' := by
  unfold Phase1b at hPhase1b
  rcases hPhase1b with ⟨m, hm, r, hr, hmatch⟩
  cases m with
  | onea mbal =>
    cases r with
    | twob rbal rvbal racc =>
      simp at hmatch
      split_ifs at hmatch with hpos <;> simp [*] at *
    | _ => simp at *;
  | _ => simp at *;

@[simp]
lemma phase2a_imp_mono_sent {b: Ballot} (hPhase2a: Phase2a Quorums sent sent' b) : sent ⊆ sent' := by
  unfold Phase2a at hPhase2a
  split_ifs at hPhase2a with h1 h2 <;> simp [*] at *

@[simp]
lemma phase2b_imp_mono_sent {a: Acceptor} (hPhase2b: Phase2b sent sent' a) : sent ⊆ sent' := by
  unfold Phase2b at hPhase2b
  rcases hPhase2b with ⟨m2b, hm2b, hmatch⟩
  cases m2b with
  | twoa mbal mval =>
    simp at hmatch
    split_ifs at hmatch with hpos <;> simp [*] at *
  | _ => simp at hmatch; simp [*] at *;

/-- This lemma simply states that `sent` grows monotonically with `Next`.
    That is, if `sent` is a subset of `sent'`, then `Next` will also be a subset of `sent'`.
    This is used in the proof of `SafeAtStable`.
-/
@[simp]
lemma next_imp_mono_sent (hNext: Next Quorums sent sent') : sent ⊆ sent' := by
  unfold Next at hNext
  rcases hNext with ⟨b, hPhase1a⟩ | ⟨a, hPhase1b⟩ | ⟨b, hPhase2a⟩ | ⟨a, hPhase2b⟩
  · exact phase1a_imp_mono_sent sent sent' hPhase1a
  · exact phase1b_imp_mono_sent sent sent' hPhase1b
  · exact phase2a_imp_mono_sent Quorums sent sent' hPhase2a
  · exact phase2b_imp_mono_sent sent sent' hPhase2b

/--
  This is the immediate consequence of the definition of VotedForIn. If no 2b message is added to `sent`, then the value predicate `¬VotedForIn` is preserved.
-/
@[simp]
lemma send_add_non_twob_preserves_no_vote {a: Acceptor} {b: Ballot} {m: Message} (hnv : ∀ v, ¬ VotedForIn sent a v b) (hsend : sent' = Send m sent) (hm : (∃ bal, m = Message.onea bal) ∨ (∃ bal maxV maxVal a', m = Message.oneb bal maxV maxVal a') ∨ (∃ bal val, m = Message.twoa bal val)) : ∀ v, ¬ VotedForIn sent' a v b := by
  intro v hVoted
  cases hm with
  | inl h_1a => specialize hnv v; unfold VotedForIn at *; simp [hsend, hVoted] at hVoted; cases hVoted with
    | inl h_m_eq_2b => cases m with
      | _ => simp [*] at *
    | inr h_2b_in_sent => simp [*] at *;
  | inr h_1b_2a => cases h_1b_2a with
    | inl h_1b => specialize hnv v; unfold VotedForIn at *; simp [hsend, hVoted] at hVoted; cases hVoted with -- This could be simplified to one line with <;> as below, here keep it for clarity
      | inl h_m_eq_2b => cases m <;> simp [*] at *
      | inr h_2b_in_sent => simp [*] at *
    | inr h_2a => specialize hnv v; unfold VotedForIn at *; simp [hsend, hVoted] at hVoted; cases hVoted <;> cases m <;> simp [*] at * -- Simplified

/-- This lemma corresponds to the monotonicity of existantial quantifier describe in the paper -/
theorem exists_mem_of_subset {s t : Set Message} {P : Message → Prop}
  (hsub : s ⊆ t) (hex : ∃ x ∈ s, P x) : ∃ x ∈ t, P x := by
  rcases hex with ⟨x, hx_s, hx_P⟩
  exact ⟨x, hsub hx_s, hx_P⟩

end Paxos.ExtraLemma
