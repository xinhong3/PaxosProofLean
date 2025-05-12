import Paxos.Spec
import Paxos.Prop
import Mathlib.Tactic
import Mathlib.Data.Set.Basic

namespace Paxos.ExtraLemma
open Paxos.Spec Paxos.Prop
open Set Classical

variable (Quorums: Set (Set Acceptor)) -- Reintroduce Quorums

/-- This lemma says we can pick something from the intersection of quorums, this is the immediate result of `QuorumAssumption`-/
@[simp]
lemma pick_from_quorum_int {Q₁: Set Acceptor} {Q₂: Set Acceptor} (h1: Q₁ ∈ Quorums) (h2: Q₂ ∈ Quorums): ∃a: Acceptor, a ∈ Q₁ ∩ Q₂ := by
  have hne := QuorumAssumption Quorums h1 h2
  rcases ((Iff.mpr nonempty_iff_ne_empty) hne) with ⟨aa, haa⟩ -- This took me
  exact Exists.intro aa haa


/-- This is the immediate consequence of the definition of `Send`.
-/
@[simp]
lemma send_monotonic {sent sent': Set Message} {x: Message} (h: sent' = Send x sent) : sent ⊆ sent' := by
  unfold Send at h; intro X hX; rw [h]; exact mem_union_left {x} hX


/-- This lemma states the messages in max_prop are of type `twob`.
-/
@[simp]
theorem mem_max_prop_is_twob {m : Message} {a : Acceptor}:
  m ∈ max_prop sent a → ∃ (b : Ballot) (v : Option Value), m = Message.twob b v a := by
  dsimp [max_prop] at *
  let twobs := { m | m ∈ sent ∧ ∃ b v, m = Message.twob b v a }
  split_ifs with h_nonempty
  · simp only [Set.mem_sep, Set.mem_setOf, exists_prop, and_assoc] at *
    intro hm; simp at hm
    simp [hm]
  · intro h_mem
    simp only [Set.mem_setOf, exists_prop, and_assoc] at h_mem
    rcases h_mem with ⟨_h_sent, ⟨b, v, rfl⟩, _⟩
    exact ⟨b, v, rfl⟩

/-- This lemma states that if we have a non-empty message from `max_prop`, then it must be a previous `twob` vote message.
-/
@[simp]
lemma max_prop_nonempty_imp_votedForIn {a : Acceptor} {v : Value} {b : Ballot} (h: m ∈ max_prop sent a) (h_not_empty: m = Message.twob b (some v) a) : VotedForIn sent a v b := by
  have hm_sent : m ∈ sent := by
    unfold max_prop at h
    dsimp at h
    split_ifs at h with h_pos
    · simp [*] at * -- This is contradicting to h_non_empty so we can use simp
    · rcases h with ⟨h1, h2⟩
      exact h1.left
  apply mem_max_prop_is_twob at h
  unfold VotedForIn at *
  exact Filter.frequently_principal.mp fun a => a hm_sent h_not_empty

/-- This lemma states that if `sent` is a subset of `sent'`, then `VotedForIn sent a v b` implies
    `VotedForIn sent' a v b`. This is used in the proof of `SafeAtStable`.
-/
@[simp]
lemma votedForIn_monotonic (h1: sent ⊆ sent'): VotedForIn sent a v b → VotedForIn sent' a v b := by
  intro h1
  rcases h1 with ⟨m, hm, hmatch⟩
  use m
  refine (and_iff_right ?h.ha).mpr hmatch
  apply h1; exact hm

/-- This lemmae simply states that `sent` grows monotonically with `Next`.
    That is, if `sent` is a subset of `sent'`, then `Next` will also be a subset of `sent'`.
    This is used in the proof of `SafeAtStable`.
-/
@[simp]
lemma next_imp_mono_sent (hNext: Next Quorums sent sent') : sent ⊆ sent' := by
  unfold Next at hNext
  rcases hNext with ⟨b, hPhase1a⟩ | ⟨a, hPhase1b⟩ | ⟨b, hPhase2a⟩ | ⟨a, hPhase2b⟩
  · unfold Phase1a at hPhase1a; exact send_monotonic hPhase1a
  · unfold Phase1b at hPhase1b
    rcases hPhase1b with ⟨m, hm, r, hr, hmatch⟩
    cases m with
    | onea mbal =>
      cases r with
        | twob rbal rvbal racc =>
          simp at hmatch
          split_ifs at hmatch with hpos <;> simp [*] at *
        | _ => simp at *;
    | _ => simp at *;
  · unfold Phase2a at hPhase2a
    split_ifs at hPhase2a with h1 h2 <;> simp [*] at *
  · unfold Phase2b at hPhase2b
    rcases hPhase2b with ⟨m2b, hm2b, hmatch⟩
    cases m2b with
    | twoa mbal mval =>
      simp at hmatch
      split_ifs at hmatch with hpos <;> simp [*] at *
    | _ => simp at hmatch; simp [*] at *;

/--
  This is the immediate consequence of the definition of VotedForIn. If no 2b message is added to `sent`, then the value predicate `¬VotedForIn` is preserved.
-/
lemma send_add_non_twob_preserves_no_vote (hnv : ∀ v, ¬ VotedForIn sent a v b) (hsend : sent' = Send m sent) (hm : (∃ bal, m = Message.onea bal) ∨ (∃ bal maxV maxVal a', m = Message.oneb bal maxV maxVal a') ∨ (∃ bal val, m = Message.twoa bal val)) : ∀ v, ¬ VotedForIn sent' a v b := by
  intro v hVoted
  cases hm with
  | inl h_1a => specialize hnv v; unfold VotedForIn at *; simp [hsend, hVoted] at hVoted; cases hVoted with
    | inl h_m_eq_2b => cases m with
      | _ => simp [*] at *
    | inr h_2b_in_sent => simp [*] at *;
  | inr h_1b_2a => cases h_1b_2a with
    | inl h_1b => specialize hnv v; unfold VotedForIn at *; simp [hsend, hVoted] at hVoted; cases hVoted with
      | inl h_m_eq_2b => cases m with
        | _ => simp [*] at *
      | inr h_2b_in_sent => simp [*] at *
    | inr h_2a => specialize hnv v; unfold VotedForIn at *; simp [hsend, hVoted] at hVoted; cases hVoted with
      | inl h_m_eq_2b => cases m with
        | _ => simp [*] at *
      | inr h_2b_in_sent => simp [*] at *;

/-- This lemma corresponds to the monotonicity of existantial quantifier describe in the paper -/
theorem exists_mem_of_subset {s t : Set Message} {P : Message → Prop}
  (hsub : s ⊆ t) (hex : ∃ x ∈ s, P x) : ∃ x ∈ t, P x := by
  rcases hex with ⟨x, hx_s, hx_P⟩
  exact ⟨x, hsub hx_s, hx_P⟩

end Paxos.ExtraLemma
