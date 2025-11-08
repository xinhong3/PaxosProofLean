/-
  Extra lemmas used to simplify the safety proof.
  These are not present in the TLAPS proof in https://arxiv.org/pdf/1802.09687.
-/
import Paxos.Spec
import Paxos.Prop
import Mathlib.Tactic
import Mathlib.Data.Set.Basic

namespace Paxos.ExtraLemma
open Paxos.Spec Paxos.Prop
open Set Classical

variable (Quorums: Set (Set Acceptor))
variable (sent sent': Set Message)

-- The following four are helper definitions for checking message types.

@[simp] def is1a : Message → Prop | Message.onea _ => True | _ => False
@[simp] def is1b : Message → Prop | Message.oneb _ _ _ _ => True | _ => False
@[simp] def is2a : Message → Prop | Message.twoa _ _ => True | _ => False
@[simp] def is2b : Message → Prop | Message.twob _ _ _ => True | _ => False

/-- Used in proving that Phase2a is inductive. -/
@[simp]
lemma ballot_none_plus_one_leq_ballot
    {b : Ballot} : (none : Option Ballot) + (1 : Nat) ≤ some b := by
  dsimp [HAdd.hAdd]
  exact Nat.zero_le b

/-- The immediate consequence of `QuorumAssumption`. Used to pick an witness from the
intersection of two quorums. -/
@[simp]
lemma pick_from_quorum_int {Q₁ Q₂ : Set Acceptor}
    (h1: Q₁ ∈ Quorums)
    (h2: Q₂ ∈ Quorums) : ∃ a: Acceptor, a ∈ Q₁ ∩ Q₂ := by
  have hne := QuorumAssumption Quorums h1 h2
  rcases ((Iff.mpr nonempty_iff_ne_empty) hne) with ⟨aa, haa⟩
  exact Exists.intro aa haa

/-- Transitive property of `Option Ballot`. Used in `ind_phase2a`. -/
@[simp]
lemma option.some_succ_le_some_of_some_le_and_lt {n m k : Ballot}
    (h₁ : some n ≤ some m)
    (h₂ : m < k) : some (n + 1) ≤ some k := by
  apply Option.some_le_some.mp at h₁
  apply le_trans (Nat.succ_le_succ h₁) (Nat.succ_le_iff.mpr h₂)

/-- The messages in `max_prop` are of type `twob`. -/
@[simp]
lemma mem_max_prop_is_2b {m : Message} {a : Acceptor} :
    m ∈ max_prop sent a →
      ∃ (b : Option Ballot) (v : Option Value), m = Message.twob b v a := by
  dsimp [max_prop] at *
  split_ifs with h_nonempty
  · simp
    intro hm;
    simp [hm]
  · intro h_mem
    simp only [Set.mem_setOf, and_assoc] at h_mem
    rcases h_mem with ⟨_h_sent, ⟨b, v, rfl⟩, _⟩
    exact ⟨b, v, rfl⟩

/-- If `max_prop` is not empty, then the acceptor must has voted for the value. -/
@[simp]
lemma max_prop_not_empty_implies_voted_for {a : Acceptor} {b : Ballot} {v : Value} :
    Message.twob b (some v) a ∈ max_prop sent a →
      VotedForIn sent a v b := by
  intro h_mem
  unfold max_prop at h_mem
  simp at h_mem
  split_ifs at h_mem with h_nonempty
  · simp only [Set.mem_setOf, and_assoc] at h_mem
    unfold VotedForIn
    simp [h_mem.1]
  · exfalso
    simp at h_mem

/-- If either ballot or value is empty, then the other one must also be empty.
This is used in later proof when we need to do pattern matching on both ballot and value
for `Message.twob`, and since they are both `Option`, we need to cover the following
cases: `match rbal, rval with | some rbal, none | none, some rval => ...` -/
@[simp]
lemma max_prop_empty_ballot_iff_empty_value {a : Acceptor} {m : Message}
    (hm : m ∈ max_prop sent a) :
    (∃ b, m = Message.twob (some b) none a) ↔ ∃ v, m = Message.twob none (some v) a := by
  dsimp [max_prop] at hm
  let twobs := { m | m ∈ sent ∧ ∃ b v, m = Message.twob (some b) (some v) a }
  split_ifs at hm with h_nonempty
  · simp at hm; simp [hm];
  · simp [*] at hm; have h_m_twob := hm.left.right; rcases h_m_twob with ⟨b, v, rfl⟩; simp

/-- The acceptor could not have voted for a ballot greater than the one in `max_prop` -/
@[simp]
lemma max_prop_implies_not_voted_for_greater_ballots
    {a : Acceptor} {b : Ballot} {v: Value} :
    Message.twob b (some v) a ∈ max_prop sent a →
      ∀ b', b' ≥ b+1 → ¬∃ v, VotedForIn sent a v b' := by
  intro h_mem
  unfold max_prop at h_mem
  simp at h_mem
  let twobs := { m | m ∈ sent ∧ ∃ b v, m = Message.twob b v a }
  split_ifs at h_mem with h_nonempty
  · simp only [Set.mem_setOf, and_assoc] at h_mem
    rcases h_mem with ⟨h1, h2, h3⟩
    by_contra h_neg
    unfold VotedForIn at *
    simp at h_neg
    obtain ⟨b', hb'_gt, v', hmem'⟩ := h_neg
    specialize h3 (Message.twob b' (some v') a)
    simp [hmem'] at h3
    exact Nat.le_lt_asymm h3 hb'_gt
  · exfalso
    simp at *

/-- If the message from `max_prop` has empty ballot and value, then the acceptor has not
voted in any previous ballots. Used in proving the case when both `rbal` and `rval` are
empty in the proof of `Phase1b`. -/
@[simp]
lemma max_prop_empty_implies_not_voted_in_prev_ballots {a: Acceptor}
    (hm: Message.twob none none a ∈ max_prop sent a) :
    ∀ b, ∀ (v: Value), ¬ VotedForIn sent a v b := by
  intro b' hb'_le h_voted
  unfold max_prop at hm
  simp [*] at *
  let twobs := { m | m ∈ sent ∧ ∃ b v, m = Message.twob b v a }
  split_ifs at hm with h_nonempty
  · simp only [Set.mem_setOf, and_assoc] at hm
    simp at hm
  · unfold VotedForIn at h_voted
    obtain ⟨m, hm_sent, hm_two_b⟩ := h_voted
    rw [not_exists] at h_nonempty
    specialize h_nonempty m
    simp [hm_two_b] at h_nonempty
    rw [←hm_two_b] at h_nonempty
    exact h_nonempty hm_sent

-- The following 5 lemmas are used to show that `sent` grows monotonically with `Next`.

/--The immediate consequence of the definition of `Send`. We use this lemma to show that
`Next` grows the history variable `sent` monotonically. -/
@[simp]
lemma send_monotonic {sent sent': Set Message} {x: Message}
    (h: sent' = Send x sent) : sent ⊆ sent' := by
  simp [Send, h]

/-- `Phase1a` grows `sent` monotonically. -/
@[simp]
lemma phase1a_imp_mono_sent {b: Ballot}
    (hPhase1a: Phase1a sent sent' b) : sent ⊆ sent' := by
  exact send_monotonic hPhase1a

/-- `Phase1b` grows `sent` monotonically. -/
@[simp]
lemma phase1b_imp_mono_sent {a: Acceptor}
    (hPhase1b: Phase1b sent sent' a) : sent ⊆ sent' := by
  rcases hPhase1b with ⟨m, hm, r, hr, hmatch⟩
  cases m <;> cases r <;> simp at hmatch; simp [hmatch]

/-- `Phase2a` grows `sent` monotonically. -/
@[simp]
lemma phase2a_imp_mono_sent {b: Ballot}
    (hPhase2a: Phase2a Quorums sent sent' b) : sent ⊆ sent' := by
  rcases hPhase2a with ⟨h_no_2a, ⟨_, _, _, h_rest⟩⟩
  simp [h_rest]

/-- `Phase2b` grows `sent` monotonically. -/
@[simp]
lemma phase2b_imp_mono_sent {a: Acceptor}
    (hPhase2b: Phase2b sent sent' a) : sent ⊆ sent' := by
  rcases hPhase2b with ⟨m2b, hm2b, hmatch⟩
  cases m2b <;> simp at hmatch; simp [hmatch]

/-- `sent` grows monotonically with `Next`. Used in the proof of `SafeAtStable`. -/
@[simp]
lemma next_imp_mono_sent
    (hNext: Next Quorums sent sent') : sent ⊆ sent' := by
  rcases hNext with ⟨b, hPhase1a | hPhase2a⟩ | ⟨a, hPhase1b | hPhase2b⟩
  · exact phase1a_imp_mono_sent sent sent' hPhase1a
  · exact phase2a_imp_mono_sent Quorums sent sent' hPhase2a
  · exact phase1b_imp_mono_sent sent sent' hPhase1b
  · exact phase2b_imp_mono_sent sent sent' hPhase2b

/-- The monotonicity of existantial quantifier describe in the TLAPS proof. -/
lemma exists_mem_of_subset {s t : Set Message} {P : Message → Prop}
    (hsub : s ⊆ t) (hex : ∃ x ∈ s, P x) : ∃ x ∈ t, P x := by
  rcases hex with ⟨x, hx_s, hx_P⟩
  exact ⟨x, hsub hx_s, hx_P⟩

/-- If `sent` is a subset of `sent'`, then voted in the former implies voted in the latter.
Used in the proof of `SafeAtStable`.-/
lemma votedForIn_monotonic
    (h1: sent ⊆ sent') : VotedForIn sent a v b → VotedForIn sent' a v b := by
  exact exists_mem_of_subset h1

/-- If no 2b message is added, then the value of `VotedForIn` stays the same. -/
lemma votedForIn_same_if_no_2b_added
    (h_mono: sent ⊆ sent')
    (hm: ∀ m ∈ sent' \ sent, ¬ is2b m) :
    VotedForIn sent a v b ↔ VotedForIn sent' a v b := by
  unfold VotedForIn at *
  constructor
  · exact exists_mem_of_subset h_mono
  · intro h2
    rcases h2 with ⟨m, hm_sent', hmatch⟩
    by_cases h_m_in_sent : m ∈ sent
    · exact ⟨m, h_m_in_sent, hmatch⟩
    · simp [*] at *
      exact False.elim (hm (Message.twob (some b) (some v) a) hm_sent' h_m_in_sent trivial)

/-- If no 2b message is added to `sent`, and the acceptor has not voted in a previous
ballot. Then it still has not voted in that ballot in `sent'`. -/
lemma votedForIn_same_if_no_2b_send
    (hsend : sent' = Send m sent)
    (hm : ¬ is2b m) : VotedForIn sent a v b ↔ VotedForIn sent' a v b := by
  have h_no_2b_added : ∀ m' ∈ sent' \ sent, ¬ is2b m' := by simp_all
  have h_mono : sent ⊆ sent' := send_monotonic hsend
  exact votedForIn_same_if_no_2b_added sent sent' h_mono h_no_2b_added

/-- If no 1b or 2b message is added, then the second invariant for 2b is stable. -/
lemma oneb_inv_2_stable_if_no_twob_added {maxVBal: Option Ballot} {b: Ballot} {a: Acceptor}
    (sent sent': Set Message)
    (h_mono: sent ⊆ sent')
    (h_no_2b_added: ∀ m ∈ sent' \ sent, ¬ is2b m) :
    (∀ (b' : Ballot), (b' ≥ (maxVBal + (1: Nat)) ∧ (b' < b))
          → ¬(∃ v : Value, VotedForIn sent a v b')) →
    (∀ (b' : Ballot), (b' ≥ (maxVBal + (1: Nat)) ∧ (b' < b))
          → ¬(∃ v : Value, VotedForIn sent' a v b')) := by
  intro h_not_voted_in_sent b' hle ⟨v, h_voted_in_sent'⟩
  have h_no_vote_in_sent_b' := h_not_voted_in_sent b' hle
  simp at h_no_vote_in_sent_b'
  exact h_no_vote_in_sent_b' v
          ((votedForIn_same_if_no_2b_added sent sent' h_mono h_no_2b_added).mpr
          h_voted_in_sent')

/-- If no 1b or 2b message is added, then `WontVoteIn` is stable. -/
lemma wontVoteIn_stable_if_no_1b2b_added
    (h_mono: sent ⊆ sent')
    (hm: ∀ m ∈ sent' \ sent, ¬ (is1b m ∨ is2b m)) :
    WontVoteIn sent a b → WontVoteIn sent' a b := by
  unfold WontVoteIn
  intro h_wontVoteIn_sent
  rcases h_wontVoteIn_sent with ⟨h_no_vote, h_exists_greater_ballot⟩
  constructor
  · intro v h_voted_in_sent'; specialize h_no_vote v
    have h_no_2b_added : ∀ m' ∈ sent' \ sent, ¬ is2b m' := by simp_all
    simp [@votedForIn_same_if_no_2b_added sent sent' a v b h_mono h_no_2b_added,
          h_voted_in_sent'] at h_no_vote
  · exact exists_mem_of_subset h_mono h_exists_greater_ballot

end Paxos.ExtraLemma
