import Paxos.Spec
import Paxos.Prop
import Paxos.ExtraLemma
--import Smt

namespace Paxos.Proof
open Paxos.Spec Paxos.Prop Paxos.ExtraLemma

variable (sent sent' : Set Message)
variable (Quorums : Set (Set Acceptor))

set_option maxHeartbeats 1000000      -- tactic 'simp' failed, nested error: (deterministic) timeout at `isDefEq`, maximum number of heartbeats (200000) has been reached Use `set_option maxHeartbeats <num>` to set the limit

lemma VotedInv (h1: MsgInv sent Quorums) : ∀ a, ∀ v, ∀ b, VotedForIn sent a v b → SafeAt sent Quorums v b := by
  unfold MsgInv VotedForIn at *
  intros a v b h; simp at h
  apply h1 at h; simp at h;
  apply h1 at h; simp at h
  exact h.left

lemma VotedOnce {a1 a2: Acceptor} {v1 v2: Value} {b: Ballot} (hInv: MsgInv sent Quorums) (h_voted_1: VotedForIn sent a1 v1 b) (h_voted_2 : VotedForIn sent a2 v2 b) : v1 = v2 := by
  unfold VotedForIn MsgInv at *
  have h_m_2a_1 : Message.twoa b v1 ∈ sent := by
    simp at h_voted_1; apply hInv at h_voted_1; simp at h_voted_1; exact h_voted_1
  apply hInv at h_m_2a_1; simp at h_m_2a_1
  have h_m_2a_2 : Message.twoa b v2 ∈ sent := by
    simp at h_voted_2; apply hInv at h_voted_2; simp at h_voted_2; exact h_voted_2
  apply h_m_2a_1.right at h_m_2a_2; simp at h_m_2a_2
  exact h_m_2a_2.symm

-- We get these for free since we've already proved the SafeAtStable, just need some refactoring. These are defined to be used in the proof of the inductiveness of invariants.
lemma SafeAtStable_Phase1a {b b': Ballot} {v: Value} (h1a: Phase1a sent sent' b') (hSafe: SafeAt sent Quorums v b): SafeAt sent' Quorums v b := by
  unfold SafeAt at *
  intro b2 hxb
  specialize hSafe b2 hxb
  rcases hSafe with ⟨Q, hQ, hProp⟩
  have hV : ∀ a ∈ Q, VotedForIn sent a v b2 → VotedForIn sent' a v b2 := by
    exact fun a a_1 a_2 ↦ votedForIn_monotonic sent sent' (send_monotonic h1a) a_2
  have hW : ∀ a ∈ Q, WontVoteIn sent a b2 → WontVoteIn sent' a b2 := by
    intro A hA hWont
    unfold WontVoteIn at *
    constructor
    · unfold Phase1a at h1a
      refine send_add_non_twob_preserves_no_vote sent sent' hWont.left h1a ?_
      refine Or.inl ?_
      exact exists_apply_eq_apply' Message.onea b'
    · exact exists_mem_of_subset (send_monotonic h1a) hWont.right
  use Q; constructor
  · exact hQ
  · intro A ha
    cases hProp A ha with
    | inl hVoted => left; exact hV A ha hVoted
    | inr hWont => right; exact hW A ha hWont

lemma SafeAtStable_Phase1b {a: Acceptor} {b: Ballot} {v: Value} (h1b: Phase1b sent sent' a) (hSafe: SafeAt sent Quorums v b): SafeAt sent' Quorums v b := by
  unfold SafeAt at *
  have h_sent_mono : sent ⊆ sent' := by exact phase1b_imp_mono_sent sent sent' h1b
  -- Goal: ∀ b2 < b, ∃ Q ∈ Quorums, ∀ a ∈ Q, VotedForIn sent' a v b2 ∨ WontVoteIn sent' a b2
  intro b2 hxb                                      -- intro `b2` and hxb : `b2 < b`
  specialize hSafe b2 hxb                           -- apply `b2` to `hSafe`
  rcases hSafe with ⟨Q, hQ, hAllVotedOrWontVote⟩    -- get the quorum that satisfies `hSafe`
  -- We prove such quorum `Q` satisfies `SafeAt` in `sent'`
  -- 1. Show that `VotedForIn` stays the same
  have hV : ∀ a ∈ Q, VotedForIn sent a v b2 → VotedForIn sent' a v b2 := by
    -- From the previous monotonic result for `VotedForIn`
    exact fun a a_1 a_2 ↦ votedForIn_monotonic sent sent' h_sent_mono a_2
  -- 2. Show that `WontVoteIn` stays the same
  have hW : ∀ a ∈ Q, WontVoteIn sent a b2 → WontVoteIn sent' a b2 := by
    intro A hA hWont
    unfold WontVoteIn at *
    constructor     -- `WontVoteIn` is a conjunction, we now prove each one
    · -- 1. Show that acceptor `A` has not voted for any value in ballot `b2`
      unfold Phase1b at h1b -- h1b: ∃ m ∈ sent, ∃ r ∈ max_prop sent a, ...
      rcases h1b with ⟨m, hmsent, r, hr, hmatch⟩
      cases m with
      | onea b1 =>
        cases r with
        | twob rbal rval a1 =>
          simp [-Send] at hmatch
          split_ifs at hmatch with hpos
          · refine send_add_non_twob_preserves_no_vote sent sent' hWont.left hmatch ?_
            refine Or.inr ?_; refine Or.inl ?_
            simp
          · simp [hmatch]; exact hWont.left
        | _ => simp at *;
      | _ => simp at *;
    · -- 2. Show that `A` will never vote
      exact exists_mem_of_subset h_sent_mono hWont.right
  -- Once we have `hV` and `hW` we can use `Q` to prove that `v` is safe at `b` for `sent'`
  use Q; constructor
  · exact hQ
  · -- Goal: ∀ a ∈ Q, VotedForIn sent' a v b2 ∨ WontVoteIn sent' a b2
    intro A ha
    specialize hAllVotedOrWontVote A ha
    specialize hV A ha
    cases hAllVotedOrWontVote with
    | inl hVotedInPrev => exact Or.inl (hV hVotedInPrev);
    | inr hWontVoteInPrev => exact Or.inr (hW A ha hWontVoteInPrev)

lemma SafeAtStable_Phase2a {b b': Ballot} {v: Value} (h2a: Phase2a Quorums sent sent' b') (hSafe: SafeAt sent Quorums v b): SafeAt sent' Quorums v b := by
  have h_sent_mono : sent ⊆ sent' := by exact phase2a_imp_mono_sent Quorums sent sent' h2a
  unfold SafeAt at *
  intro b2 hxb
  specialize hSafe b2 hxb
  rcases hSafe with ⟨Q, hQ, hProp⟩
  have hV : ∀ a ∈ Q, VotedForIn sent a v b2 → VotedForIn sent' a v b2 := by
    exact fun a a_1 a_2 ↦ votedForIn_monotonic sent sent' h_sent_mono a_2
  have hW : ∀ a ∈ Q, WontVoteIn sent a b2 → WontVoteIn sent' a b2 := by
    intro A hA hWont
    unfold WontVoteIn at *
    constructor
    · unfold Phase2a at h2a
      split_ifs at h2a
      · simp [h2a]; exact hWont.left
      · refine send_add_non_twob_preserves_no_vote sent sent' hWont.left h2a ?_
        refine Or.inr ?_; refine Or.inr ?_
        simp
      · simp [h2a]; exact hWont.left
    · exact exists_mem_of_subset h_sent_mono hWont.right
  use Q; constructor
  · exact hQ
  · intro A ha
    specialize hProp A ha         -- get rid of ∀ in hProp
    specialize hV A ha
    cases hProp with
    | inl hVotedInPrev => exact Or.inl (hV hVotedInPrev);
    | inr hWontVoteInPrev => exact Or.inr (hW A ha hWontVoteInPrev)

lemma SafeAtStable_Phase2b {a: Acceptor} {b: Ballot} {v: Value} (h2b: Phase2b sent sent' a) (hSafe: SafeAt sent Quorums v b): SafeAt sent' Quorums v b := by
    have h_sent_sub : sent ⊆ sent' := by exact phase2b_imp_mono_sent sent sent' h2b
    unfold SafeAt at *
    intro b2 hxb
    specialize hSafe b2 hxb
    rcases hSafe with ⟨Q, hQ, hProp⟩
    have hV : ∀ a ∈ Q, VotedForIn sent a v b2 → VotedForIn sent' a v b2 := by
      exact fun a a_1 a_2 ↦ votedForIn_monotonic sent sent' h_sent_sub a_2
    have hW : ∀ a ∈ Q, WontVoteIn sent a b2 → WontVoteIn sent' a b2 := by
      intro A hA hWont
      unfold WontVoteIn at *
      constructor
      · unfold Phase2b at h2b
        rcases h2b with ⟨m2a, hmsent, hmatch⟩
        let m2a_c := m2a
        cases m2a with
        | twoa b1 v1 =>
          simp [-Send] at hmatch
          split_ifs at hmatch with hpos
          · by_cases ha : a = A
            · have h_not_eq_bal : b2 ≠ b1 := by
                rcases hWont with ⟨_, ⟨m_1b_2b, hm_sent, hm_match⟩⟩
                let m_1b_2b_c := m_1b_2b
                cases m_1b_2b with
                | oneb bb _ _ a1  =>
                  simp at hm_match
                  specialize hpos m_1b_2b_c
                  simp [hm_sent, m_1b_2b_c]at hpos
                  simp [ha, hm_match] at hpos
                  exact ne_of_lt (lt_of_lt_of_le hm_match.right hpos)
                | twob bb _ a1 =>
                  simp at hm_match
                  specialize hpos m_1b_2b_c
                  simp [hm_sent, m_1b_2b_c]at hpos
                  simp [ha, hm_match] at hpos
                  match bb with
                  | none => exfalso; have h_false := hm_match.right
                            exact @Option.not_lt_none (Ballot) _ b2 h_false   -- Trick needed?
                  | some bb => exact ne_of_lt (lt_of_lt_of_le hm_match.right hpos)
                | _ => simp [*] at *
              intro V hVoted
              let hNotVotedPrev := hWont.left
              specialize hNotVotedPrev V
              unfold VotedForIn at hVoted hNotVotedPrev
              simp [*] at *; exact hNotVotedPrev hVoted
            · intro V hVoted
              let hNotVotedPrev := hWont.left
              specialize hNotVotedPrev V
              unfold VotedForIn at hVoted hNotVotedPrev
              simp [hmatch] at hVoted
              cases hVoted with
              | inl hVotedInPrev => simp [hVotedInPrev] at ha;
              | inr hVotedInPrev => simp [*] at *;
          · simp [hmatch]; exact hWont.left
        | _ => simp at *; simp [hmatch]; exact hWont.left
      · exact exists_mem_of_subset h_sent_sub hWont.right
    use Q; constructor
    · exact hQ
    · intro A ha
      specialize hProp A ha
      specialize hV A ha
      cases hProp with
      | inl hVotedInPrev => exact Or.inl (hV hVotedInPrev);
      | inr hWontVoteInPrev => exact Or.inr (hW A ha hWontVoteInPrev)

theorem SafeAtStable (hNext : Next Quorums sent sent')
                     (hSafe : SafeAt sent Quorums v b) : SafeAt sent' Quorums v b := by
  unfold Next at hNext
  rcases hNext with ⟨b, hPhase1a | hPhase2a⟩ | ⟨a, hPhase1b | hPhase2b⟩
  · exact SafeAtStable_Phase1a sent sent' Quorums hPhase1a hSafe
  · exact SafeAtStable_Phase2a sent sent' Quorums hPhase2a hSafe
  · exact SafeAtStable_Phase1b sent sent' Quorums hPhase1b hSafe
  · exact SafeAtStable_Phase2b sent sent' Quorums hPhase2b hSafe

theorem MsgInv_implies_Consistency (hInv : MsgInv sent Quorums) : Consistency sent Quorums := by
  unfold Consistency
  rintro v1 v2 ⟨⟨b1, hChosenIn1⟩, ⟨b2, hChosenIn2⟩⟩
  -- We prove the following symmetrical result for it to be used later in the proof
  have Consistent_ChosenIn_Diff_Bal (b1: Ballot) (v1: Value) (b2: Ballot) (v2: Value) (hChosenIn1: ChosenIn sent Quorums v1 b1) (hChosenIn2: ChosenIn sent Quorums v2 b2) (h_ls: b1 < b2) : v1 = v2 := by
      have h_safe_b2 : SafeAt sent Quorums v2 b2 := by
        -- By VotedInv, QuorumAssumption DEF ChosenIn, Inv
        unfold ChosenIn at hChosenIn2
        rcases hChosenIn2 with ⟨Q2, hQ2, hVotedQ2⟩
        have ⟨aa, haa⟩ := pick_from_quorum_int Quorums hQ2 hQ2
        refine VotedInv sent Quorums hInv ?a v2 b2 ?_
        · exact aa
        · specialize hVotedQ2 aa; exact (hVotedQ2 haa.left)
      unfold SafeAt at h_safe_b2
      specialize h_safe_b2 b1
      have hsb1 := h_safe_b2 h_ls
      rcases hsb1 with ⟨Q1, hQ1, hqsb1⟩
      unfold ChosenIn at hChosenIn1
      rcases hChosenIn1 with ⟨Q2, hQ2, hvotedin1⟩
      have ⟨aa, haa⟩ := pick_from_quorum_int Quorums hQ1 hQ2
      have haa_voted_v1_b1 : VotedForIn sent aa v1 b1 := by exact hvotedin1 aa haa.right
      have haa_safe_b1 : VotedForIn sent aa v2 b1 ∨ WontVoteIn sent aa b1 := by exact hqsb1 aa haa.left
      cases haa_safe_b1 with
      | inl haa_voted_v2_b1 => exact VotedOnce sent Quorums hInv haa_voted_v1_b1 haa_voted_v2_b1
      | inr haa_wont_vote_b1 =>
        unfold WontVoteIn at haa_wont_vote_b1
        rcases haa_wont_vote_b1 with ⟨haa_not_vote_b1, _⟩
        exact (haa_not_vote_b1 v1 haa_voted_v1_b1).elim
  by_cases h_eq : b1 = b2
  · unfold ChosenIn at *
    rcases hChosenIn1 with ⟨Q1, hQ1, hProp1⟩
    rcases hChosenIn2 with ⟨Q2, hQ2, hProp2⟩
    have ⟨aa, haa⟩ := pick_from_quorum_int Quorums hQ1 hQ2
    specialize hProp1 aa
    specialize hProp2 aa
    have hv1 := hProp1 (And.left haa); have hv2 := hProp2 (And.right haa)
    rw [←h_eq] at hv2
    exact VotedOnce sent Quorums hInv hv1 hv2
  by_cases h_lt: b1 < b2
  · exact Consistent_ChosenIn_Diff_Bal b1 v1 b2 v2 hChosenIn1 hChosenIn2 h_lt
  · have h_nlt: b2 < b1 := by
      have h_total := lt_trichotomy b1 b2
      rcases h_total with (h_total_left | h_total_mid | h_total_r) <;> simp [*] at *
    exact id (Consistent_ChosenIn_Diff_Bal b2 v2 b1 v1 hChosenIn2 hChosenIn1 h_nlt).symm

-- Effort: 1h
lemma ind_phase1a {b: Ballot} (hInv: MsgInv sent Quorums) (h1a: Phase1a sent sent' b) : MsgInv sent' Quorums := by
  have h_subset : sent ⊆ sent' := by
    unfold Phase1a at h1a
    exact send_monotonic h1a
  have h1a_copy := h1a
  unfold Phase1a at h1a; unfold MsgInv at *
  rw [h1a]
  intro m h_m_in_sent'
  by_cases h_m_eq_onea_msg : m = Message.onea b
  · simp [*] at *
  · have h_m_in_sent : m ∈ sent := by simp [h_m_eq_onea_msg] at h_m_in_sent'; exact h_m_in_sent'
    specialize hInv m h_m_in_sent
    cases m with
    | onea b1 => simp
    | oneb b1 maxVBal maxVal a1 =>
      simp at hInv; simp [-Send]
      match maxVBal, maxVal with
      | some maxVBal, some maxVal =>
        simp [-Send]; simp at hInv
        refine And.intro ?_ ?_
        · rw [←h1a]
          exact votedForIn_monotonic sent sent' h_subset hInv.left
        · intro b' hb_lower hb_upper
          have h_not_voted := hInv.right
          specialize h_not_voted b'
          simp [hb_lower, hb_upper] at h_not_voted
          rw [←h1a]
          refine send_add_non_twob_preserves_no_vote sent sent' h_not_voted h1a ?_
          simp;
      | none, some maxVal | some maxVBal, none => simp at hInv;
      | none, none =>
        simp [-Send]; simp at hInv;
        intro b' hb_lower
        have h_not_voted := hInv
        specialize h_not_voted b'
        simp [hb_lower] at h_not_voted
        rw [←h1a]
        refine send_add_non_twob_preserves_no_vote sent sent' h_not_voted h1a ?_
        simp;
    | twoa b1 v1 =>
      simp at hInv; simp [-Send]
      rw [←h1a]
      refine And.intro ?_ ?_
      · exact SafeAtStable_Phase1a sent sent' Quorums h1a_copy hInv.left
      · have h_inv_right := hInv.right
        intro m2 h_m2_in_sent'
        specialize h_inv_right m2
        cases m2 <;> simp [*] at * ; apply h_inv_right at h_m2_in_sent' ; exact h_m2_in_sent'
    | twob b1 v1 a1 =>
      match b1, v1 with
      | some b1, some v1 => simp [hInv]
      | none, some v1 | some b1, none | none, none => simp;

-- Effort: 5m (Writing down the skeleton, not yet to prove the main one)
-- 30m: trying to figure out how to get rid of the universal quantifier in MsgInv.
-- 2hr: finish the rest of the proof. including proving two lemmas: max_prop_not_empty_implies_voted_for, and max_prop_implies_not_voted_for_greater_ballots

/--
how to prove this? Spent about an hour proving this lemma
hr : Message.twob rbal (some rvbal) racc ∈ max_prop sent a
hmatch : sent' = Send (Message.oneb mbal rbal (some rvbal) a) sent
h_m_eq_oneb : m' = Message.oneb mbal rbal (some rvbal) a
⊢ ∀ (b' : Ballot), rbal + 1 ≤ b' → b' ≤ mbal - 1 → ∀ (x : Value), ¬VotedForIn sent' a x b'
-/
lemma ind_phase1b {a: Acceptor} (hInv: MsgInv sent Quorums) (h1b: Phase1b sent sent' a) : MsgInv sent' Quorums := by
  have h1b_copy := h1b
  rcases h1b with ⟨m, hmsent, r, hr, hmatch⟩
  cases m with
  | onea mbal =>
    cases r with
    | twob rbal rval racc =>
      have h_same_accptor : a = racc := by
        have h_exists_b_v_with_same_acceptor := mem_max_prop_is_twob sent hr
        simp [*] at *
        exact id (Eq.symm h_exists_b_v_with_same_acceptor)
      simp [-Send] at hmatch
      split_ifs at hmatch with hpos
      · -- Here we are proving the oneb case
        have l1 : ∀ a v b, VotedForIn sent a v b ↔ VotedForIn sent' a v b := by
          intro a v b
          unfold VotedForIn
          simp [hmatch]
        have h_subset : sent ⊆ sent' := by exact send_monotonic hmatch
        unfold MsgInv at hInv; unfold MsgInv
        have h_exists_b_v_with_same_acceptor := mem_max_prop_is_twob sent hr
        intro m' hm'
        by_cases h_m_eq_oneb : m' = Message.oneb mbal rbal rval a  -- m' is the witness message sent
        · simp [h_m_eq_oneb]
          match rbal, rval with
          | some rbal, none | none, some rval => simp; unfold Phase1b at h1b_copy; rw [h_same_accptor] at hr; apply max_prop_empty_ballot_iff_empty_value at hr; simp at hr
          | none, none =>
            simp
            rw [←h_same_accptor] at hr
            intro b hb_upper
            have h_not_voted_in_sent := max_prop_empty_implies_not_voted_in_prev_ballots sent hr b
            -- The following line suggested by apply?
            exact fun x ↦ (fun {a b} ha ↦ (iff_false_left ha).mp) (h_not_voted_in_sent x) (l1 a x b)
          | some rbal, some rval =>
            simp
            constructor
            · refine votedForIn_monotonic sent sent' h_subset ?_    -- use refine, and we are just trying to prove that a voted in sent, which can be derived from max_prop
              rw [h_same_accptor] at *
              exact max_prop_not_empty_implies_voted_for sent hr
            · have h_not_voted_for_greater_ballots : ∀ (b' : Ballot), rbal + 1 ≤ b' → b' < mbal → ∀ (x : Value), ¬VotedForIn sent a x b' := by
                rw [h_same_accptor] at hr
                have h_not_voted_for_greater_ballots := max_prop_implies_not_voted_for_greater_ballots sent hr
                intro b' hb_lower hb_upper x
                specialize h_not_voted_for_greater_ballots b' x hb_lower
                simp [h_same_accptor]; exact h_not_voted_for_greater_ballots
              exact fun b' a_1 a_2 x ↦        -- This is from "apply?" I think the goal is clear enough but simp [h_not_voted_for_greater_ballots, l1] didn't work. TODO: make this more readble
                (fun {a b} ha ↦ (iff_false_left ha).mp)
                  (h_not_voted_for_greater_ballots b' a_1 a_2 x) (l1 a x b')
        · have h_m'_in_sent : m' ∈ sent := by simp [*] at * ; simp [h_m_eq_oneb] at hm' ; exact hm'    -- TODO: This part is repetitive, as I copied this from the 1a case and just changes a few things. How to get rid of this repetition?
          cases hm' : m' with
          | onea b1 => simp
          | oneb b1 maxVBal maxVal a1 =>
            simp at hInv; simp [-Send]
            match maxVBal, maxVal with
            | none, none =>
              simp
              specialize hInv m' h_m'_in_sent; simp [hm'] at hInv;
              exact fun b' a x ↦ (fun {a b} ha ↦ (iff_false_left ha).mp) (hInv b' a x) (l1 a1 x b')
            | some maxVBal, none | none, some maxVal =>
              simp;
              specialize hInv m' h_m'_in_sent
              simp [hm'] at hInv;
            | some maxVBal, some maxVal =>
              simp [-Send]; specialize hInv m' h_m'_in_sent; simp [hm'] at hInv
              refine And.intro ?_ ?_
              · rw [←l1]; exact hInv.left
              · intro b' hb_lower hb_upper x
                have h_not_voted := hInv.right
                specialize h_not_voted b'
                simp [hb_lower, hb_upper] at h_not_voted
                specialize h_not_voted x
                unfold VotedForIn at *
                simp [hmatch]; simp at h_not_voted; exact h_not_voted
          | twoa b1 v1 =>
            simp at hInv; simp [-Send]
            specialize hInv m' h_m'_in_sent; simp [hm'] at hInv
            refine And.intro ?_ ?_
            · exact SafeAtStable_Phase1b sent sent' Quorums h1b_copy hInv.left
            · have h_inv_right := hInv.right
              intro m2 h_m2_in_sent'
              specialize h_inv_right m2
              cases m2 <;> simp [*] at *; apply h_inv_right at h_m2_in_sent' ; exact h_m2_in_sent'
          | twob b1 v1 a1 =>
            match b1, v1 with
            | none, none => simp;
            | some b1, some v1 => simp; specialize hInv m' h_m'_in_sent; simp [hm'] at hInv; exact h_subset hInv
            | some b1, none | none, some v1 => simp;
      · rw [hmatch]; exact hInv
    | _ => simp [*] at *
  | _ => simp [*] at *
-- Effort: 1h30m, taking care of some chores with Phase 2a.
-- Effort: 10hr trying to prove the inductiveness. Also make changes to the Spec and MsgInv.
lemma ind_phase2a {b: Ballot} (hInv: MsgInv sent Quorums) (h2a: Phase2a Quorums sent sent' b) : MsgInv sent' Quorums := by
  have h2a_copy := h2a
  unfold Phase2a at h2a
  split_ifs at h2a with h_exist_prev_2a_msg h_no_prev_2a_msg
  · simp [hInv, h2a]
  · let v := Classical.choose h_no_prev_2a_msg                -- This line is suggested by chatGPT
    have h_send : sent' = Send (Message.twoa b v) sent := by  -- after the previous line, we can get the send relation
      simpa [v] using h2a
    have h_subset : sent ⊆ sent' := by exact send_monotonic h_send
    unfold MsgInv at hInv; unfold MsgInv
    intro m' hm_sent'
    have l1 : ∀ a v b, VotedForIn sent a v b ↔ VotedForIn sent' a v b := by
      intro a v b
      unfold VotedForIn
      simp [h2a]
    by_cases h_m_eq_t2a : m' = Message.twoa b v
    · simp [h_m_eq_t2a]
      constructor
      · -- Proving SafeAt
        have h_safe_at_prev : SafeAt sent Quorums v b := by         -- Proving SafeAt sent, and use SafeAtStable
          rcases Classical.choose_spec h_no_prev_2a_msg with ⟨Q, S, ⟨h_Q_in_quorums, h_S_set_of_oneb, h_all_acc_in_Q_sent_oneb, h_all_not_voted_or_some_voted⟩⟩
          cases' h_all_not_voted_or_some_voted with h_none_voted h_some_voted
          · unfold SafeAt             -- this case, every acceptor in S has not voted in the past
            -- after unfolding SafeAt, we try to show
            -- ∀ b2 < b, ∃ Q ∈ Quorums, ∀ a ∈ Q, VotedForIn sent a v b2 ∨ WontVoteIn sent a b2
            intro b2 h_b2_less_than_b
            use Q; simp [h_Q_in_quorums]
            intro a haQ       -- proving a disjunction VotedForIn sent a v b2 ∨ WontVoteIn sent a b2
            right             -- since we know none voted, we are proving the right part, which is WontVoteIn sent a b2
            have ⟨m1, hm1S, hm1_match⟩ := h_all_acc_in_Q_sent_oneb a haQ
            unfold WontVoteIn
            constructor
            · cases m1 with
              | oneb bal1 maxVBal1 maxVal1 acc1 =>
                let m1 := Message.oneb bal1 maxVBal1 maxVal1 acc1     -- TODO: get rid of renaming of m1, and ust the h_m1.
                have h_m1_in_sent : m1 ∈ sent := by exact Set.mem_of_mem_inter_left (h_S_set_of_oneb hm1S)
                have bal1_eq : bal1 = b := by
                  rcases h_S_set_of_oneb hm1S with ⟨_, h_match_m1_eq_b⟩
                  simp [h_match_m1_eq_b]
                simp at hm1_match
                specialize h_none_voted m1 hm1S
                simp [m1] at h_none_voted
                have h_target := hInv
                specialize h_target m1 h_m1_in_sent
                simp [m1] at h_target
                have h_target := h_target.right
                specialize h_target b2
                simp [h_none_voted, h_b2_less_than_b, bal1_eq, hm1_match] at h_target; exact h_target
              | _ => simp at hm1_match;
            · cases m1 with
              | oneb bal1 maxVBal1 maxVal1 acc1 =>
                let m1 := Message.oneb bal1 maxVBal1 maxVal1 acc1
                have h_m1_in_sent : m1 ∈ sent := by exact Set.mem_of_mem_inter_left (h_S_set_of_oneb hm1S)
                have bal1_eq : bal1 = b := by
                  rcases h_S_set_of_oneb hm1S with ⟨_, h_match_m1_eq_b⟩
                  simp [h_match_m1_eq_b]
                use m1, h_m1_in_sent; simp [m1]
                simp [hm1_match, bal1_eq, h_b2_less_than_b]
              | _ => simp at hm1_match;
          · unfold SafeAt
            intro b2 h_b2_less_than_b
            obtain ⟨c, h_c_greater_than_zero, h_c_less_than_b, ⟨h_all_messgae_in_S_less_than_c, h_some_message_in_S_equals_C⟩⟩ := h_some_voted
            by_cases h_b2_less_than_c : b2 < c
            · obtain ⟨m_with_ballot_c, h_m_c_in_S, h_m_c_match⟩ := h_some_message_in_S_equals_C
              cases m_with_ballot_c with
              | oneb bal_c mc_vbal mc_val mc_acc =>
                match mc_vbal, mc_val with
                | some mc_vbal, some mc_val =>
                  let mc := Message.oneb bal_c mc_vbal mc_val mc_acc
                  have ⟨mc_in_sent, _⟩ := h_S_set_of_oneb h_m_c_in_S
                  have hInv_2b := hInv mc mc_in_sent
                  -- specialize hInv mc mc_in_sent
                  simp [mc] at hInv_2b
                  simp at h_m_c_match
                  simp [h_m_c_match] at hInv_2b
                  have h_safe_at_c : SafeAt sent Quorums mc_val mc_vbal := by
                    have h_voted_acc : VotedForIn sent mc_acc mc_val mc_vbal := by
                      simp [h_m_c_match, hInv_2b.left]
                    exact VotedInv sent Quorums hInv mc_acc mc_val mc_vbal h_voted_acc
                  unfold SafeAt at h_safe_at_c
                  rw [h_m_c_match.left, h_m_c_match.right] at h_safe_at_c
                  specialize h_safe_at_c b2 h_b2_less_than_c
                  simp [h_safe_at_c, v]
                | none, some mc_val => simp at h_m_c_match;
                | some mc_vbal, none => simp at h_m_c_match;
                | none, none => simp at h_m_c_match;
              | _ => simp at h_m_c_match;
            · by_cases h_b2_eq_c : b2 = c
              · obtain ⟨m_with_ballot_c, h_m_c_in_S, h_m_c_match⟩ := h_some_message_in_S_equals_C
                cases m_with_ballot_c with
                | oneb bal_c mc_vbal mc_val mc_acc =>
                  match mc_vbal, mc_val with
                  | some mc_vbal, some mc_val =>
                    let mc := Message.oneb bal_c mc_vbal mc_val mc_acc
                    have h_vbal_eq_c : mc_vbal = c := by
                      simp at h_m_c_match
                      exact h_m_c_match.left
                    have h_mc_val_eq_v : mc_val = v := by
                      simp at h_m_c_match
                      simp [h_m_c_match.right, v]
                   -- Obtain the following from the MsgInv for 1b message
                    have h_voted_acc_c : VotedForIn sent mc_acc mc_val mc_vbal := by
                      have ⟨mc_in_sent, _⟩ := h_S_set_of_oneb h_m_c_in_S
                      have h_inv_mc := hInv mc mc_in_sent
                      simp [mc] at h_inv_mc
                      exact h_inv_mc.left
                    rw [h_vbal_eq_c, h_mc_val_eq_v] at h_voted_acc_c
                    have h_all_voted_in_c_for_v : ∀ q ∈ Q, ∀ (w: Value), VotedForIn sent q w c → w = v := by
                      intro q h_q_in_Q w h_voted
                      exact VotedOnce sent Quorums hInv h_voted h_voted_acc_c
                    use Q; simp [h_Q_in_quorums]
                    intro a haQ
                    -- The following shows that either a has voted for v in c, or it won't vote in c.
                    by_cases h_a_voted_in_c : VotedForIn sent a v c     -- If a has voted for v in c, we are done
                    · left
                      simp [h_b2_eq_c, h_a_voted_in_c]
                    · right -- If a has not voted for v in c, we show that it won't vote in c because
                      unfold WontVoteIn
                      constructor
                      · intro w h_voted    -- 1. It could not have voted for any other value in c
                        rw [h_b2_eq_c] at h_voted
                        have h_voted_eq_v := h_all_voted_in_c_for_v a haQ w h_voted
                        rw [h_voted_eq_v] at h_voted
                        exact h_a_voted_in_c h_voted
                      · specialize h_all_acc_in_Q_sent_oneb a haQ    -- 2. It has a 1b message with higher ballot than c
                        obtain ⟨m2, hm2S, hm2_match⟩ := h_all_acc_in_Q_sent_oneb
                        cases m2 with
                        | oneb bal2 maxVBal2 maxVal2 acc2 =>
                          simp at hm2_match
                          have h123 := h_S_set_of_oneb hm2S
                          simp at h123
                          have h_m2_in_sent := h123.left
                          use Message.oneb bal2 maxVBal2 maxVal2 acc2
                          simp only [h_m2_in_sent]
                          simp [h123.2, hm2_match, h_b2_less_than_b]
                        | _ => simp at hm2_match;
                | _ => simp at h_m_c_match;
              · have h_b2_greater_than_c : c < b2 := by
                  have h_total := lt_trichotomy c b2
                  rcases h_total with (h_total_left | h_total_mid | h_total_r)
                  · exact h_total_left
                  · simp [h_total_mid] at h_b2_eq_c
                  · simp [h_total_r] at h_b2_less_than_c
                have h_safe_at_c : SafeAt sent Quorums v c := by
                  obtain ⟨m1, hm1S, hm1_match⟩ := h_some_message_in_S_equals_C
                  cases m1 with
                  | oneb bal1 maxVBal1 maxVal1 acc1 =>
                    simp at hm1_match
                    have h_acc_voted : VotedForIn sent acc1 v c := by
                      have h_m1_in_sent := (h_S_set_of_oneb hm1S).left
                      specialize hInv (Message.oneb bal1 maxVBal1 maxVal1 acc1) h_m1_in_sent
                      simp at hInv
                      rw [hm1_match.left, hm1_match.right] at hInv
                      simp at hInv
                      simp [hInv.left, v]
                    exact VotedInv sent Quorums hInv acc1 v c h_acc_voted
                  | _ => simp at hm1_match;
                use Q; simp [h_Q_in_quorums]
                intro a haQ
                right
                constructor
                · specialize h_all_acc_in_Q_sent_oneb a haQ
                  obtain ⟨m2, hm2S, hm2_match⟩ := h_all_acc_in_Q_sent_oneb
                  have hm2_sent := (h_S_set_of_oneb hm2S).1
                  cases h_case_m2: m2 with
                  | oneb bal2 maxVBal2 maxVal2 acc2 =>
                    have acc_eq : acc2 = a := by simpa [h_case_m2] using hm2_match
                    specialize hInv m2 hm2_sent
                    simp [h_case_m2] at hInv
                    rcases hInv with ⟨_, h_lim⟩
                    have no_ex : ∀ x, ¬VotedForIn sent acc2 x b2 := by
                      specialize h_lim b2
                      specialize h_all_messgae_in_S_less_than_c m2 hm2S
                      simp [h_case_m2] at h_all_messgae_in_S_less_than_c
                      have h_lower : maxVBal2 + (1 : Ballot) ≤ some b2 := by
                        cases maxVBal2 with
                        | none => simp;
                        | some maxVBal2 =>
                          exact option.some_succ_le_some_of_some_le_and_lt h_all_messgae_in_S_less_than_c h_b2_greater_than_c
                      have h_upper : b2 < bal2 := by
                        rcases h_S_set_of_oneb hm2S with ⟨_, h_m2_match_bal_eq_b⟩
                        simp [h_case_m2] at h_m2_match_bal_eq_b
                        -- refine Nat.le_sub_one_of_lt ?_
                        simp only [h_m2_match_bal_eq_b, h_b2_less_than_b]
                      exact (h_lim h_lower h_upper)
                    rw [acc_eq] at no_ex; exact no_ex
                  | _ => simp [h_case_m2] at hm2_match;
                · specialize h_all_acc_in_Q_sent_oneb a haQ    -- 2. It has a 1b message with higher ballot than c
                  obtain ⟨m2, hm2S, hm2_match⟩ := h_all_acc_in_Q_sent_oneb
                  cases m2 with
                  | oneb bal2 maxVBal2 maxVal2 acc2 =>
                    simp at hm2_match
                    have h123 := h_S_set_of_oneb hm2S
                    simp at h123
                    have h_m2_in_sent := h123.left
                    use Message.oneb bal2 maxVBal2 maxVal2 acc2
                    simp only [h_m2_in_sent]
                    simp [h123.2, hm2_match, h_b2_less_than_b]
                  | _ => exfalso; simp at hm2_match;
        exact SafeAtStable_Phase2a sent sent' Quorums h2a_copy h_safe_at_prev
      · intro m2 h_m2_in_sent'
        by_cases h_m2_in_sent : m2 ∈ sent
        · cases h_m2 : m2 with
          | twoa bal2 val2 =>
            simp
            intro h_bal2_eq_b
            have ex : ∃ m ∈ sent, match m with
              | Message.twoa b' val => b' = b
              | _                   => False :=
              ⟨m2, h_m2_in_sent, by simp [h_m2, h_bal2_eq_b]⟩
            exact False.elim (h_exist_prev_2a_msg ex)
          | _ => simp
        · have h_m2_eq_t2a : m2 = Message.twoa b v := by
            unfold Send at h_send
            simp [h_send] at h_m2_in_sent'
            simp [h_m2_in_sent] at h_m2_in_sent'; exact h_m2_in_sent'
          simp [h_m2_eq_t2a]
    · simp [h_send, h_m_eq_t2a] at hm_sent'
      cases hm' : m' with
      | onea b1 => simp
      | oneb b1 maxVBal maxVal a1 =>
        simp at hInv; simp [-Send]
        match maxVBal, maxVal with
        | none, none =>
          simp
          specialize hInv m' hm_sent'; simp [hm'] at hInv;
          exact fun b' a x ↦ (fun {a b} ha ↦ (iff_false_left ha).mp) (hInv b' a x) (l1 a1 x b')
        | some maxVBal, none | none, some maxVal =>
          simp;
          specialize hInv m' hm_sent'; simp [hm'] at hInv
        | some maxVBal, some maxVal =>
          simp [-Send]; specialize hInv m' hm_sent'; simp [hm'] at hInv
          constructor
          · exact votedForIn_monotonic sent sent' h_subset hInv.left
          · intro b' hb_lower hb_upper x
            have h_not_voted := hInv.right
            specialize h_not_voted b'
            simp [hb_lower, hb_upper] at h_not_voted
            specialize h_not_voted x
            unfold VotedForIn at *
            simpa [h_send] using h_not_voted
      | twoa b1 v1 =>   -- For 2a message in sent
        simp at hInv; simp [-Send]
        specialize hInv m' hm_sent'; simp [hm'] at hInv
        refine And.intro ?_ ?_
        · exact SafeAtStable_Phase2a sent sent' Quorums h2a_copy hInv.left
        · have h_inv_right := hInv.right
          intro m2 h_m2_in_sent'
          specialize h_inv_right m2
          cases m2 with
          | twoa b1' v1' =>
            simp;
            intro h_same_ballot_b1_b1'
            simp [h_same_ballot_b1_b1']
            by_cases h_m2_in_sent : Message.twoa b1' v1' ∈ sent
            · simp [h_m2_in_sent] at h_inv_right
              simp [h_inv_right, h_same_ballot_b1_b1']
            · unfold Send at h2a;
              have h_b1_eq_b_and_v1_eq_v : Message.twoa b1' v1' = Message.twoa b v := by
                simp [h_send] at h_m2_in_sent'
                rcases h_m2_in_sent' with (h_eq | h1)
                · simp [h_eq]
                · exact False.elim (h_m2_in_sent h1)
              simp at h_b1_eq_b_and_v1_eq_v
              simp [*] at *
              exfalso
              specialize h_exist_prev_2a_msg m'; simp [hm', hm_sent'] at h_exist_prev_2a_msg; exact h_exist_prev_2a_msg h_b1_eq_b_and_v1_eq_v.left
          | _ => simp;
          -- cases m2 <;> simp [*] at * ; apply h_inv_right at h_m2_in_sent' ; exact h_m2_in_sent' -- -- tactic 'simp' failed, nested error: (deterministic) timeout at `isDefEq`, maximum number of heartbeats (200000) has been reached Use `set_option maxHeartbeats <num>` to set the limit
      | twob b1 v1 a1 =>
        match b1, v1 with
        | none, none => simp;
        | some b1, some v1 => simp; specialize hInv m' hm_sent'; simp [hm'] at hInv; exact h_subset hInv
        | some b1, none | none, some v1 => simp;
  · simp [hInv, h2a]

-- Effort: 30m, pending on the proof for m' being a 1b message
-- Effort: 30m on the proof for m' being a 2a message, chatGPT helped.
-- Total Effort: 1h
lemma ind_phase2b {a: Acceptor} (hInv: MsgInv sent Quorums) (h2b: Phase2b sent sent' a) : MsgInv sent' Quorums := by
  have h2b_copy := h2b
  unfold Phase2b at h2b
  rcases h2b with ⟨m2a, h_2a_sent, hmatch⟩
  cases m2a with
  | twoa b v =>
    simp [-Send] at hmatch
    split_ifs at hmatch with hpo
    · have h_subset : sent ⊆ sent' := by exact send_monotonic hmatch
      unfold MsgInv at *
      intro m' hm_sent'
      by_cases h_m'_in_sent : m' ∈ sent
      · cases hm': m' with
          | onea b1 => simp
          | oneb b1 maxVBal maxVal a1 =>
            simp at hInv; simp [-Send]
            match maxVBal, maxVal with
            | none, none =>
              simp; specialize hInv m' h_m'_in_sent; simp [hm'] at hInv;  -- TODO: Need to show the new 2b message has no impact on previous ballots.
              intro b' hb_lower x
              have h_not_voted := hInv
              specialize h_not_voted b'
              simp [hb_lower] at h_not_voted
              specialize h_not_voted x
              unfold VotedForIn at *
              simp [hmatch]; simp at h_not_voted
              constructor
              · intro hb_eq hv_eq ha_eq
                have h_inv_right := hInv
                specialize h_inv_right b' hb_lower x
                specialize hpo m' h_m'_in_sent; simp [hm'] at hpo
                have h_b1_le_b : b1 ≤ b := hpo ha_eq
                have hf : b1 < b1 := by rw [hb_eq] at hb_lower; exact Nat.lt_of_le_of_lt (hpo ha_eq) hb_lower
                simp at hf
              · exact h_not_voted
            | some maxVBal, none | none, some maxVal => simp; specialize hInv m' h_m'_in_sent; simp [hm'] at hInv
            | some maxVBal, some maxVal =>
              simp [-Send]; specialize hInv m' h_m'_in_sent; simp [hm'] at hInv
              constructor
              · exact votedForIn_monotonic sent sent' h_subset hInv.left
              · intro b' hb_lower hb_upper x
                have h_not_voted := hInv.right
                specialize h_not_voted b'
                simp [hb_lower, hb_upper] at h_not_voted
                specialize h_not_voted x
                unfold VotedForIn at *
                simp [hmatch]; simp at h_not_voted
                constructor
                · intro hb_eq hv_eq ha_eq
                  -- simp [hb_eq, hv_eq, ha_eq] at *
                  have h_inv_right := hInv.right
                  specialize h_inv_right b' hb_lower hb_upper x
                  specialize hpo m' h_m'_in_sent; simp [hm'] at hpo
                  have h_b1_le_b : b1 ≤ b := hpo ha_eq
                  rw [hb_eq] at hb_upper
                  have hf : b1 < b1 := by exact Nat.lt_of_le_of_lt (hpo ha_eq) hb_upper
                  simp at hf
                  -- simp [h_b_le_b1_1, h_b1_le_b]
                · exact h_not_voted
          | twoa b1 v1 =>
            simp at hInv; simp [-Send]
            specialize hInv m' h_m'_in_sent; simp [hm'] at hInv
            refine And.intro ?_ ?_
            · exact SafeAtStable_Phase2b sent sent' Quorums h2b_copy hInv.left
            · have h_inv_right := hInv.right
              intro m2 h_m2_in_sent'
              specialize h_inv_right m2
              cases m2 <;> simp [*] at * ; apply h_inv_right at h_m2_in_sent' ; exact h_m2_in_sent'
          | twob b1 v1 a1 =>
            match b1, v1 with
            | none, none => simp;
            | some b1, some v1 => simp; specialize hInv m' h_m'_in_sent; simp [hm'] at hInv; exact h_subset hInv
            | some b1, none | none, some v1 => simp;
      · have m'_eq_twob : m' = Message.twob b v a := by simp [*] at *; exact hm_sent'
        simp [m'_eq_twob]
        exact h_subset h_2a_sent
    · simp [*] at *
  | _ => simp [*] at *

theorem Inductiveness (hInv: MsgInv sent Quorums) (hNext: Next Quorums sent sent') : MsgInv sent' Quorums := by
  unfold Next at hNext
  rcases hNext with ⟨b, hPhase1a | hPhase2a⟩ | ⟨a, hPhase1b | hPhase2b⟩
  · exact ind_phase1a sent sent' Quorums hInv hPhase1a
  · exact ind_phase2a sent sent' Quorums hInv hPhase2a
  · exact ind_phase1b sent sent' Quorums hInv hPhase1b
  · exact ind_phase2b sent sent' Quorums hInv hPhase2b

-- THEOREM Consistent == Spec => []Consistency in TLAPS
theorem Consistent (σ : ℕ → Set Message) (hSpec : PaxosSpec Quorums σ) : ∀ n, Consistency (σ n) Quorums := by
  have inv : ∀ n, MsgInv (σ n) Quorums := by
    intro n
    induction n with
    | zero   =>
      unfold PaxosSpec Init at hSpec;
      simp [MsgInv, hSpec.1]
    | succ k ih =>
      let sent := σ k; let sent' := σ (k + 1)
      unfold PaxosSpec at hSpec
      have hStep := hSpec.2 k
      cases hStep with
      | inl hNext =>
        have hInvHoldsPrev: MsgInv sent Quorums := ih
        exact Inductiveness (σ k) (σ (k + 1)) Quorums ih hNext
      | inr hStutter =>
        simp [hStutter] at ih; exact ih;
  intro n
  exact MsgInv_implies_Consistency (σ n) Quorums (inv n)

end Paxos.Proof
