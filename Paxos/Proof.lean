import Paxos.Spec
import Paxos.Prop
import Paxos.ExtraLemma
--import Smt

open Paxos.Spec Paxos.Prop Paxos.ExtraLemma

variable (sent sent' : Set Message)
variable (Quorums : Set (Set Acceptor))

lemma VotedInv (h1: MsgInv sent Quorums) : ∀ a, ∀ v, ∀ b, VotedForIn sent a v b → SafeAt sent Quorums v b := by
  unfold MsgInv VotedForIn at *
  intros a v b h; simp at h
  apply h1 at h; simp at h
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
lemma SafeAtStable_Phase1a {b b': Ballot} {v: Value} (h1a: Phase1a sent sent' b') (hSafe: SafeAt sent Quorums v b): SafeAt sent' Quorums v b := by sorry

lemma SafeAtStable_Phase1b {a: Acceptor} {b: Ballot} {v: Value} (h1b: Phase1b sent sent' a) (hSafe: SafeAt sent Quorums v b): SafeAt sent' Quorums v b := by sorry

lemma SafeAtStable_Phase2a {b b': Ballot} {v: Value} (h2a: Phase2a Quorums sent sent' b') (hSafe: SafeAt sent Quorums v b): SafeAt sent' Quorums v b := by sorry

lemma SafeAtStable_Phase2b {a: Acceptor} {b: Ballot} {v: Value} (h2b: Phase2b sent sent' a) (hSafe: SafeAt sent Quorums v b): SafeAt sent' Quorums v b := by sorry

theorem SafeAtStable (hNext : Next Quorums sent sent')
  (v : Value) (b : Ballot) (hSafe : SafeAt sent Quorums v b) : SafeAt sent' Quorums v b := by
  have h_sent_sub : sent ⊆ sent' := by exact next_imp_mono_sent Quorums sent sent' hNext
  unfold Next at hNext
  rcases hNext with ⟨b', h1a⟩ | ⟨a', h1b⟩ | ⟨b', h2a⟩ | ⟨a', h2b⟩
  · unfold SafeAt at *
    intro b2 hxb
    specialize hSafe b2 hxb
    rcases hSafe with ⟨Q, hQ, hProp⟩
    have hV : ∀ a ∈ Q, VotedForIn sent a v b2 → VotedForIn sent' a v b2 := by
      intro a ha
      exact fun a_1 => votedForIn_monotonic sent sent' h_sent_sub a_1
    have hW : ∀ a ∈ Q, WontVoteIn sent a b2 → WontVoteIn sent' a b2 := by
      intro a ha hWont
      unfold WontVoteIn at *
      constructor
      · unfold Phase1a at h1a
        refine send_add_non_twob_preserves_no_vote sent sent' hWont.left h1a ?_
        refine Or.inl ?_
        exact exists_apply_eq_apply' Message.onea b'
      · exact exists_mem_of_subset h_sent_sub hWont.right
    use Q; constructor
    · exact hQ
    · intro a ha
      cases hProp a ha with
      | inl hVoted => left; exact hV a ha hVoted
      | inr hWont => right; exact hW a ha hWont
  · unfold SafeAt at *
    intro b2 hxb
    specialize hSafe b2 hxb
    rcases hSafe with ⟨Q, hQ, hProp⟩
    have hV : ∀ a ∈ Q, VotedForIn sent a v b2 → VotedForIn sent' a v b2 := by
      exact fun a a_1 a_2 ↦ votedForIn_monotonic sent sent' h_sent_sub a_2
    have hW : ∀ a ∈ Q, WontVoteIn sent a b2 → WontVoteIn sent' a b2 := by
      intro A hA hWont
      unfold WontVoteIn at *
      constructor
      · unfold Phase1b at h1b
        rcases h1b with ⟨m, hmsent, r, hr, hmatch⟩
        cases m with
        | onea b1 => cases r with
          | twob rbal rval a1 =>
            simp only [if_pos] at hmatch
            split_ifs at hmatch with hpos
            · refine send_add_non_twob_preserves_no_vote sent sent' hWont.left hmatch ?_
              refine Or.inr ?_; refine Or.inl ?_
              simp
            · simp [hmatch]; exact hWont.left
          | _ => simp at *;
        | _ => simp at *;
      · exact exists_mem_of_subset h_sent_sub hWont.right
    use Q; constructor
    · exact hQ
    · intro A ha
      specialize hProp A ha         -- get rid of ∀ in hProp
      specialize hV A ha
      cases hProp with
      | inl hVotedInPrev => exact Or.inl (hV hVotedInPrev);
      | inr hWontVoteInPrev => exact Or.inr (hW A ha hWontVoteInPrev)
  · unfold SafeAt at *
    intro b2 hxb
    specialize hSafe b2 hxb
    rcases hSafe with ⟨Q, hQ, hProp⟩
    have hV : ∀ a ∈ Q, VotedForIn sent a v b2 → VotedForIn sent' a v b2 := by
      exact fun a a_1 a_2 ↦ votedForIn_monotonic sent sent' h_sent_sub a_2
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
      · exact exists_mem_of_subset h_sent_sub hWont.right
    use Q; constructor
    · exact hQ
    · intro A ha
      specialize hProp A ha         -- get rid of ∀ in hProp
      specialize hV A ha
      cases hProp with
      | inl hVotedInPrev => exact Or.inl (hV hVotedInPrev);
      | inr hWontVoteInPrev => exact Or.inr (hW A ha hWontVoteInPrev)
  · unfold SafeAt at *
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
          · by_cases ha : a' = A
            · have h_not_eq_bal : b2 ≠ b1 := by
                rcases hWont with ⟨_, ⟨m_1b_2b, hm_sent, hm_match⟩⟩
                let m_1b_2b_c := m_1b_2b
                cases m_1b_2b with
                | oneb bb _ _ a1 | twob bb _ a1 => -- Merging two cases together
                  simp at hm_match
                  specialize hpos m_1b_2b_c
                  simp [hm_sent, m_1b_2b_c]at hpos
                  simp [ha, hm_match] at hpos
                  exact ne_of_lt (lt_of_lt_of_le hm_match.right hpos)
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
      specialize hProp A ha         -- get rid of ∀ in hProp
      specialize hV A ha
      cases hProp with
      | inl hVotedInPrev => exact Or.inl (hV hVotedInPrev);
      | inr hWontVoteInPrev => exact Or.inr (hW A ha hWontVoteInPrev)

theorem Consistent (hInv : MsgInv sent Quorums) : Consistency sent Quorums := by
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

theorem SafeAtStableSkeleton (hNext : Next Quorums sent sent')
  (v : Value) (b : Ballot) (hSafe : SafeAt sent Quorums v b) : SafeAt sent' Quorums v b := by
  have h_sent_sub : sent ⊆ sent' := by exact next_imp_mono_sent Quorums sent sent' hNext  -- First we obtain the subset relation
  unfold Next at hNext
  rcases hNext with ⟨b', h1a⟩ | ⟨a', h1b⟩ | ⟨b', h2a⟩ | ⟨a', h2b⟩ <;> unfold SafeAt at *   -- Break down the cases of Next and go case by case
  · intro b2 hxb; specialize hSafe b2 hxb; rcases hSafe with ⟨Q, hQ, hProp⟩
    have hV : ∀ a ∈ Q, VotedForIn sent a v b2 → VotedForIn sent' a v b2 := by sorry
    have hW : ∀ a ∈ Q, WontVoteIn sent a b2 → WontVoteIn sent' a b2 := by sorry
    use Q; constructor
    · exact hQ
    · intro aQ haQ
      cases hProp aQ haQ <;> simp [*] at *
  · intro b2 hxb; specialize hSafe b2 hxb; rcases hSafe with ⟨Q, hQ, hProp⟩
    have hV : ∀ a ∈ Q, VotedForIn sent a v b2 → VotedForIn sent' a v b2 := by sorry
    have hW : ∀ a ∈ Q, WontVoteIn sent a b2 → WontVoteIn sent' a b2 := by sorry
    use Q; constructor
    · exact hQ
    · intro aQ haQ
      cases hProp aQ haQ <;> simp [*] at *
  · intro b2 hxb; specialize hSafe b2 hxb; rcases hSafe with ⟨Q, hQ, hProp⟩
    have hV : ∀ a ∈ Q, VotedForIn sent a v b2 → VotedForIn sent' a v b2 := by sorry
    have hW : ∀ a ∈ Q, WontVoteIn sent a b2 → WontVoteIn sent' a b2 := by sorry
    use Q; constructor
    · exact hQ
    · intro aQ haQ
      cases hProp aQ haQ <;> simp [*] at *
  · intro b2 hxb; specialize hSafe b2 hxb; rcases hSafe with ⟨Q, hQ, hProp⟩
    have hV : ∀ a ∈ Q, VotedForIn sent a v b2 → VotedForIn sent' a v b2 := by sorry
    have hW : ∀ a ∈ Q, WontVoteIn sent a b2 → WontVoteIn sent' a b2 := by sorry
    use Q; constructor
    · exact hQ
    · intro aQ haQ
      cases hProp aQ haQ <;> simp [*] at *

theorem ConsistentSkeleton (hInv : MsgInv sent Quorums) : Consistency sent Quorums := by
  unfold Consistency
  rintro v1 v2 ⟨⟨b1, hChosenIn1⟩, ⟨b2, hChosenIn2⟩⟩
  -- We prove the following symmetrical result for it to be used later in the proof
  have Consistent_ChosenIn_Diff_Bal (b1: Ballot) (v1: Value) (b2: Ballot) (v2: Value) (hChosenIn1: ChosenIn sent Quorums v1 b1) (hChosenIn2: ChosenIn sent Quorums v2 b2) (h_ls: b1 < b2) : v1 = v2 := by
      have h_safe_b2 : SafeAt sent Quorums v2 b2 := by
        -- By VotedInv, QuorumAssumption DEF ChosenIn, Inv
        sorry
      sorry -- rest of the proof
  by_cases h_eq : b1 = b2       -- assume b1 = b2, we conclude Consistency
  · unfold ChosenIn at *
    rcases hChosenIn1 with ⟨Q1, hQ1, hProp1⟩
    rcases hChosenIn2 with ⟨Q2, hQ2, hProp2⟩
    have ⟨aa, haa⟩ := pick_from_quorum_int Quorums hQ1 hQ2
    specialize hProp1 aa
    specialize hProp2 aa
    have hv1 := hProp1 (And.left haa); have hv2 := hProp2 (And.right haa)
    rw [←h_eq] at hv2
    exact VotedOnce sent Quorums hInv hv1 hv2
  by_cases h_lt: b1 < b2         -- Otherwise, assume b1 < b2, we conclude Consistency, by Consistent_ChosenIn_Diff_Bal
  · exact Consistent_ChosenIn_Diff_Bal b1 v1 b2 v2 hChosenIn1 hChosenIn2 h_lt
  · have h_nlt: b2 < b1 := by    -- This is symmetrical to the previous case, use Consistent_ChosenIn_Diff_Bal again
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
      cases maxVal with
      | none => simp
      | some v₀ =>
        simp [-Send]; simp at hInv
        refine And.intro ?_ ?_
        · rw [←h1a]
          exact votedForIn_monotonic sent sent' h_subset hInv.left
        · intro b' hb_lower hb_upper x
          have h_not_voted := hInv.right
          specialize h_not_voted b'
          simp [hb_lower, hb_upper] at h_not_voted
          specialize h_not_voted x
          unfold VotedForIn at *
          simp ; simp at h_not_voted; exact h_not_voted
    | twoa b1 v1 =>
      simp at hInv; simp [-Send]
      rw [←h1a]
      refine And.intro ?_ ?_
      · exact SafeAtStable_Phase1a sent sent' Quorums h1a_copy hInv.left
      · have h_inv_right := hInv.right
        intro m2 h_m2_in_sent'
        specialize h_inv_right m2
        cases m2 <;> simp [*] at * ; apply h_inv_right at h_m2_in_sent' ; exact h_m2_in_sent'
    | twob b1 v1 a1 => cases v1 <;> simp [*] at *

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
    | twob rbal rvbal racc =>
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
        by_cases h_m_eq_oneb : m' = Message.oneb mbal rbal rvbal a  -- m' is the witness message sent
        · simp [h_m_eq_oneb]
          cases rvbal with
          | none => simp
          | some rvbal =>
            simp
            constructor
            · refine votedForIn_monotonic sent sent' h_subset ?_    -- use refine, and we are just trying to prove that a voted in sent, which can be derived from max_prop
              rw [h_same_accptor] at *
              exact max_prop_not_empty_implies_voted_for sent hr
            · have h_not_voted_for_greater_ballots : ∀ (b' : Ballot), rbal + 1 ≤ b' → b' ≤ mbal - 1 → ∀ (x : Value), ¬VotedForIn sent a x b' := by
                rw [h_same_accptor] at hr
                have h_not_voted_for_greater_ballots := max_prop_implies_not_voted_for_greater_ballots sent hr
                intro b' hb_lower hb_upper x
                specialize h_not_voted_for_greater_ballots b' x hb_lower
                simp [h_same_accptor]; exact h_not_voted_for_greater_ballots
              exact fun b' a_1 a_2 x ↦        -- This is from "apply?" I think the goal is clear enough but simp [h_not_voted_for_greater_ballots, l1] didn't work. TODO: make this more readble
                (fun {a b} ha ↦ (iff_false_left ha).mp)
                  (h_not_voted_for_greater_ballots b' a_1 a_2 x) (l1 a x b')
        · have h_m_in_sent : m' ∈ sent := by simp [*] at * ; simp [h_m_eq_oneb] at hm' ; exact hm'    -- TODO: This part is repetitive, as I copied this from the 1a case and just changes a few things. How to get rid of this repetition?
          cases m' with
          | onea b1 => simp
          | oneb b1 maxVBal maxVal a1 =>
            simp at hInv; simp [-Send]
            cases maxVal with
            | none => simp
            | some v₀ =>
              simp [-Send]; specialize hInv (Message.oneb b1 maxVBal (some v₀) a1); simp [h_m_in_sent] at hInv
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
            specialize hInv (Message.twoa b1 v1); simp [h_m_in_sent] at hInv
            refine And.intro ?_ ?_
            · exact SafeAtStable_Phase1b sent sent' Quorums h1b_copy hInv.left
            · have h_inv_right := hInv.right
              intro m2 h_m2_in_sent'
              specialize h_inv_right m2
              cases m2 <;> simp [*] at * ; apply h_inv_right at h_m2_in_sent' ; exact h_m2_in_sent'
          | twob b1 v1 a1 =>
            cases v1 with
            | none => simp [*] at *
            | some v1 => specialize hInv (Message.twob b1 v1 a1); simp [h_m_in_sent] at hInv; simp [*] at *
      · rw [hmatch]; exact hInv
    | _ => simp [*] at *
  | _ => simp [*] at *

set_option maxHeartbeats 1000000      -- tactic 'simp' failed, nested error: (deterministic) timeout at `isDefEq`, maximum number of heartbeats (200000) has been reached Use `set_option maxHeartbeats <num>` to set the limit

-- Effort: 1h30m, taking care of some chores with Phase 2a.
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
    by_cases h_m_eq_t2a : m' = Message.twoa b v
    · simp [h_m_eq_t2a]
      constructor
      · -- Proving SafeAt
        have h_safe_at_prev : SafeAt sent Quorums v b := by         -- Proving SafeAt sent, and use SafeAtStable
          rcases h_no_prev_2a_msg with ⟨V, Q, S, ⟨h_Q_in_quorums, h_S_set_of_oneb, h_all_acc_in_Q_sent_oneb, h_all_not_voted_or_some_voted⟩⟩
          cases' h_all_not_voted_or_some_voted with h_none_voted h_some_voted
          · unfold SafeAt
            intro b2 h_b2_less_than_b
            use Q; simp [h_Q_in_quorums]
            intro a haQ
            right
            have ⟨m1, hm1S, hm1_match⟩ := h_all_acc_in_Q_sent_oneb a haQ
            unfold WontVoteIn
            sorry
          · sorry
        exact SafeAtStable_Phase2a sent sent' Quorums h2a_copy h_safe_at_prev
      · sorry
    · simp [h_send, h_m_eq_t2a] at hm_sent'
      cases m' with
      | onea b1 => simp
      | oneb b1 maxVBal maxVal a1 =>
        simp at hInv; simp [-Send]
        cases maxVal with
        | none => simp
        | some v₀ =>
          simp [-Send]; specialize hInv (Message.oneb b1 maxVBal (some v₀) a1); simp [hm_sent'] at hInv
          constructor
          · exact votedForIn_monotonic sent sent' h_subset hInv.left
          · intro b' hb_lower hb_upper x
            have h_not_voted := hInv.right
            specialize h_not_voted b'
            simp [hb_lower, hb_upper] at h_not_voted
            specialize h_not_voted x
            unfold VotedForIn at *
            simpa [h_send] using h_not_voted
      | twoa b1 v1 =>
        simp at hInv; simp [-Send]
        specialize hInv (Message.twoa b1 v1); simp [hm_sent'] at hInv
        refine And.intro ?_ ?_
        · exact SafeAtStable_Phase2a sent sent' Quorums h2a_copy hInv.left
        · have h_inv_right := hInv.right
          intro m2 h_m2_in_sent'
          specialize h_inv_right m2
          cases m2 with
          | twoa b1' v1' => sorry
          | _ => simp [*] at *;
          -- cases m2 <;> simp [*] at * ; apply h_inv_right at h_m2_in_sent' ; exact h_m2_in_sent' -- -- tactic 'simp' failed, nested error: (deterministic) timeout at `isDefEq`, maximum number of heartbeats (200000) has been reached Use `set_option maxHeartbeats <num>` to set the limit
      | twob b1 v1 a1 =>
        cases v1 with
        | none => simp [*] at *
        | some v1 => specialize hInv (Message.twob b1 v1 a1); simp [hm_sent'] at hInv; simp [*] at *
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
      · cases m' with
          | onea b1 => simp
          | oneb b1 maxVBal maxVal a1 =>
            simp at hInv; simp [-Send]
            cases maxVal with
            | none => simp
            | some v₀ =>
              simp [-Send]; specialize hInv (Message.oneb b1 maxVBal (some v₀) a1); simp [h_m'_in_sent] at hInv
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
                ·
                  intro hb_eq hv_eq ha_eq
                  -- simp [hb_eq, hv_eq, ha_eq] at *
                  have h_inv_right := hInv.right
                  specialize h_inv_right b' hb_lower hb_upper x
                  specialize hpo (Message.oneb b1 maxVBal (some v₀) a1) h_m'_in_sent      -- finished by chatGPT
                  have h_b1_le_b : b1 ≤ b := hpo ha_eq
                  have h_b_le_b1_1 : b ≤ b1 - 1 := by simpa [hb_eq] using hb_upper
                  linarith                                                                -- I would not have thought of using linarith here, but it makes sense.
                · exact h_not_voted
          | twoa b1 v1 =>
            simp at hInv; simp [-Send]
            specialize hInv (Message.twoa b1 v1); simp [h_m'_in_sent] at hInv
            refine And.intro ?_ ?_
            · exact SafeAtStable_Phase2b sent sent' Quorums h2b_copy hInv.left
            · have h_inv_right := hInv.right
              intro m2 h_m2_in_sent'
              specialize h_inv_right m2
              cases m2 <;> simp [*] at * ; apply h_inv_right at h_m2_in_sent' ; exact h_m2_in_sent'
          | twob b1 v1 a1 =>
            cases v1 with
            | none => simp [*] at *
            | some v1 => specialize hInv (Message.twob b1 v1 a1); simp [h_m'_in_sent] at hInv; simp [*] at *
      · have m'_eq_twob : m' = Message.twob b v a := by simp [*] at *; exact hm_sent'
        simp [m'_eq_twob]
        exact h_subset h_2a_sent
    · simp [*] at *
  | _ => simp [*] at *

theorem Inductiveness (hInv: MsgInv sent Quorums) (hNext: Next Quorums sent sent') : MsgInv sent' Quorums := by
  unfold Next at hNext
  rcases hNext with ⟨b', h1a⟩ | ⟨a', h1b⟩ | ⟨b', h2a⟩ | ⟨a', h2b⟩
  · exact ind_phase1a sent sent' Quorums hInv h1a
  · exact ind_phase1b sent sent' Quorums hInv h1b
  · exact ind_phase2a sent sent' Quorums hInv h2a
  · exact ind_phase2b sent sent' Quorums hInv h2b
