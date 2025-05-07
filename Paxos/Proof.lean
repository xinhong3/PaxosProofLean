import Paxos.Spec
import Paxos.Prop
import Paxos.ExtraLemma
import Smt

set_option auto.native true

open Paxos.Spec Paxos.Prop Paxos.ExtraLemma

lemma VotedInv (h1: MsgInv sent Quorums) : ∀ a, ∀ v, ∀ b, VotedForIn sent a v b → SafeAt sent Quorums v b := by
  unfold MsgInv VotedForIn at *
  intros a v b h; simp at h
  apply h1 at h; simp at h
  apply h1 at h; simp at h
  exact h.left

lemma VotedOnce (hInv: MsgInv sent Quorums) (h_voted_1: VotedForIn sent a1 v1 b) (h_voted_2 : VotedForIn sent a2 v2 b) : v1 = v2 := by
  unfold VotedForIn MsgInv at *
  have h_m_2a_1 : Message.twoa b v1 ∈ sent := by
    simp at h_voted_1; apply hInv at h_voted_1; simp at h_voted_1; exact h_voted_1
  apply hInv at h_m_2a_1; simp at h_m_2a_1
  have h_m_2a_2 : Message.twoa b v2 ∈ sent := by
    simp at h_voted_2; apply hInv at h_voted_2; simp at h_voted_2; exact h_voted_2
  apply h_m_2a_1.right at h_m_2a_2; simp at h_m_2a_2
  exact h_m_2a_2.symm

theorem SafeAtStable (hNext : Next Quorums sent sent')
  (v : Value) (b : Ballot) (hSafe : SafeAt sent Quorums v b) : SafeAt sent' Quorums v b := by
  have h_sent_sub : sent ⊆ sent' := by exact next_imp_mono_sent Quorums hNext
  unfold Next at hNext
  rcases hNext with ⟨b', h1a⟩ | ⟨a', h1b⟩ | ⟨b', h2a⟩ | ⟨a', h2b⟩
  · unfold SafeAt at *
    intro b2 hxb
    specialize hSafe b2 hxb
    rcases hSafe with ⟨Q, hQ, hProp⟩
    have hV : ∀ a ∈ Q, VotedForIn sent a v b2 → VotedForIn sent' a v b2 := by
      intro a ha
      exact fun a_1 => votedForIn_monotonic h_sent_sub a_1
    have hW : ∀ a ∈ Q, WontVoteIn sent a b2 → WontVoteIn sent' a b2 := by
      intro a ha hWont
      unfold WontVoteIn at *
      constructor
      · unfold Phase1a at h1a
        refine send_add_non_twob_preserves_no_vote hWont.left h1a ?_
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
      exact fun a a_1 a_2 ↦ votedForIn_monotonic h_sent_sub a_2
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
            · refine send_add_non_twob_preserves_no_vote hWont.left hmatch ?_
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
      exact fun a a_1 a_2 ↦ votedForIn_monotonic h_sent_sub a_2
    have hW : ∀ a ∈ Q, WontVoteIn sent a b2 → WontVoteIn sent' a b2 := by
      intro A hA hWont
      unfold WontVoteIn at *
      constructor
      · unfold Phase2a at h2a
        split_ifs at h2a
        · simp [h2a]; exact hWont.left
        · refine send_add_non_twob_preserves_no_vote hWont.left h2a ?_
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
      exact fun a a_1 a_2 ↦ votedForIn_monotonic h_sent_sub a_2
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
        refine VotedInv hInv ?a v2 b2 ?_
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
      | inl haa_voted_v2_b1 => exact VotedOnce hInv haa_voted_v1_b1 haa_voted_v2_b1
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
    exact VotedOnce hInv hv1 hv2
  by_cases h_lt: b1 < b2
  · exact Consistent_ChosenIn_Diff_Bal b1 v1 b2 v2 hChosenIn1 hChosenIn2 h_lt
  · have h_nlt: b2 < b1 := by
      have h_total := lt_trichotomy b1 b2
      rcases h_total with (h_total_left | h_total_mid | h_total_r) <;> simp [*] at *
    exact id (Consistent_ChosenIn_Diff_Bal b2 v2 b1 v1 hChosenIn2 hChosenIn1 h_nlt).symm
