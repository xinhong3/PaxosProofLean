/-
  Safety Proof of Basic Paxos, translated from TLAPS proof
  in https://arxiv.org/pdf/1802.09687, Appendix C, by Chand and Liu, referred to as CL.
-/
import Paxos.Spec
import Paxos.Prop
import Paxos.ExtraLemma

namespace Paxos.Proof
open Paxos.Spec Paxos.Prop Paxos.ExtraLemma

variable (sent sent' : Set Message)
variable (Quorums : Set (Set Acceptor))

/-- lemma VotedInv in CL. -/
lemma VotedInv (h1 : MsgInv sent Quorums) :
    ∀ a v b, VotedForIn sent a v b → SafeAt sent Quorums v b := by
  unfold MsgInv VotedForIn at *
  intros a v b h; simp at h
  apply h1 at h; simp at h
  apply h1 at h; simp at h
  exact h.left

/-- lemma VotedOnce in CL. -/
lemma VotedOnce
    (hInv : MsgInv sent Quorums)
    (h_voted_v1 : VotedForIn sent a1 v1 b)
    (h_voted_v2 : VotedForIn sent a2 v2 b) : v1 = v2 := by
  unfold VotedForIn MsgInv at *
  have h_exists_2a_with_v1 : Message.twoa b v1 ∈ sent := by
    simp at h_voted_v1; apply hInv at h_voted_v1; simpa using h_voted_v1
  have h_exists_2a_with_v2 : Message.twoa b v2 ∈ sent := by
    simp at h_voted_v2; apply hInv at h_voted_v2; simpa using h_voted_v2
  apply hInv at h_exists_2a_with_v1; simp at h_exists_2a_with_v1
  apply h_exists_2a_with_v1.right at h_exists_2a_with_v2;
  simp at h_exists_2a_with_v2
  exact Eq.symm h_exists_2a_with_v2

/-- A template for proving `SafeAtStable`. Each phase only need to provide the proof that
`h_wontVoteIn_preserves` holds. -/
lemma safeAt_inductive_template {v : Value} {b : Ballot} {sent sent' : Set Message}
    {Quorums : Set (Set Acceptor)}
    (h_mono : sent ⊆ sent')
    (h_wontVoteIn_preserves : ∀ {a b}, WontVoteIn sent a b → WontVoteIn sent' a b) :
    SafeAt sent Quorums v b → SafeAt sent' Quorums v b := by
  intro hSafe b2 hxb
  rcases hSafe b2 hxb with ⟨Q, h_Q_in_quorums, h_all_voted_or_wont_vote⟩
  have hV : ∀ a, a ∈ Q → VotedForIn sent a v b2 → VotedForIn sent' a v b2 := by
    exact fun a a_1 a_2 => votedForIn_stable sent sent' h_mono a_2
  refine ⟨Q, h_Q_in_quorums, ?forAllAccInQ_votedFor_or_wontVote⟩
  intro A hA
  cases h_all_voted_or_wont_vote A hA with
  | inl hVoted  => exact Or.inl (hV A hA hVoted)
  | inr hWont   => exact Or.inr (h_wontVoteIn_preserves hWont)

-- The following four lemmas show that `SafeAt` is inductive over all four phases.

lemma safeAt_is_inductive_phase1a
    (h1a : Phase1a sent sent' b2)
    (hSafe : SafeAt sent Quorums v b) : SafeAt sent' Quorums v b := by
  have h_mono : sent ⊆ sent' := phase1a_imp_mono_sent h1a
  have h_no_1b_or_2b_added : ∀ m ∈ sent' \ sent, ¬ (is1b m ∨ is2b m) := by simp_all
  unfold Phase1a at h1a
  have h_wontVoteIn_stable : ∀ {a b}, WontVoteIn sent a b → WontVoteIn sent' a b := by
    exact wontVoteIn_stable_if_no_1b2b_added sent sent' h_mono h_no_1b_or_2b_added
  exact safeAt_inductive_template h_mono h_wontVoteIn_stable hSafe

lemma safeAt_is_inductive_phase1b
    (h1b : Phase1b sent sent' a)
    (hSafe : SafeAt sent Quorums v b) : SafeAt sent' Quorums v b := by
  have h_mono : sent ⊆ sent' := phase1b_imp_mono_sent h1b
  have h_wontVoteIn_preserves : ∀ {a1 b1}, WontVoteIn sent a1 b1 → WontVoteIn sent' a1 b1 := by
    intro a1 b1 hW; unfold WontVoteIn at *
    refine And.intro ?h_not_voted_for_any ?h_exists_higher_ballot
    · unfold Phase1b at h1b
      rcases h1b with ⟨m, _h_m_in_sent, r, _h_r_in_sent, hmatch⟩
      cases m with
      | onea _ =>
        cases r with
        | twob _ _ _ =>
          simp only at hmatch
          simpa [votedForIn_same_if_no_2b_send sent sent' hmatch.right] using hW.left
        | _ => simp at *
      | _ => simp at *
    · exact exists_mem_of_subset h_mono hW.right
  exact safeAt_inductive_template h_mono h_wontVoteIn_preserves hSafe

lemma safeAt_is_inductive_phase2a
    (h2a : Phase2a Quorums sent sent' b2)
    (hSafe : SafeAt sent Quorums v b) : SafeAt sent' Quorums v b := by
  have h_mono : sent ⊆ sent' := phase2a_imp_mono_sent h2a
  rcases h2a with ⟨_, ⟨_,_,_,_,_,_,_, h_send⟩⟩
  have h_no_1b_or_2b_added : ∀ m ∈ sent' \ sent, ¬ (is1b m ∨ is2b m) := by simp_all
  have h_wontVoteIn_stable : ∀ {a b}, WontVoteIn sent a b → WontVoteIn sent' a b := by
    exact wontVoteIn_stable_if_no_1b2b_added sent sent' h_mono h_no_1b_or_2b_added
  exact safeAt_inductive_template h_mono h_wontVoteIn_stable hSafe

lemma safeAt_is_inductive_phase2b
    (h2b : Phase2b sent sent' a)
    (hSafe : SafeAt sent Quorums v b) : SafeAt sent' Quorums v b := by
  have h_mono : sent ⊆ sent' := phase2b_imp_mono_sent h2b
  have h_wontVoteIn_stable : ∀ {a2 b2}, WontVoteIn sent a2 b2 → WontVoteIn sent' a2 b2 := by
    intro a2 b2 hW; unfold WontVoteIn at *
    have ⟨hNotVotedPrev, ⟨m_1b_2b, hm_sent, hm_match⟩⟩ := hW
    refine And.intro ?h_not_voted_for_any ?h_exists_higher_ballot
    · unfold Phase2b at h2b
      rcases h2b with ⟨m2a, h_twoa_in_sent, hmatch⟩
      cases m2a with
      | twoa b1 v1 =>
        simp only at hmatch
        rcases hmatch with ⟨h_no_greater_ballot, h_send⟩
        by_cases ha : a = a2
        · have h_not_eq_bal : b2 ≠ b1 := by
            cases hm : m_1b_2b with
            | oneb bb _ _ a2 | twob bb _ a2 =>
              all_goals              -- consolidate the two cases
              simp [hm] at hm_match  -- the first three lines are the same
              have hle := h_no_greater_ballot m_1b_2b hm_sent
              simp [hm_match.left, ha, hm] at hle
              -- the first `try` handles `1b` case, the second handles `2b` case.
              try exact ne_of_lt (lt_of_lt_of_le hm_match.right hle)
              try cases bb with
                | none    => simp at *
                | some bb => exact ne_of_lt (lt_of_lt_of_le hm_match.right hle)
            | _ => simp [hm] at *
          intro V h_A_voted_V_b2_sent'
          have h_A_not_voted_V_b2_sent := hNotVotedPrev V
          unfold VotedForIn at *
          simp_all
        · intro V hVoted
          specialize hNotVotedPrev V
          unfold VotedForIn at hVoted hNotVotedPrev
          simp [h_send] at hVoted
          cases hVoted with
          | inl hVotedCurrent => simp [hVotedCurrent] at ha
          | inr hVotedInPrev => simp [*] at *
      | _ => simp at hmatch
    · exact exists_mem_of_subset h_mono hW.right
  exact safeAt_inductive_template h_mono h_wontVoteIn_stable hSafe

/-- lemma SafeAtStable in CL. -/
lemma SafeAtStable {v : Value} {b : Ballot}
    (hNext : Next Quorums sent sent')
    (hSafe : SafeAt sent Quorums v b) : SafeAt sent' Quorums v b := by
  unfold Next at hNext
  rcases hNext with ⟨b, hPhase1a | hPhase2a⟩ | ⟨a, hPhase1b | hPhase2b⟩
  · exact safeAt_is_inductive_phase1a sent sent' Quorums hPhase1a hSafe
  · exact safeAt_is_inductive_phase2a sent sent' Quorums hPhase2a hSafe
  · exact safeAt_is_inductive_phase1b sent sent' Quorums hPhase1b hSafe
  · exact safeAt_is_inductive_phase2b sent sent' Quorums hPhase2b hSafe

-- The following four lemmas show that `MsgInv` is inductive over all four phases.

lemma msginv_is_inductive_phase1a
    (hInv : MsgInv sent Quorums)
    (h1a : Phase1a sent sent' b) : MsgInv sent' Quorums := by
  have h_mono : sent ⊆ sent' := phase1a_imp_mono_sent h1a
  have h_no_1b_or_2b_added : ∀ m ∈ sent' \ sent, ¬ (is1b m ∨ is2b m) := by simp_all
  have h_no_2b_added : ∀ m ∈ sent' \ sent, ¬ is2b m := by simp_all
  unfold MsgInv Phase1a at *
  intro m h_m_in_sent'; rw [h1a] at h_m_in_sent'
  rcases Or.symm h_m_in_sent' with (rfl | h_m_in_sent)  -- whether m is the new message
  · simp
  · specialize hInv m h_m_in_sent
    cases m with
    | onea _ => simp
    | oneb b1 maxVBal maxVal a1 =>
      simp only at hInv ⊢
      rcases hInv with ⟨hInv_1b_1, hInv_1b_2⟩
      match maxVBal, maxVal with
      | some rbal, some rval =>
        simp only at hInv_1b_1 ⊢
        apply And.intro ?h_inv_1b_1 ?h_inv_1b_2
        · exact votedForIn_stable sent sent' h_mono hInv_1b_1
        · exact oneb_inv_2_stable_if_no_twob_added sent sent' h_mono h_no_2b_added hInv_1b_2
      | none, none =>
        simp only at hInv_1b_1 ⊢
        simpa [votedForIn_same_if_no_2b_send sent sent' h1a] using hInv_1b_2
      | some rbal, none | none, some rval => simp at hInv_1b_1
    | twoa b1 v1 =>
      simp only at hInv
      rcases hInv with ⟨hSafeAt, hUnique⟩
      refine And.intro ?safe_at ?unique_proposal
      · exact safeAt_is_inductive_phase1a sent sent' Quorums h1a hSafeAt
      · intro m2 hm2_in_sent'
        rw [h1a] at hm2_in_sent'
        rcases hm2_in_sent' with (hm2_in_sent | rfl)
        · exact hUnique m2 hm2_in_sent
        · simp
     | twob b1 v1 a1 => cases b1 <;> cases v1 <;> simp [*]

lemma msginv_is_inductive_phase1b
    (hInv : MsgInv sent Quorums)
    (h1b : Phase1b sent sent' a) : MsgInv sent' Quorums := by
  have h_mono : sent ⊆ sent' := phase1b_imp_mono_sent h1b
  have ⟨m1a, _, r, h_r_in_sent, hmatch⟩ := h1b
  cases m1a with
  | onea mbal =>
    cases r with
    | twob rbal rval racc =>
      have h_exists_b_v_with_same_acceptor := mem_max_prop_is_2b sent h_r_in_sent
      have h_r_has_same_acc : a = racc := by simp_all
      simp only at hmatch
      rcases hmatch with ⟨h_no_2a_with_same_ballot, h_send⟩
      have h_no_2b_added : ∀ m ∈ sent' \ sent, ¬ (is2b m) := by simp_all
      unfold MsgInv at *
      intro m2 hm2; rw [h_send] at hm2
      rcases Or.symm hm2 with h_m2_is_1b | h_m2_in_sent -- whether m2 is the new message
      · simp at h_m2_is_1b; simp only [h_m2_is_1b]
        match rbal, rval with         -- case on whether max_prop is empty
        | some rbal, some rval =>     -- max_prop not empty, which means voted before
          simp only
          refine And.intro ?h_inv_1b_1 ?h_inv_1b_2
          · subst a
            exact votedForIn_stable sent sent' h_mono
                    (max_prop_not_empty_implies_voted_for sent h_r_in_sent)
          · have h_inv_1b_2_prev :
                ∀ (b' : Ballot), some rbal + 1 ≤ b' → b' < some mbal →
                  ∀ (x : Value), ¬VotedForIn sent a x b' := by
              subst racc
              intro b' hb'_lower hb'_upper
              have h_not_voted_for_greater_ballots :=
                max_prop_implies_not_voted_for_greater_ballots sent h_r_in_sent b'
              have hb'_lower : b' ≥ rbal +1 := by exact hb'_lower
              simp [hb'_lower] at h_not_voted_for_greater_ballots
              simpa [votedForIn_same_if_no_2b_send sent sent' h_send] using
                h_not_voted_for_greater_ballots
            simpa [votedForIn_same_if_no_2b_send sent sent' h_send] using h_inv_1b_2_prev
        | none, none =>               -- max_prop empty
          simp; subst racc
          intro b hb_upper
          have h_not_voted_in_sent :=
            max_prop_empty_implies_not_voted_in_prev_ballots sent h_r_in_sent b
          simpa [votedForIn_same_if_no_2b_send sent sent' h_send] using h_not_voted_in_sent
        | some rbal, none | none, some rval =>
          rw [h_r_has_same_acc] at h_r_in_sent
          apply max_prop_empty_ballot_iff_empty_value at h_r_in_sent
          simp at h_r_in_sent
      · cases m2 with       -- `m2 ∈ sent`, show each invariant still holds
        | onea b1 => simp
        | oneb b1 maxVBal maxVal a1 =>
          simp only at hInv ⊢
          rcases (hInv (Message.oneb b1 maxVBal maxVal a1) h_m2_in_sent) with
                   ⟨hInv_1b_1, hInv_1b_2⟩
          match maxVBal, maxVal with
          | some rbal, some rval =>
            simp only at hInv ⊢
            constructor
            · exact votedForIn_stable sent sent' h_mono hInv_1b_1
            · exact oneb_inv_2_stable_if_no_twob_added sent sent' h_mono h_no_2b_added hInv_1b_2
          | none, none =>
            simp only [true_and] at hInv_1b_1 ⊢
            simpa [votedForIn_same_if_no_2b_send sent sent' h_send] using hInv_1b_2
          | some rbal, none | none, some rval =>
            simp at hInv_1b_1
        | twoa b1 v1 =>
          simp only at hInv
          specialize hInv (Message.twoa b1 v1) h_m2_in_sent
          rcases hInv with ⟨hSafeAt, hUnique⟩
          refine And.intro ?safe ?uniq
          · exact safeAt_is_inductive_phase1b sent sent' Quorums h1b hSafeAt
          · intro m2a h_m2a_in_sent'
            rw [h_send] at h_m2a_in_sent'
            rcases h_m2a_in_sent' with (h_m2a_in_sent | rfl)
            · exact hUnique m2a h_m2a_in_sent
            · simp
        | twob b1 v1 a1 =>
          match b1, v1 with
          | some b1, some v1 => exact h_mono (hInv (Message.twob b1 v1 a1) h_m2_in_sent)
          | none, none | some b1, none | none, some v1 => simp
    | _ => simp at hmatch
  | _ => simp at hmatch

lemma msginv_is_inductive_phase2a
    (hInv : MsgInv sent Quorums)
    (h2a : Phase2a Quorums sent sent' b) : MsgInv sent' Quorums := by
  have h_mono : sent ⊆ sent' := phase2a_imp_mono_sent h2a
  have ⟨h_no_prev_2a_with_same_ballot,
         ⟨v, Q, S, h_Q_in_quorums, h_S_subsetOf_1b_msgs,h_all_acc_in_Q_sent_1b,
           h_all_acc_none_voted_or_some_voted, h_sent_2a_msg⟩⟩ := h2a
  have h_no_2b_added : ∀ m ∈ sent' \ sent, ¬ is2b m := by simp_all
  have h_votedForIn_same : ∀ a v b, VotedForIn sent a v b ↔ VotedForIn sent' a v b := by
    intro a v b
    unfold VotedForIn
    simp [h_sent_2a_msg]
  unfold MsgInv at *
  intro m1 h_m1_in_sent'; rw [h_sent_2a_msg] at h_m1_in_sent'
  rcases Or.symm h_m1_in_sent' with (rfl | h_m1_in_sent)
  -- `m1 = Message.twoa b v`, the new message sent in phase 2a
  · simp only
    refine And.intro ?safe_at ?unique_proposal    -- two invariants for `2a`
    -- To show `SafeAt sent' ...`, we show `SafeAt sent ...` and then use `SafeAtStable`.
    · suffices h_safe_at_sent : SafeAt sent Quorums v b by
        exact safeAt_is_inductive_phase2a sent sent' Quorums h2a h_safe_at_sent
      -- Showing `SafeAt sent ...`
      unfold SafeAt
      intro b2 h_b2_less_than_b
      cases' h_all_acc_none_voted_or_some_voted with h_none_voted h_some_voted
      -- case where no acceptors in Q voted.
      · use Q, h_Q_in_quorums
        intro a haQ
        refine Or.inr ?wontVoteIn_a_b2
        obtain ⟨m1, hm1S, hm1_match⟩ := h_all_acc_in_Q_sent_1b a haQ
        obtain ⟨h_m1S_in_sent, h_match_m1_eq_b⟩ := h_S_subsetOf_1b_msgs hm1S
        unfold WontVoteIn
        cases hm1: m1 with
        | oneb bal1 maxVBal1 maxVal1 acc1 =>
          subst m1 bal1
          refine And.intro ?h_not_voted_for_any ?h_exists_higher_ballot
          · specialize h_none_voted _ hm1S
            have hInv_1b := hInv _ h_m1S_in_sent
            simpa [h_none_voted, h_b2_less_than_b, hm1_match] using hInv_1b.right b2
          · use Message.oneb b maxVBal1 maxVal1 acc1, h_m1S_in_sent
        | _ => simp [hm1] at hm1_match;
      -- case where some acceptors in Q voted.
      · rcases h_some_voted with    -- `c` is the maximum ballot voted by acceptors in Q
          ⟨c, h_c_gte_zero, h_c_lt_b, ⟨h_all_1b_has_ballot_lte_c, h_some_1b_has_ballot_c⟩⟩
        -- For each case: `b2 < c`, `b2 = c`, `b2 > c`, show `SafeAt sent ...`
        rcases lt_trichotomy b2 c with h_b2_less_than_c | h_b2_eq_c | h_b2_greater_than_c
        -- 1. `b2 < c`
        · rcases h_some_1b_has_ballot_c with ⟨m1b_with_ballot_c, h_m1b_in_S, h_m1b_match⟩
          cases hm1b : m1b_with_ballot_c with
          | oneb bal_c mc_vbal mc_val mc_acc =>
            subst m1b_with_ballot_c
            match mc_vbal, mc_val with
            | some mc_vbal, some mc_val =>
              have ⟨mc_in_sent, _⟩ := h_S_subsetOf_1b_msgs h_m1b_in_S
              have hInv_2b := hInv _ mc_in_sent
              simp at h_m1b_match; obtain ⟨h_mc_vbal_eq_c, h_mc_val_eq_v⟩ := h_m1b_match
              subst mc_vbal mc_val
              have h_safe_at_c : SafeAt sent Quorums v c := by
                have h_voted_acc : VotedForIn sent mc_acc v c := by simp [hInv_2b.left]
                exact VotedInv sent Quorums hInv mc_acc v c h_voted_acc
              exact h_safe_at_c b2 h_b2_less_than_c
            | none, some _ | some _, none | none, none => simp at h_m1b_match
          | _ => simp only [hm1b] at h_m1b_match;
        -- 2. `b2 = c`
        · use Q, h_Q_in_quorums
          intro a haQ
          · rcases h_some_1b_has_ballot_c with ⟨m1b_with_ballot_c, h_m1b_in_S, h_m1b_match⟩
            cases hm1b: m1b_with_ballot_c with     -- get the `1b` message with ballot `c`
            | oneb bal_c mc_vbal mc_val mc_acc =>
              match mc_vbal, mc_val with
              | some mc_vbal, some mc_val =>
                simp [hm1b] at h_m1b_match
                have ⟨h_vbal_eq_c, h_mc_val_eq_v⟩ := h_m1b_match
                subst mc_vbal; subst mc_val; subst b2
                have h_voted_acc_c : VotedForIn sent mc_acc v c := by
                  have ⟨mc_in_sent, _⟩ := h_S_subsetOf_1b_msgs h_m1b_in_S
                  have h_inv_mc := hInv m1b_with_ballot_c mc_in_sent
                  simp [hm1b] at h_inv_mc
                  exact h_inv_mc.left
                have h_all_voted_in_c_for_v :
                    ∀ q ∈ Q, ∀ (w: Value), VotedForIn sent q w c → w = v := by
                  intro q h_q_in_Q w h_voted
                  exact VotedOnce sent Quorums hInv h_voted h_voted_acc_c
                by_cases h_a_voted_in_c : VotedForIn sent a v c
                · simp [h_a_voted_in_c]
                · right
                  unfold WontVoteIn
                  constructor
                  · intro v' h_voted_in_v'
                    have h_voted_eq_v := h_all_voted_in_c_for_v a haQ v' h_voted_in_v'
                    subst v'
                    exact h_a_voted_in_c h_voted_in_v'
                  · obtain ⟨m2_1b, h_m2_in_S, h_m2_acc_a⟩ := h_all_acc_in_Q_sent_1b a haQ
                    cases m2_1b with
                    | oneb bal2 maxVBal2 maxVal2 acc2 =>
                      have h_m2_is_1b := h_S_subsetOf_1b_msgs h_m2_in_S
                      obtain ⟨h_m2_in_sent, h_same_ballot⟩ := h_m2_is_1b
                      use Message.oneb bal2 maxVBal2 maxVal2 acc2, h_m2_in_sent
                      simp [h_same_ballot, h_m2_acc_a, h_b2_less_than_b]
                    | _ => simp at h_m2_acc_a;
              | some _, none | none, some _ | none, none => simp [hm1b] at h_m1b_match
            | _ => simp [hm1b] at h_m1b_match;
        -- 3. `b2 > c`
        · use Q, h_Q_in_quorums
          intro a haQ
          · refine Or.inr ?wontVoteIn_a_b2_1
            obtain ⟨m2_1b, h_m2_in_S, h_m2_acc_a⟩ := h_all_acc_in_Q_sent_1b a haQ
            constructor
            · obtain ⟨hm2_sent, h_m2_match_bal_eq_b⟩ := (h_S_subsetOf_1b_msgs h_m2_in_S)
              cases h_case_m2: m2_1b with
              | oneb bal2 maxVBal2 maxVal2 acc2 =>
                have h_acc_eq : acc2 = a := by simpa [h_case_m2] using h_m2_acc_a
                subst acc2
                specialize hInv m2_1b hm2_sent
                simp [h_case_m2] at hInv
                rcases hInv with ⟨_, h_lim⟩
                suffices no_ex : ∀ x, ¬VotedForIn sent a x b2 by exact no_ex
                · specialize h_lim b2
                  specialize h_all_1b_has_ballot_lte_c m2_1b h_m2_in_S
                  simp [h_case_m2] at h_all_1b_has_ballot_lte_c
                  have h_lower : maxVBal2 + (1 : Nat) ≤ some b2 := by
                    cases maxVBal2 with
                    | none => simp [ballot_none_plus_one_leq_ballot]
                    | some maxVBal2 =>
                      exact option.some_succ_le_some_of_some_le_and_lt
                        h_all_1b_has_ballot_lte_c
                        h_b2_greater_than_c
                  simp_all
              | _ => simp [h_case_m2] at h_m2_acc_a;
            · cases m2_1b with
              | oneb bal2 maxVBal2 maxVal2 acc2 =>
                have h_m2_is_1b := h_S_subsetOf_1b_msgs h_m2_in_S
                obtain ⟨h_m2_in_sent, h_same_ballot⟩ := h_m2_is_1b
                use Message.oneb bal2 maxVBal2 maxVal2 acc2, h_m2_in_sent
                simp [h_same_ballot, h_m2_acc_a, h_b2_less_than_b]
              | _ => simp at h_m2_acc_a;
    -- unique proposal
    · intro m2 h_m2_in_sent'
      by_cases h_m2_in_sent : m2 ∈ sent
      · cases h_m2 : m2 with
        | twoa bal2 val2 =>
          simp; intro h_bal2_eq_b
          have h_exists_prev_2a_with_same_ballot :
              ∃ m ∈ sent, match m with
                          | Message.twoa b' _ => b' = b
                          | _                 => False :=
            ⟨m2, h_m2_in_sent, by simp [h_m2, h_bal2_eq_b]⟩
          exact False.elim (h_no_prev_2a_with_same_ballot h_exists_prev_2a_with_same_ballot)
        | _ => simp
      · simp_all
  -- `m1 ∈ sent`
  · simp [h_m1_in_sent] at h_m1_in_sent'
    cases hm1 : m1 with
      all_goals
      try simp only
      try specialize hInv m1 h_m1_in_sent
      try simp [hm1] at hInv
    | oneb b1 maxVBal maxVal a1 =>
      match maxVBal, maxVal with
      | some maxVBal, some maxVal =>
        apply And.intro ?h_no_vote ?h_inv_1b_2
        · exact votedForIn_stable sent sent' h_mono hInv.left
        · simpa [h_sent_2a_msg, VotedForIn] using hInv.right
      | none, none => simpa [h_votedForIn_same] using hInv.right
      | some maxVBal, none | none, some maxVal =>
        simp only at hInv ⊢
        exact ⟨hInv.left, (by simpa [h_votedForIn_same] using hInv.right)⟩
    | twoa b1 v1 =>
      have ⟨h_safe_at_sent, h_unique_prop⟩ := hInv
      refine And.intro ?safe ?uniq
      · exact safeAt_is_inductive_phase2a sent sent' Quorums h2a h_safe_at_sent
      · intro m2 h_m2_in_sent'
        specialize h_unique_prop m2
        cases m2 with
        | twoa b1' v1' =>
          simp
          intro h_b1_eq_b1'; subst b1'
          by_cases h_m2_in_sent : Message.twoa b1 v1' ∈ sent
          · simp_all
          · unfold Send at h_sent_2a_msg;
            have h_b1_eq_b_and_v1_eq_v : v1' = v := by
              simp [h_sent_2a_msg] at h_m2_in_sent'
              rcases h_m2_in_sent' with (h_eq | h1) <;> simp_all
            simp [*] at *
            exfalso
            refine (h_no_prev_2a_with_same_ballot (Message.twoa b1 v1) h_m1_in_sent ?_)
            simpa [h_m2_in_sent] using h_m2_in_sent'
        | _ => simp
    | twob b1 v1 a1 =>
      match b1, v1 with
      | some b1, some v1 => simp; exact h_mono hInv
      | none, none | some b1, none | none, some v1 => simp;

lemma msginv_is_inductive_phase2b
    (hInv : MsgInv sent Quorums)
    (h2b : Phase2b sent sent' a) : MsgInv sent' Quorums := by
  have h_mono : sent ⊆ sent' := phase2b_imp_mono_sent h2b
  have ⟨m2a, h_m2a_in_sent, hmatch⟩ := h2b
  cases m2a with
  | twoa b v =>
    simp [-Send] at hmatch
    rcases hmatch with ⟨h_no_greater_ballot, h_send⟩
    unfold MsgInv at *
    intro m1 h_m1_in_sent'
    rw [h_send] at h_m1_in_sent'
    rcases Or.symm h_m1_in_sent' with (h_m1_is_2b | h_m1_in_sent)
    · simp_all              -- `m1` is the new `2b` message
    · cases hm1: m1 with    -- `m1 ∈ sent`, we show for each type the invariant holds
      | onea b1 => simp
      | oneb b1 maxVBal maxVal a1 => -- the main effort is for the `1b` case
        simp at hInv; simp [-Send]
        specialize hInv m1 h_m1_in_sent; simp [hm1] at hInv
        have ⟨h_a1_voted, h_a1_not_voted_in_between⟩ := hInv
        constructor
        · match maxVBal, maxVal with
          | some maxVBal, some maxVal =>
            simp at *
            exact votedForIn_stable sent sent' h_mono h_a1_voted
          | none, none => simp
        · intro b' hb'_lower hb'_upper x
          have h_a1_no_votes_in_b' := h_a1_not_voted_in_between b' hb'_lower hb'_upper x
          unfold VotedForIn at *
          simp [h_send]; simp at h_a1_no_votes_in_b'
          constructor
          · intro hb_eq hv_eq ha_eq
            specialize h_a1_not_voted_in_between b' hb'_lower hb'_upper x
            specialize h_no_greater_ballot m1 h_m1_in_sent
            simp [hm1] at h_no_greater_ballot
            have h_b1_le_b : b1 ≤ b := h_no_greater_ballot ha_eq
            rw [hb_eq] at hb'_upper
            have h_contra : b1 < b1 := by
              exact Nat.lt_of_le_of_lt (h_no_greater_ballot ha_eq) hb'_upper
            simp at h_contra
          · exact h_a1_no_votes_in_b'
      | twoa b1 v1 =>
        simp at hInv; simp [-Send]
        specialize hInv m1 h_m1_in_sent; simp [hm1] at hInv
        refine And.intro ?safe ?uniq
        · exact safeAt_is_inductive_phase2b sent sent' Quorums h2b hInv.left
        · have h_inv_unique_prop := hInv.right
          intro m2 h_m2_in_sent'
          specialize h_inv_unique_prop m2
          cases m2 <;> simp_all
      | twob b1 v1 a1 =>
        match b1, v1 with
        | some b1, some v1 => simp; specialize hInv m1 h_m1_in_sent; simp_all
        | none, none | some b1, none | none, some v1 => simp
  | _ => simp [*] at *

/-- THEOREM Invariant in CL. -/
theorem Invariant {σ : ℕ → Set Message}
    (hSpec : PaxosSpec Quorums σ) : ∀ n, MsgInv (σ n) Quorums := by
  intro n
  unfold PaxosSpec Init at *
  rcases hSpec with ⟨hInit, hNext⟩
  induction n with
  | zero   => simp [MsgInv, hInit]
  | succ k ih =>
    let sent := σ k; let sent' := σ (k + 1)
    have hStep := hNext k
    cases hStep with
    | inl hNext =>
      have hInvHoldsPrev: MsgInv sent Quorums := ih
      unfold Next at hNext
      rcases hNext with ⟨b, hPhase1a | hPhase2a⟩ | ⟨a, hPhase1b | hPhase2b⟩
      · exact msginv_is_inductive_phase1a sent sent' Quorums hInvHoldsPrev hPhase1a
      · exact msginv_is_inductive_phase2a sent sent' Quorums hInvHoldsPrev hPhase2a
      · exact msginv_is_inductive_phase1b sent sent' Quorums hInvHoldsPrev hPhase1b
      · exact msginv_is_inductive_phase2b sent sent' Quorums hInvHoldsPrev hPhase2b
    | inr hStutter =>
      rw [←hStutter]; exact ih

/-- MsgInv => Agree in CL. We write it as a seperate lemma. -/
lemma msginv_implies_agree
    (hInv : MsgInv sent Quorums) : Agree sent Quorums := by
  unfold Agree
  rintro v1 v2 ⟨⟨b1, hChosenIn1⟩, ⟨b2, hChosenIn2⟩⟩
  -- we prove the following symmetrical result for it to be used later in the proof
  suffices agree_chosen_in_diff_bal (b1 b2 : Ballot) (v1 v2 : Value)
      (hChosenIn1 : ChosenIn sent Quorums v1 b1)
      (hChosenIn2 : ChosenIn sent Quorums v2 b2)
      (h_b1_lt_b2 : b1 < b2) : v1 = v2
  rcases lt_trichotomy b1 b2 with h_lt | h_eq | h_gt
  · exact agree_chosen_in_diff_bal b1 b2 v1 v2 hChosenIn1 hChosenIn2 h_lt
  · unfold ChosenIn at *
    rcases hChosenIn1 with ⟨Q1, hQ1, h_all_acc_in_Q1_voted_v1⟩
    rcases hChosenIn2 with ⟨Q2, hQ2, h_all_acc_in_Q2_voted_v2⟩
    have ⟨acc_voted_both, h_aa_in_quorum_int⟩ := pick_from_quorum_int Quorums hQ1 hQ2
    specialize h_all_acc_in_Q1_voted_v1 acc_voted_both
    specialize h_all_acc_in_Q2_voted_v2 acc_voted_both
    have hv1 := h_all_acc_in_Q1_voted_v1 (h_aa_in_quorum_int.left)
    have hv2 := h_all_acc_in_Q2_voted_v2 (h_aa_in_quorum_int.right)
    rw [←h_eq] at hv2
    exact VotedOnce sent Quorums hInv hv1 hv2
  · exact Eq.symm (agree_chosen_in_diff_bal b2 b1 v2 v1 hChosenIn2 hChosenIn1 h_gt)
  -- proving `agree_chosen_in_diff_bal`
  have h_v2_safe_at_b2 : SafeAt sent Quorums v2 b2 := by
    unfold ChosenIn at hChosenIn2
    rcases hChosenIn2 with ⟨Q2, hQ2, hVotedQ2⟩
    have ⟨aa, haa⟩ := pick_from_quorum_int Quorums hQ2 hQ2
    refine VotedInv sent Quorums hInv aa v2 b2 ?_
    specialize hVotedQ2 aa; exact (hVotedQ2 haa.left)
  unfold SafeAt at h_v2_safe_at_b2
  specialize h_v2_safe_at_b2 b1
  have h_v2_safe_at_b1 := h_v2_safe_at_b2 h_b1_lt_b2
  rcases h_v2_safe_at_b1 with ⟨Q1, hQ1, hQ_safe_at_b1⟩
  unfold ChosenIn at hChosenIn1
  rcases hChosenIn1 with ⟨Q2, hQ2, hvotedin1⟩
  have ⟨acc_voted_both, h_aa_in_quorum_int⟩ := pick_from_quorum_int Quorums hQ1 hQ2
  have haa_voted_v1_b1 : VotedForIn sent acc_voted_both v1 b1 :=
    hvotedin1 acc_voted_both h_aa_in_quorum_int.right
  have haa_safe_at_b1 := hQ_safe_at_b1 acc_voted_both h_aa_in_quorum_int.left
  cases haa_safe_at_b1 with
  | inl haa_voted_v2_b1 =>
    exact VotedOnce sent Quorums hInv haa_voted_v1_b1 haa_voted_v2_b1
  | inr haa_wont_vote_b1 =>
    unfold WontVoteIn at haa_wont_vote_b1
    rcases haa_wont_vote_b1 with ⟨haa_not_vote_b1, _⟩
    exact (haa_not_vote_b1 v1 haa_voted_v1_b1).elim

/-- THEOREM Agreement in CL. -/
theorem Agreement {σ : ℕ → Set Message}
    (hSpec : PaxosSpec Quorums σ) : ∀ n, Agree (σ n) Quorums := by
  have inv : ∀ n, MsgInv (σ n) Quorums := by
    intro n
    exact Invariant Quorums hSpec n
  exact fun n ↦ msginv_implies_agree (σ n) Quorums (inv n)

end Paxos.Proof
