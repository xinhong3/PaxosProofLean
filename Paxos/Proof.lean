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

-- Setting a higher heartbeat limit for simp.
set_option maxHeartbeats 1000000

/-- lemma VotedInv in CL. -/
lemma VotedInv (h1: MsgInv sent Quorums) :
    ∀ a v b, VotedForIn sent a v b → SafeAt sent Quorums v b := by
  unfold MsgInv VotedForIn at *
  intros a v b h; simp at h
  apply h1 at h; simp at h
  apply h1 at h; simp at h
  exact h.left

/-- lemma VotedOnce in CL. -/
lemma VotedOnce
    (hInv: MsgInv sent Quorums)
    (h_voted_1: VotedForIn sent a1 v1 b)
    (h_voted_2: VotedForIn sent a2 v2 b) : v1 = v2 := by
  unfold VotedForIn MsgInv at *
  have h_exists_2a_with_v1 : Message.twoa b v1 ∈ sent := by
    simp at h_voted_1; apply hInv at h_voted_1; simp at h_voted_1; exact h_voted_1
  have h_exists_2a_with_v2 : Message.twoa b v2 ∈ sent := by
    simp at h_voted_2; apply hInv at h_voted_2; simp at h_voted_2; exact h_voted_2
  apply hInv at h_exists_2a_with_v1; simp at h_exists_2a_with_v1
  apply h_exists_2a_with_v1.right at h_exists_2a_with_v2; simp at h_exists_2a_with_v2
  exact h_exists_2a_with_v2.symm

/-- A template for proving `SafeAtStable`. Each phase only need to provide the proof that
`WontVoteIn sent' a b` holds. -/
lemma safeAt_inductive_template
    (v: Value) (b: Ballot)
    (h_mono : sent ⊆ sent')
    (h_wontVoteIn_preserves : ∀ {a b2}, WontVoteIn sent a b2 → WontVoteIn sent' a b2)
    : SafeAt sent Quorums v b → SafeAt sent' Quorums v b := by
  intro hSafe b2 hxb
  rcases hSafe b2 hxb with ⟨Q, h_Q_in_quorums, h_all_voted_or_wont_vote⟩
  have hV : ∀ {a}, a ∈ Q → VotedForIn sent a v b2 → VotedForIn sent' a v b2 := by
    exact fun {a} a_1 a_2 => votedForIn_monotonic sent sent' h_mono a_2
  refine ⟨Q, h_Q_in_quorums, ?forAllAccInQ_votedFor_or_wontVote⟩
  intro A hA
  cases h_all_voted_or_wont_vote A hA with
  | inl hVoted  => exact Or.inl (hV hA hVoted)
  | inr hWont   => exact Or.inr (h_wontVoteIn_preserves hWont)

-- The following four lemmas show that `SafeAt` is inductive over all four phases.

lemma safeAt_is_inductive_phase1a
    (h1a : Phase1a sent sent' b')
    (hSafe : SafeAt sent Quorums v b) : SafeAt sent' Quorums v b := by
  have h_mono : sent ⊆ sent' := send_monotonic h1a
  unfold Phase1a at h1a
  have h_wontVoteIn_preserves :
      ∀ {A b2}, WontVoteIn sent A b2 → WontVoteIn sent' A b2 := by
    intro A b2 hW; unfold WontVoteIn at *
    constructor
    · simpa [votedForIn_same_if_no_2b_send sent sent' h1a] using hW.left
    · exact exists_mem_of_subset h_mono hW.right
  exact safeAt_inductive_template
          sent sent' Quorums v b h_mono h_wontVoteIn_preserves hSafe

lemma safeAt_is_inductive_phase1b
    (h1b: Phase1b sent sent' a)
    (hSafe: SafeAt sent Quorums v b) : SafeAt sent' Quorums v b := by
  have h_mono : sent ⊆ sent' := by exact phase1b_imp_mono_sent sent sent' h1b
  have h_wontVoteIn_preserves :
      ∀ {A b2}, WontVoteIn sent A b2 → WontVoteIn sent' A b2 := by
    intro A b2 hW; unfold WontVoteIn at *
    constructor
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
  exact safeAt_inductive_template
          sent sent' Quorums v b h_mono h_wontVoteIn_preserves hSafe

lemma safeAt_is_inductive_phase2a
    (h2a : Phase2a Quorums sent sent' b')
    (hSafe : SafeAt sent Quorums v b) : SafeAt sent' Quorums v b := by
  have h_mono : sent ⊆ sent' := phase2a_imp_mono_sent Quorums sent sent' h2a
  rcases h2a with ⟨_, ⟨_,_,_,_,_,_,_, h_send⟩⟩
  have h_wontVoteIn_preserves :
      ∀ {A b2}, WontVoteIn sent A b2 → WontVoteIn sent' A b2 := by
    intro A b2 hW; unfold WontVoteIn at *
    constructor
    · simpa [votedForIn_same_if_no_2b_send sent sent' h_send] using hW.left
    · exact exists_mem_of_subset h_mono hW.right
  exact safeAt_inductive_template
          sent sent' Quorums v b h_mono h_wontVoteIn_preserves hSafe

lemma safeAt_is_inductive_phase2b
    (h2b : Phase2b sent sent' a)
    (hSafe : SafeAt sent Quorums v b) : SafeAt sent' Quorums v b := by
  have h_mono : sent ⊆ sent' := phase2b_imp_mono_sent sent sent' h2b
  have h_wontVoteIn_preserves :
      ∀ {A b2}, WontVoteIn sent A b2 → WontVoteIn sent' A b2 := by
    intro A b2 hW; unfold WontVoteIn at *
    constructor
    · unfold Phase2b at h2b
      rcases h2b with ⟨m2a, h_twoa_in_sent, hmatch⟩
      cases m2a with
      | twoa b1 v1 =>
        simp only at hmatch
        rcases hmatch with ⟨h_no_greater_ballot, h_send⟩
        by_cases ha : a = A
        · have h_not_eq_bal : b2 ≠ b1 := by
            rcases hW with ⟨_, ⟨m_1b_2b, hm_sent, hm_match⟩⟩
            let m_1b_2b_copy := m_1b_2b
            cases m_1b_2b with
            | oneb bb _ _ a1 | twob bb _ a1 =>
              all_goals         -- consolidate the two cases
              simp at hm_match  -- the first three lines are the same
              have hle := h_no_greater_ballot m_1b_2b_copy hm_sent
              simp [hm_match.left, ha, m_1b_2b_copy] at hle
              -- the first `try` handles `1b` case, the second handles `2b` case.
              try exact ne_of_lt (lt_of_lt_of_le hm_match.right hle)
              try cases bb with
                | none    => simp at *
                | some bb => exact ne_of_lt (lt_of_lt_of_le hm_match.right hle)
            | _ => simp at *
          intro V hVoted
          let hNotVotedPrev := hW.left
          specialize hNotVotedPrev V
          unfold VotedForIn at hVoted hNotVotedPrev
          simp [*] at *; exact hNotVotedPrev hVoted
        · intro V hVoted
          let hNotVotedPrev := hW.left
          specialize hNotVotedPrev V
          unfold VotedForIn at hVoted hNotVotedPrev
          simp [h_send] at hVoted
          cases hVoted with
          | inl hVotedCurrent => simp [hVotedCurrent] at ha
          | inr hVotedInPrev => simp [*] at *
      | _ => simp at hmatch
    · exact exists_mem_of_subset h_mono hW.right
  exact safeAt_inductive_template
          sent sent' Quorums v b h_mono h_wontVoteIn_preserves hSafe

/-- lemma SafeAtStable in CL. -/
lemma SafeAtStable {v: Value} {b: Ballot}
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
    (h1a  : Phase1a sent sent' b) : MsgInv sent' Quorums := by
  have h_mono : sent ⊆ sent' := send_monotonic h1a
  have h_no_1b_or_2b_added : ∀ m ∈ sent' \ sent, ¬ (is1b m ∨ is2b m) := by simp_all
  have h_no_2b_added : ∀ m ∈ sent' \ sent, ¬ is2b m := by simp_all
  unfold MsgInv at *
  unfold Phase1a at h1a;
  intro m h_m_in_sent'; rw [h1a] at h_m_in_sent'
  rcases Or.symm h_m_in_sent' with (rfl | h_m_in_sent)  -- whether m is the new message
  · -- Case 1: `m` is the new `onea` message. For `onea`, MsgInv holds trivially.
    simp
  · -- Case 2: `m ∈ sent`. Need to go through each type and show the invariant holds.
    specialize hInv m h_m_in_sent
    cases m with
    | onea _ => simp
    | oneb b1 maxVBal maxVal a1 =>
      simp only at hInv; simp only
      rcases hInv with ⟨hInv_1b_1, hInv_1b_2⟩
      match maxVBal, maxVal with
      | some rbal, some rval =>
        simp only at hInv_1b_1; simp only
        apply And.intro ?h_no_vote ?h_inv_1b_2
        · exact votedForIn_monotonic sent sent' h_mono hInv_1b_1
        · exact oneb_inv_2_stable_if_no_twob_added sent sent' h_mono h_no_2b_added hInv_1b_2
      | none, none =>
        simp only at hInv_1b_1; simp only
        simpa [votedForIn_same_if_no_2b_send sent sent' h1a] using hInv_1b_2
      | some rbal, none | none, some rval =>
        simp at hInv_1b_1
    | twoa b1 v1 =>
      simp only at hInv
      rcases hInv with ⟨hSafeAt, hUnique⟩
      refine And.intro ?safe ?uniq
      · exact safeAt_is_inductive_phase1a sent sent' Quorums h1a hSafeAt
      · intro m2 hm2_in_sent'
        rw [h1a] at hm2_in_sent'
        rcases hm2_in_sent' with (hm2_in_sent | rfl)
        · specialize hUnique m2 hm2_in_sent
          exact hUnique
        · simp
     | twob b1 v1 a1 => cases b1 <;> cases v1 <;> simp [*]

lemma msginv_is_inductive_phase1b
    (hInv : MsgInv sent Quorums)
    (h1b : Phase1b sent sent' a) : MsgInv sent' Quorums := by
  have h_mono : sent ⊆ sent' := by exact phase1b_imp_mono_sent sent sent' h1b
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
      rcases Or.symm hm2 with h_m2_is_1b | h_m2_in_sent
      · -- Case1: m  is the new `1b` message
        simp at h_m2_is_1b; simp only [h_m2_is_1b]
        match rbal, rval with
        | some rbal, some rval =>     -- case when max_prop is non-empty
          simp only
          constructor
          · refine votedForIn_monotonic sent sent' h_mono ?_
            rw [h_r_has_same_acc] at *
            exact max_prop_not_empty_implies_voted_for sent h_r_in_sent
          ·
            have h_inv_1b_2:
                ∀ (b' : Ballot), some rbal + 1 ≤ b' → b' < some mbal → ∀ (x : Value),
                ¬VotedForIn sent a x b' := by
              rw [h_r_has_same_acc] at h_r_in_sent
              intro b' hb'_lower hb'_upper
              have h_not_voted_for_greater_ballots :=
                max_prop_implies_not_voted_for_greater_ballots sent h_r_in_sent b'
              rw [←not_exists]
              have hb'_lower : b' ≥ rbal +1 := by exact hb'_lower
              simp [hb'_lower,
                    -not_exists,
                    ←h_r_has_same_acc] at h_not_voted_for_greater_ballots
              simpa [votedForIn_same_if_no_2b_send sent sent' h_send] using
                h_not_voted_for_greater_ballots
            simpa [votedForIn_same_if_no_2b_send sent sent' h_send] using h_inv_1b_2
        | none, none =>               -- case when max_prop is empty
          simp; rw [←h_r_has_same_acc] at h_r_in_sent
          intro b hb_upper
          have h_not_voted_in_sent :=
            max_prop_empty_implies_not_voted_in_prev_ballots sent h_r_in_sent b
          simpa [votedForIn_same_if_no_2b_send sent sent' h_send] using h_not_voted_in_sent
        | some rbal, none | none, some rval =>
          rw [h_r_has_same_acc] at h_r_in_sent
          apply max_prop_empty_ballot_iff_empty_value at h_r_in_sent
          simp at h_r_in_sent
      · cases m2 with
        | onea b1 => simp
        | oneb b1 maxVBal maxVal a1 =>
          simp only at hInv; simp only
          have h_mono : sent ⊆ sent' := by exact send_monotonic h_send
          have h_no_2b_added : ∀ m ∈ sent' \ sent, ¬ is2b m := by simp_all
          rcases (hInv (Message.oneb b1 maxVBal maxVal a1) h_m2_in_sent) with
                   ⟨hInv_1b_1, hInv_1b_2⟩
          match maxVBal, maxVal with
          | some rbal, some rval =>
            simp only at hInv_1b_1; simp only
            constructor
            · exact votedForIn_monotonic sent sent' h_mono hInv_1b_1
            · exact oneb_inv_2_stable_if_no_twob_added sent sent' h_mono h_no_2b_added hInv_1b_2
          | none, none =>
            simp only at hInv_1b_1; simp only [true_and]
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
    (hInv: MsgInv sent Quorums)
    (h2a: Phase2a Quorums sent sent' b) : MsgInv sent' Quorums := by
  have h_mono : sent ⊆ sent' := by exact phase2a_imp_mono_sent Quorums sent sent' h2a
  have ⟨h_no_prev_2a_with_same_ballot,
        ⟨v, Q, S, h_Q_in_quorums, h_S_subsetOf_1b_msgs,h_all_acc_in_Q_sent_1b,
        h_all_acc_none_voted_or_some_voted, h_sent_2a_msg⟩⟩ := h2a
  have h_no_2b_added : ∀ m ∈ sent' \ sent, ¬ is2b m := by simp_all
  have h_votedForIn_same : ∀ a v b, VotedForIn sent a v b ↔ VotedForIn sent' a v b := by
    intro a v b
    unfold VotedForIn
    simp [h_sent_2a_msg]
  unfold MsgInv; unfold MsgInv at hInv
  intro m1 h_m1_in_sent'; rw [h_sent_2a_msg] at h_m1_in_sent'
  rcases Or.symm h_m1_in_sent' with (rfl | h_m1_in_sent)
  -- m1 is the new 2a message
  · simp
    constructor
    -- ⊢ SafeAt sent' Quorums v b
    -- We prove this by showing SafeAt sent Quorums v b and use SafeAtStable
    · have h_safe_at_prev : SafeAt sent Quorums v b := by
        cases' h_all_acc_none_voted_or_some_voted with h_none_voted h_some_voted
        -- first case: no acceptors in S has voted in the past (`maxVBal = none`)
        · unfold SafeAt
          intro b2 h_b2_less_than_b
          use Q, h_Q_in_quorums
          -- ⊢ ∀ a ∈ Q, VotedForIn sent a v b2 ∨ WontVoteIn sent a b2
          intro a haQ
          right       -- only need to show WontVoteIn sent a b2 (since none voted)
          have ⟨m1, hm1S, hm1_match⟩ := h_all_acc_in_Q_sent_1b a haQ
          unfold WontVoteIn
          constructor
          -- ⊢ ∀ (v : Value), ¬VotedForIn sent a v b2
          · cases m1 with
            | oneb bal1 maxVBal1 maxVal1 acc1 =>
              let m1 := Message.oneb bal1 maxVBal1 maxVal1 acc1
              have h_m1_in_sent : m1 ∈ sent := by
                exact Set.mem_of_mem_inter_left (h_S_subsetOf_1b_msgs hm1S)
              have bal1_eq : bal1 = b := by
                rcases h_S_subsetOf_1b_msgs hm1S with ⟨_, h_match_m1_eq_b⟩
                simp [h_match_m1_eq_b]
              simp at hm1_match
              specialize h_none_voted m1 hm1S
              simp [m1] at h_none_voted
              have hInv_1b := hInv m1 h_m1_in_sent
              simp [m1] at hInv_1b
              simpa [h_none_voted, h_b2_less_than_b, bal1_eq, hm1_match] using
                hInv_1b.right b2
            | _ => simp at hm1_match;
          -- showing there is some 1b message with greater ballot
          · cases m1 with
            | oneb bal1 maxVBal1 maxVal1 acc1 =>        -- we only care about 1b
              let m1 := Message.oneb bal1 maxVBal1 maxVal1 acc1
              have h_m1_in_sent : m1 ∈ sent := by
                exact Set.mem_of_mem_inter_left (h_S_subsetOf_1b_msgs hm1S)
              have bal1_eq : bal1 = b := by
                rcases h_S_subsetOf_1b_msgs hm1S with ⟨_, h_match_m1_eq_b⟩
                simp [h_match_m1_eq_b]
              use m1, h_m1_in_sent
              simp [m1, hm1_match, bal1_eq, h_b2_less_than_b]
            | _ => simp at hm1_match;  -- the rest can be done by simp
        -- second case: some acceptor has voted in the past (`maxVBal ≠ none`)
        · -- ⊢ SafeAt sent Quorums v b
          unfold SafeAt
          intro b2 h_b2_less_than_b
          rcases h_some_voted with
            ⟨c, h_c_gte_zero, h_c_lt_b, ⟨h_all_1b_has_ballot_lt_c, h_some_1b_has_ballot_c⟩⟩
          by_cases h_b2_less_than_c : b2 < c
          -- ⊢ ∃ Q ∈ Quorums, ∀ a ∈ Q, VotedForIn sent a v b2 ∨ WontVoteIn sent a b2
          · rcases h_some_1b_has_ballot_c with
              ⟨m1b_ballot_c, h_m1b_in_S, h_m1b_match⟩
            cases m1b_ballot_c with
            | oneb bal_c mc_vbal mc_val mc_acc =>
              match mc_vbal, mc_val with
              | some mc_vbal, some mc_val =>
                let mc := Message.oneb bal_c mc_vbal mc_val mc_acc
                have ⟨mc_in_sent, _⟩ := h_S_subsetOf_1b_msgs h_m1b_in_S
                have hInv_2b := hInv mc mc_in_sent
                simp at h_m1b_match
                simp [mc, h_m1b_match] at hInv_2b
                have h_safe_at_c : SafeAt sent Quorums mc_val mc_vbal := by
                  have h_voted_acc : VotedForIn sent mc_acc mc_val mc_vbal := by
                    simp [h_m1b_match, hInv_2b.left]
                  exact VotedInv sent Quorums hInv mc_acc mc_val mc_vbal h_voted_acc
                unfold SafeAt at h_safe_at_c
                rw [h_m1b_match.left, h_m1b_match.right] at h_safe_at_c
                specialize h_safe_at_c b2 h_b2_less_than_c
                simp [h_safe_at_c]
              | none, some mc_val => simp at h_m1b_match;
              | some mc_vbal, none => simp at h_m1b_match;
              | none, none => simp at h_m1b_match;
            | _ => simp at h_m1b_match;
          -- ⊢ ∃ Q ∈ Quorums, ∀ a ∈ Q, VotedForIn sent a v b2 ∨ WontVoteIn sent a b2
          use Q, h_Q_in_quorums
          intro a haQ
          · by_cases h_b2_eq_c : b2 = c
            · rcases h_some_1b_has_ballot_c with ⟨m1b_ballot_c, h_m1b_in_S, h_m1b_match⟩
              cases m1b_ballot_c with
              | oneb bal_c mc_vbal mc_val mc_acc =>
                match mc_vbal, mc_val with
                | some mc_vbal, some mc_val =>
                  let mc := Message.oneb bal_c mc_vbal mc_val mc_acc
                  simp at h_m1b_match
                  have ⟨h_vbal_eq_c, h_mc_val_eq_v⟩ := h_m1b_match
                  have h_voted_acc_c : VotedForIn sent mc_acc mc_val mc_vbal := by
                    have ⟨mc_in_sent, _⟩ := h_S_subsetOf_1b_msgs h_m1b_in_S
                    have h_inv_mc := hInv mc mc_in_sent
                    simp [mc] at h_inv_mc
                    exact h_inv_mc.left
                  rw [h_vbal_eq_c, h_mc_val_eq_v] at h_voted_acc_c
                  have h_all_voted_in_c_for_v :
                      ∀ q ∈ Q, ∀ (w: Value), VotedForIn sent q w c → w = v := by
                    intro q h_q_in_Q w h_voted
                    exact VotedOnce sent Quorums hInv h_voted h_voted_acc_c
                  -- the following shows that either a has voted for v in b2,
                  --  or it won't vote in b2. Note that c = b2 in this case.
                  by_cases h_a_voted_in_c : VotedForIn sent a v c
                  · left  -- if a has voted for v in c, we are done
                    simp [h_b2_eq_c, h_a_voted_in_c]
                  · right -- otherwise, we show that it won't vote in c
                    unfold WontVoteIn
                    constructor
                    · intro w h_voted
                      rw [h_b2_eq_c] at h_voted
                      have h_voted_eq_v := h_all_voted_in_c_for_v a haQ w h_voted
                      rw [h_voted_eq_v] at h_voted
                      exact h_a_voted_in_c h_voted
                    · specialize h_all_acc_in_Q_sent_1b a haQ
                      obtain ⟨m2_1b, h_m2_in_S, hm2_match⟩ := h_all_acc_in_Q_sent_1b
                      cases m2_1b with
                      | oneb bal2 maxVBal2 maxVal2 acc2 =>
                        simp at hm2_match
                        have h_m2_is_oneb := h_S_subsetOf_1b_msgs h_m2_in_S
                        simp at h_m2_is_oneb
                        have h_m2_in_sent := h_m2_is_oneb.left
                        use Message.oneb bal2 maxVBal2 maxVal2 acc2, h_m2_in_sent
                        simp [h_m2_is_oneb.2, hm2_match, h_b2_less_than_b]
                      | _ => simp at hm2_match;
              | _ => simp at h_m1b_match;
            · have h_b2_greater_than_c : c < b2 := by
                have h_total := lt_trichotomy c b2
                rcases h_total with (h_total_left | h_total_mid | h_total_r)
                · exact h_total_left
                · simp [h_total_mid] at h_b2_eq_c
                · simp [h_total_r] at h_b2_less_than_c
              right
              specialize h_all_acc_in_Q_sent_1b a haQ
              obtain ⟨m2_1b, h_m2_in_S, hm2_match⟩ := h_all_acc_in_Q_sent_1b
              constructor
              · have hm2_sent := (h_S_subsetOf_1b_msgs h_m2_in_S).1
                cases h_case_m2: m2_1b with
                | oneb bal2 maxVBal2 maxVal2 acc2 =>
                  have acc_eq : acc2 = a := by simpa [h_case_m2] using hm2_match
                  specialize hInv m2_1b hm2_sent
                  simp [h_case_m2] at hInv
                  rcases hInv with ⟨_, h_lim⟩
                  have no_ex : ∀ x, ¬VotedForIn sent acc2 x b2 := by
                    specialize h_lim b2
                    specialize h_all_1b_has_ballot_lt_c m2_1b h_m2_in_S
                    simp [h_case_m2] at h_all_1b_has_ballot_lt_c
                    have h_lower : maxVBal2 + (1 : Nat) ≤ some b2 := by
                      cases maxVBal2 with
                      | none => simp
                      | some maxVBal2 =>
                        exact option.some_succ_le_some_of_some_le_and_lt
                          h_all_1b_has_ballot_lt_c
                          h_b2_greater_than_c
                    have h_upper : b2 < bal2 := by
                      rcases h_S_subsetOf_1b_msgs h_m2_in_S with ⟨_, h_m2_match_bal_eq_b⟩
                      simp [h_case_m2] at h_m2_match_bal_eq_b
                      simp only [h_m2_match_bal_eq_b, h_b2_less_than_b]
                    exact (h_lim h_lower h_upper)
                  rw [acc_eq] at no_ex; exact no_ex
                | _ => simp [h_case_m2] at hm2_match;
              · cases m2_1b with
                | oneb bal2 maxVBal2 maxVal2 acc2 =>
                  simp at hm2_match
                  have h_m2_is_oneb := h_S_subsetOf_1b_msgs h_m2_in_S
                  simp at h_m2_is_oneb
                  have h_m2_in_sent := h_m2_is_oneb.left
                  use Message.oneb bal2 maxVBal2 maxVal2 acc2, h_m2_in_sent
                  simp [h_m2_is_oneb.2, hm2_match, h_b2_less_than_b]
                | _ => simp at hm2_match;
      exact safeAt_is_inductive_phase2a sent sent' Quorums h2a h_safe_at_prev
    -- unique proposal
    · intro m2 h_m2_in_sent'
      by_cases h_m2_in_sent : m2 ∈ sent
      · cases h_m2 : m2 with
        | twoa bal2 val2 =>
          simp; intro h_bal2_eq_b
          have h_exists_prev_2a_with_same_ballot : ∃ m ∈ sent, match m with
                                             | Message.twoa b' _ => b' = b
                                             | _                 => False :=
            ⟨m2, h_m2_in_sent, by simp [h_m2, h_bal2_eq_b]⟩
          exact False.elim (h_no_prev_2a_with_same_ballot h_exists_prev_2a_with_same_ballot)
        | _ => simp
      · have h_m2_eq_2a : m2 = Message.twoa b v := by simp_all
        simp [h_m2_eq_2a]
  -- `m1 ∈ sent`, need to show for each type the invariant holds
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
        · exact votedForIn_monotonic sent sent' h_mono hInv.left
        · simpa [h_sent_2a_msg, VotedForIn] using hInv.right
      | none, none => simp; simpa [h_votedForIn_same] using hInv.right
      | some maxVBal, none | none, some maxVal =>
        simp only at *
        exact ⟨hInv.left, (by simpa [h_votedForIn_same] using hInv.right)⟩
    | twoa b1 v1 =>   -- For 2a message in sent
      refine And.intro ?safe ?uniq
      · exact safeAt_is_inductive_phase2a sent sent' Quorums h2a hInv.left
      · have h_inv_unique_prop := hInv.right
        intro m2 h_m2_in_sent'
        specialize h_inv_unique_prop m2
        cases m2 with
        | twoa b1' v1' =>
          simp
          intro h_same_ballot_b1_b1'
          by_cases h_m2_in_sent : Message.twoa b1' v1' ∈ sent
          · simp [h_m2_in_sent] at h_inv_unique_prop
            simp [h_inv_unique_prop, h_same_ballot_b1_b1']
          · unfold Send at h_sent_2a_msg;
            have h_b1_eq_b_and_v1_eq_v : Message.twoa b1' v1' = Message.twoa b v := by
              simp [h_sent_2a_msg] at h_m2_in_sent'
              rcases h_m2_in_sent' with (h_eq | h1)
              · simp [h_eq]
              · exact False.elim (h_m2_in_sent h1)
            simp at h_b1_eq_b_and_v1_eq_v
            simp [*] at *
            exfalso
            exact (h_no_prev_2a_with_same_ballot
                  (Message.twoa b1 v1) h_m1_in_sent (id (Eq.symm h_same_ballot_b1_b1')))
        | _ => simp
    | twob b1 v1 a1 =>
      match b1, v1 with
      | some b1, some v1 => simp; exact h_mono hInv
      | none, none | some b1, none | none, some v1 => simp;

lemma msginv_is_inductive_phase2b
    (hInv: MsgInv sent Quorums)
    (h2b: Phase2b sent sent' a) : MsgInv sent' Quorums := by
  have h_mono : sent ⊆ sent' := by exact phase2b_imp_mono_sent sent sent' h2b
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
            exact votedForIn_monotonic sent sent' h_mono h_a1_voted
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
theorem Invariant {σ: ℕ → Set Message}
    (hSpec : PaxosSpec Quorums σ) : ∀ n, MsgInv (σ n) Quorums := by
  intro n
  unfold PaxosSpec Init at *
  induction n with
  | zero   =>
    simp [MsgInv, hSpec.1]
  | succ k ih =>
    let sent := σ k; let sent' := σ (k + 1)
    have hStep := hSpec.right k
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
  have agree_chosen_in_diff_bal (b1 b2: Ballot) (v1 v2: Value)
      (hChosenIn1: ChosenIn sent Quorums v1 b1)
      (hChosenIn2: ChosenIn sent Quorums v2 b2)
      (h_b1_lt_b2: b1 < b2) : v1 = v2 := by
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
  by_cases h_eq : b1 = b2
  · unfold ChosenIn at *
    rcases hChosenIn1 with ⟨Q1, hQ1, h_all_acc_in_Q1_voted_v1⟩
    rcases hChosenIn2 with ⟨Q2, hQ2, h_all_acc_in_Q2_voted_v2⟩
    have ⟨acc_voted_both, h_aa_in_quorum_int⟩ := pick_from_quorum_int Quorums hQ1 hQ2
    specialize h_all_acc_in_Q1_voted_v1 acc_voted_both
    specialize h_all_acc_in_Q2_voted_v2 acc_voted_both
    have hv1 := h_all_acc_in_Q1_voted_v1 (And.left h_aa_in_quorum_int)
    have hv2 := h_all_acc_in_Q2_voted_v2 (And.right h_aa_in_quorum_int)
    rw [←h_eq] at hv2
    exact VotedOnce sent Quorums hInv hv1 hv2
  by_cases h_lt: b1 < b2
  · exact agree_chosen_in_diff_bal b1 b2 v1 v2 hChosenIn1 hChosenIn2 h_lt
  · have h_nlt: b2 < b1 := by
      have h_total := lt_trichotomy b1 b2
      rcases h_total with (h_total_left | h_total_mid | h_total_r) <;> simp [*] at *
    exact id (agree_chosen_in_diff_bal b2 b1 v2 v1 hChosenIn2 hChosenIn1 h_nlt).symm

/-- THEOREM Agreement in TLAPS. -/
theorem Agreement {σ : ℕ → Set Message}
    (hSpec : PaxosSpec Quorums σ) : ∀ n, Agree (σ n) Quorums := by
  have inv : ∀ n, MsgInv (σ n) Quorums := by
    intro n
    exact Invariant Quorums hSpec n
  exact fun n ↦ msginv_implies_agree (σ n) Quorums (inv n)

end Paxos.Proof
