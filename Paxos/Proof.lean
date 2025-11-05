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


/-- A template for proving `SafeAtStable`. For each phase, we only need to show that
`WontVoteIn` is preserved from `sent` to `sent'`. In other words, each phase only needs to
provide a proof for `h_wontVoteIn_preserves`. -/
lemma safeAt_inductive_template
    (v: Value) (b: Ballot)
    (h_sent_monotonic : sent ⊆ sent')
    (h_wontVoteIn_preserves : ∀ {a b2}, WontVoteIn sent a b2 → WontVoteIn sent' a b2)
    : SafeAt sent Quorums v b → SafeAt sent' Quorums v b := by
  intro hSafe
  unfold SafeAt at *
  intro b2 hxb
  rcases hSafe b2 hxb with ⟨Q, hQ, hAll⟩
  have hV : ∀ {a}, a ∈ Q → VotedForIn sent a v b2 → VotedForIn sent' a v b2 := by
    exact fun {a} a_1 a_2 => votedForIn_monotonic sent sent' h_sent_monotonic a_2
  refine ⟨Q, hQ, ?_⟩
  intro A hA
  cases hAll A hA with
  | inl hVoted  => exact Or.inl (hV hA hVoted)
  | inr hWont   => exact Or.inr (h_wontVoteIn_preserves hWont)

-- The following four lemmas show that `SafeAt` is inductive over all four phases.

lemma safeAt_is_inductive_phase1a
    (h1a : Phase1a sent sent' b')
    (hSafe : SafeAt sent Quorums v b) : SafeAt sent' Quorums v b := by
  have h_mono : sent ⊆ sent' := send_monotonic h1a
  have h_wontVoteIn_preserves :
      ∀ {A b2}, WontVoteIn sent A b2 → WontVoteIn sent' A b2 := by
    intro A b2 hW; unfold WontVoteIn at *
    constructor
    · refine send_add_non_twob_preserves_no_vote sent sent' hW.left h1a ?_
      exact Or.inl (exists_apply_eq_apply' Message.onea b')
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
      rcases h1b with ⟨m, hm, r, hr, hmatch⟩
      cases m with
      | onea _ =>
        cases r with
        | twob _ _ _ =>
          simp [-Send] at hmatch
          refine send_add_non_twob_preserves_no_vote sent sent' hW.left hmatch.right ?_
          exact Or.inr (Or.inl (by simp))
        | _ => simp at *
      | _ => simp at *
    · exact exists_mem_of_subset h_mono hW.right
  exact safeAt_inductive_template
          sent sent' Quorums v b h_mono h_wontVoteIn_preserves hSafe

lemma safeAt_is_inductive_phase2a
    (h2a : Phase2a Quorums sent sent' b')
    (hSafe : SafeAt sent Quorums v b) : SafeAt sent' Quorums v b := by
  have h_mono : sent ⊆ sent' := phase2a_imp_mono_sent Quorums sent sent' h2a
  have h_wontVoteIn_preserves :
      ∀ {A b2}, WontVoteIn sent A b2 → WontVoteIn sent' A b2 := by
    intro A b2 hW; unfold WontVoteIn at *
    constructor
    · rcases h2a with ⟨_, ⟨_,_,_,_,_,_,_, h_send⟩⟩
      refine send_add_non_twob_preserves_no_vote sent sent' hW.left h_send ?_
      exact Or.inr (Or.inr (by simp))
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
        simp [-Send] at hmatch
        rcases hmatch with ⟨hpo, h_send⟩
        by_cases ha : a = A
        · have h_not_eq_bal : b2 ≠ b1 := by
            rcases hW with ⟨_, ⟨m_1b_2b, hm_sent, hm_match⟩⟩
            let m_1b_2b_c := m_1b_2b
            cases m_1b_2b with
            | oneb bb _ _ a1 | twob bb _ a1 =>
              all_goals         -- consolidate the two cases
              simp at hm_match
              have hle := hpo m_1b_2b_c hm_sent
              simp [hm_match.left, ha, m_1b_2b_c] at hle
              -- specific to oneb
              try exact ne_of_lt (lt_of_lt_of_le hm_match.right hle)
              -- specific to twob
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
    (hInv: MsgInv sent Quorums)
    (h1a: Phase1a sent sent' b) : MsgInv sent' Quorums := by
  have h_sent_monotonic : sent ⊆ sent' := by
    unfold Phase1a at h1a
    exact send_monotonic h1a
  have h1a_copy := h1a
  unfold Phase1a at h1a; unfold MsgInv at *
  rw [h1a]
  intro m h_m_in_sent'
  by_cases h_m_eq_onea_msg : m = Message.onea b
  · simp [*] at *
  · have h_m_in_sent : m ∈ sent := by
      simp [h_m_eq_onea_msg] at h_m_in_sent'; exact h_m_in_sent'
    specialize hInv m h_m_in_sent
    cases m with
    | onea b1 => simp
    | oneb b1 maxVBal maxVal a1 =>
      simp at hInv; simp [-Send]
      match maxVBal, maxVal with
      | some maxVBal, some maxVal =>
        simp [-Send]; simp at hInv
        apply And.intro
        · rw [←h1a]
          exact votedForIn_monotonic sent sent' h_sent_monotonic hInv.left
        · intro b' hb_lower hb_upper
          have h_not_voted := hInv.right
          specialize h_not_voted b'
          simp [hb_lower, hb_upper] at h_not_voted
          rw [←h1a]
          refine send_add_non_twob_preserves_no_vote sent sent' h_not_voted h1a (by simp)
      | none, some maxVal | some maxVBal, none => simp at hInv;
      | none, none =>
        simp [-Send]; simp at hInv;
        intro b' hb_lower
        have h_not_voted := hInv
        specialize h_not_voted b'
        simp [hb_lower] at h_not_voted
        rw [←h1a]
        refine send_add_non_twob_preserves_no_vote sent sent' h_not_voted h1a (by simp)
    | twoa b1 v1 =>
      simp at hInv; simp [-Send]
      rw [←h1a]
      apply And.intro
      · exact safeAt_is_inductive_phase1a sent sent' Quorums h1a_copy hInv.left
      · have h_inv_right := hInv.right
        intro m2 h_m2_in_sent'
        specialize h_inv_right m2
        cases m2 <;> simp [*] at *; apply h_inv_right at h_m2_in_sent'; exact h_m2_in_sent'
    | twob b1 v1 a1 =>
      match b1, v1 with
      | some b1, some v1 => simp [hInv]
      | none, some v1 | some b1, none | none, none => simp;

lemma msginv_is_inductive_phase1b
    (hInv: MsgInv sent Quorums)
    (h1b: Phase1b sent sent' a) : MsgInv sent' Quorums := by
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
      have h_sent_monotonic : sent ⊆ sent' := by exact send_monotonic hmatch.right
      have h_votedForIn_same :
          ∀ a v b, VotedForIn sent a v b ↔ VotedForIn sent' a v b := by
        intro a v b
        unfold VotedForIn
        simp [hmatch]
      unfold MsgInv at hInv; unfold MsgInv
      have h_exists_b_v_with_same_acceptor := mem_max_prop_is_twob sent hr
      intro m' hm'
      -- m' is the witness message sent
      by_cases h_m_eq_oneb : m' = Message.oneb mbal rbal rval a
      · simp [h_m_eq_oneb]
        match rbal, rval with
        | some rbal, none | none, some rval =>
          simp; unfold Phase1b at h1b_copy
          rw [h_same_accptor] at hr
          apply max_prop_empty_ballot_iff_empty_value at hr
          simp at hr
        | none, none =>
          simp; rw [←h_same_accptor] at hr
          intro b hb_upper
          have h_not_voted_in_sent :=
            max_prop_empty_implies_not_voted_in_prev_ballots sent hr b
          exact fun x ↦
            (fun {a b} ha ↦ (iff_false_left ha).mp) (h_not_voted_in_sent x)
              (h_votedForIn_same a x b)
        | some rbal, some rval =>
          simp
          constructor
          · refine votedForIn_monotonic sent sent' h_sent_monotonic ?_
            rw [h_same_accptor] at *
            exact max_prop_not_empty_implies_voted_for sent hr
          · have h_not_voted_for_greater_ballots :
                ∀ (b' : Ballot), rbal + 1 ≤ b' → b' < mbal → ∀ (x : Value),
                ¬VotedForIn sent a x b' := by
              rw [h_same_accptor] at hr
              have h_not_voted_for_greater_ballots :=
                max_prop_implies_not_voted_for_greater_ballots sent hr
              intro b' hb_lower hb_upper x
              specialize h_not_voted_for_greater_ballots b' x hb_lower
              simp [h_same_accptor]; exact h_not_voted_for_greater_ballots
            -- I think the goal is clear enough but for the following:
            -- simp [h_not_voted_for_greater_ballots, h_votedForIn_same] didn't work.
            exact fun b' a_1 a_2 x ↦
              (fun {a b} ha ↦ (iff_false_left ha).mp)
                (h_not_voted_for_greater_ballots b' a_1 a_2 x) (h_votedForIn_same a x b')
        -- TODO: The following part is repetitive, as I copied this from the 1a case
        -- and just changes a few things. How to get rid of this repetition?
      · have h_m'_in_sent : m' ∈ sent := by
          simp [*] at *; simp [h_m_eq_oneb] at hm'; exact hm'
        cases hm' : m' with
        | onea b1 => simp
        | oneb b1 maxVBal maxVal a1 =>
          simp at hInv; simp [-Send]
          match maxVBal, maxVal with
          | none, none =>
            simp
            specialize hInv m' h_m'_in_sent; simp [hm'] at hInv;
            exact fun b' a x ↦
              (fun {a b} ha ↦ (iff_false_left ha).mp)
                (hInv b' a x) (h_votedForIn_same a1 x b')
          | some maxVBal, none | none, some maxVal =>
            simp;
            specialize hInv m' h_m'_in_sent
            simp [hm'] at hInv;
          | some maxVBal, some maxVal =>
            simp [-Send]; specialize hInv m' h_m'_in_sent; simp [hm'] at hInv
            apply And.intro
            · rw [←h_votedForIn_same]; exact hInv.left
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
          apply And.intro
          · exact safeAt_is_inductive_phase1b sent sent' Quorums h1b_copy hInv.left
          · have h_inv_right := hInv.right
            intro m2 h_m2_in_sent'
            specialize h_inv_right m2
            cases m2 <;>  simp [*] at *;
                          apply h_inv_right at h_m2_in_sent';
                          exact h_m2_in_sent'
        | twob b1 v1 a1 =>
          match b1, v1 with
          | none, none | some b1, none | none, some v1 => simp;
          | some b1, some v1 =>
            simp
            specialize hInv m' h_m'_in_sent
            simp [hm'] at hInv
            exact h_sent_monotonic hInv
    | _ => simp at hmatch
  | _ => simp at hmatch

lemma msginv_is_inductive_phase2a
    (hInv: MsgInv sent Quorums)
    (h2a: Phase2a Quorums sent sent' b) : MsgInv sent' Quorums := by
  have h2a_copy := h2a
  unfold Phase2a at h2a
  rcases h2a with ⟨h_no_prev_2a_msg, ⟨v, Q, S, h_Q_in_quorums, h_S_set_of_oneb,
                                    h_all_acc_in_Q_sent_oneb,
                                    h_all_not_voted_or_some_voted,
                                    h2a⟩⟩
  have h_sent_monotonic : sent ⊆ sent' := by exact send_monotonic h2a
  have h_votedForIn_same : ∀ a v b, VotedForIn sent a v b ↔ VotedForIn sent' a v b := by
    intro a v b
    unfold VotedForIn
    simp [h2a]
  unfold MsgInv; unfold MsgInv at hInv
  intro m' hm_sent'
  by_cases h_m_eq_t2a : m' = Message.twoa b v
  · simp [h_m_eq_t2a]
    constructor
    -- ⊢ SafeAt sent' Quorums v b
    -- We prove this by showing SafeAt sent Quorums v b and use SafeAtStable
    · have h_safe_at_prev : SafeAt sent Quorums v b := by
        cases' h_all_not_voted_or_some_voted with h_none_voted h_some_voted
        -- first case: no acceptors in S has voted in the past (`maxVBal = none`)
        · unfold SafeAt
          intro b2 h_b2_less_than_b
          use Q; simp [h_Q_in_quorums]
          -- ⊢ ∀ a ∈ Q, VotedForIn sent a v b2 ∨ WontVoteIn sent a b2
          intro a haQ
          right       -- only need to show WontVoteIn sent a b2 (since none voted)
          have ⟨m1, hm1S, hm1_match⟩ := h_all_acc_in_Q_sent_oneb a haQ
          unfold WontVoteIn
          constructor
          -- ⊢ ∀ (v : Value), ¬VotedForIn sent a v b2
          · cases m1 with
            | oneb bal1 maxVBal1 maxVal1 acc1 =>
              let m1 := Message.oneb bal1 maxVBal1 maxVal1 acc1
              have h_m1_in_sent : m1 ∈ sent := by
                exact Set.mem_of_mem_inter_left (h_S_set_of_oneb hm1S)
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
              simp [h_none_voted, h_b2_less_than_b, bal1_eq, hm1_match] at h_target
              exact h_target
            | _ => simp at hm1_match;
          -- showing there is some 1b message with greater ballot
          · cases m1 with
            | oneb bal1 maxVBal1 maxVal1 acc1 =>        -- we only care about 1b
              let m1 := Message.oneb bal1 maxVBal1 maxVal1 acc1
              have h_m1_in_sent : m1 ∈ sent := by
                exact Set.mem_of_mem_inter_left (h_S_set_of_oneb hm1S)
              have bal1_eq : bal1 = b := by
                rcases h_S_set_of_oneb hm1S with ⟨_, h_match_m1_eq_b⟩
                simp [h_match_m1_eq_b]
              use m1, h_m1_in_sent; simp [m1]
              simp [hm1_match, bal1_eq, h_b2_less_than_b]
            | _ => simp at hm1_match;  -- the rest can be done by simp
        -- second case: some acceptor has voted in the past (`maxVBal ≠ none`)
        · -- ⊢ SafeAt sent Quorums v b
          unfold SafeAt
          intro b2 h_b2_less_than_b
          rcases h_some_voted with
            ⟨c,
              h_c_greater_than_zero,
              h_c_less_than_b,
              ⟨h_all_messgae_in_S_less_than_c,
              h_some_message_in_S_equals_C⟩⟩
          by_cases h_b2_less_than_c : b2 < c
          -- ⊢ ∃ Q ∈ Quorums, ∀ a ∈ Q, VotedForIn sent a v b2 ∨ WontVoteIn sent a b2
          · rcases h_some_message_in_S_equals_C with
              ⟨m_with_ballot_c, h_m_c_in_S, h_m_c_match⟩
            cases m_with_ballot_c with
            | oneb bal_c mc_vbal mc_val mc_acc =>
              match mc_vbal, mc_val with
              | some mc_vbal, some mc_val =>
                let mc := Message.oneb bal_c mc_vbal mc_val mc_acc
                have ⟨mc_in_sent, _⟩ := h_S_set_of_oneb h_m_c_in_S
                have hInv_2b := hInv mc mc_in_sent
                simp at h_m_c_match
                simp [mc, h_m_c_match] at hInv_2b
                have h_safe_at_c : SafeAt sent Quorums mc_val mc_vbal := by
                  have h_voted_acc : VotedForIn sent mc_acc mc_val mc_vbal := by
                    simp [h_m_c_match, hInv_2b.left]
                  exact VotedInv sent Quorums hInv mc_acc mc_val mc_vbal h_voted_acc
                unfold SafeAt at h_safe_at_c
                rw [h_m_c_match.left, h_m_c_match.right] at h_safe_at_c
                specialize h_safe_at_c b2 h_b2_less_than_c
                simp [h_safe_at_c]
              | none, some mc_val => simp at h_m_c_match;
              | some mc_vbal, none => simp at h_m_c_match;
              | none, none => simp at h_m_c_match;
            | _ => simp at h_m_c_match;
          -- ⊢ ∃ Q ∈ Quorums, ∀ a ∈ Q, VotedForIn sent a v b2 ∨ WontVoteIn sent a b2
          · by_cases h_b2_eq_c : b2 = c
            · rcases h_some_message_in_S_equals_C with
                ⟨m_with_ballot_c, h_m_c_in_S, h_m_c_match⟩
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
                    simp [h_m_c_match.right]
                  have h_voted_acc_c : VotedForIn sent mc_acc mc_val mc_vbal := by
                    have ⟨mc_in_sent, _⟩ := h_S_set_of_oneb h_m_c_in_S
                    have h_inv_mc := hInv mc mc_in_sent
                    simp [mc] at h_inv_mc
                    exact h_inv_mc.left
                  rw [h_vbal_eq_c, h_mc_val_eq_v] at h_voted_acc_c
                  have h_all_voted_in_c_for_v :
                      ∀ q ∈ Q, ∀ (w: Value), VotedForIn sent q w c → w = v := by
                    intro q h_q_in_Q w h_voted
                    exact VotedOnce sent Quorums hInv h_voted h_voted_acc_c
                  use Q; simp [h_Q_in_quorums]
                  intro a haQ
                  -- the following shows that either a has voted for v in b2,
                  --  or it won't vote in b2. Note that c = b2 in this case.
                  by_cases h_a_voted_in_c : VotedForIn sent a v c
                    -- if a has voted for v in c, we are done
                  · left
                    simp [h_b2_eq_c, h_a_voted_in_c]
                    -- otherwise, we show that it won't vote in c
                  · right
                    unfold WontVoteIn
                    constructor
                    · intro w h_voted
                      rw [h_b2_eq_c] at h_voted
                      have h_voted_eq_v := h_all_voted_in_c_for_v a haQ w h_voted
                      rw [h_voted_eq_v] at h_voted
                      exact h_a_voted_in_c h_voted
                    · specialize h_all_acc_in_Q_sent_oneb a haQ
                      obtain ⟨m2, hm2S, hm2_match⟩ := h_all_acc_in_Q_sent_oneb
                      cases m2 with
                      | oneb bal2 maxVBal2 maxVal2 acc2 =>
                        simp at hm2_match
                        have h_m2_is_oneb := h_S_set_of_oneb hm2S
                        simp at h_m2_is_oneb
                        have h_m2_in_sent := h_m2_is_oneb.left
                        use Message.oneb bal2 maxVBal2 maxVal2 acc2
                        simp only [h_m2_in_sent]
                        simp [h_m2_is_oneb.2, hm2_match, h_b2_less_than_b]
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
                    simp [hInv.left]
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
                    have h_lower : maxVBal2 + (1 : Nat) ≤ some b2 := by
                      cases maxVBal2 with
                      | none => simp
                      | some maxVBal2 =>
                        exact option.some_succ_le_some_of_some_le_and_lt
                          h_all_messgae_in_S_less_than_c
                          h_b2_greater_than_c
                    have h_upper : b2 < bal2 := by
                      rcases h_S_set_of_oneb hm2S with ⟨_, h_m2_match_bal_eq_b⟩
                      simp [h_case_m2] at h_m2_match_bal_eq_b
                      simp only [h_m2_match_bal_eq_b, h_b2_less_than_b]
                    exact (h_lim h_lower h_upper)
                  rw [acc_eq] at no_ex; exact no_ex
                | _ => simp [h_case_m2] at hm2_match;
              · specialize h_all_acc_in_Q_sent_oneb a haQ
                obtain ⟨m2, hm2S, hm2_match⟩ := h_all_acc_in_Q_sent_oneb
                cases m2 with
                | oneb bal2 maxVBal2 maxVal2 acc2 =>
                  simp at hm2_match
                  have h_m2_is_oneb := h_S_set_of_oneb hm2S
                  simp at h_m2_is_oneb
                  have h_m2_in_sent := h_m2_is_oneb.left
                  use Message.oneb bal2 maxVBal2 maxVal2 acc2
                  simp only [h_m2_in_sent]
                  simp [h_m2_is_oneb.2, hm2_match, h_b2_less_than_b]
                | _ => exfalso; simp at hm2_match;
      exact safeAt_is_inductive_phase2a sent sent' Quorums h2a_copy h_safe_at_prev
    -- unique proposal
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
          exact False.elim (h_no_prev_2a_msg ex)
        | _ => simp
      · have h_m2_eq_t2a : m2 = Message.twoa b v := by
          unfold Send at h2a
          simp [h2a] at h_m2_in_sent'
          simp [h_m2_in_sent] at h_m2_in_sent'; exact h_m2_in_sent'
        simp [h_m2_eq_t2a]
  · simp [h2a, h_m_eq_t2a] at hm_sent'
    cases hm' : m' with
    | onea b1 => simp
    | oneb b1 maxVBal maxVal a1 =>
      simp at hInv; simp [-Send]
      match maxVBal, maxVal with
      | none, none =>
        simp
        specialize hInv m' hm_sent'; simp [hm'] at hInv;
        intro b' a x
        exact (iff_false_left (hInv b' a x)).mp (h_votedForIn_same a1 x b')
      | some maxVBal, none | none, some maxVal =>
        simp
        specialize hInv m' hm_sent'; simp [hm'] at hInv
      | some maxVBal, some maxVal =>
        simp [-Send]; specialize hInv m' hm_sent'; simp [hm'] at hInv
        constructor
        · exact votedForIn_monotonic sent sent' h_sent_monotonic hInv.left
        · intro b' hb_lower hb_upper x
          have h_not_voted := hInv.right
          specialize h_not_voted b'
          simp [hb_lower, hb_upper] at h_not_voted
          specialize h_not_voted x
          unfold VotedForIn at *
          simpa [h2a] using h_not_voted
    | twoa b1 v1 =>   -- For 2a message in sent
      simp at hInv; simp [-Send]
      specialize hInv m' hm_sent'; simp [hm'] at hInv
      apply And.intro
      · exact safeAt_is_inductive_phase2a sent sent' Quorums h2a_copy hInv.left
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
              simp [h2a] at h_m2_in_sent'
              rcases h_m2_in_sent' with (h_eq | h1)
              · simp [h_eq]
              · exact False.elim (h_m2_in_sent h1)
            simp at h_b1_eq_b_and_v1_eq_v
            simp [*] at *
            exfalso
            exact (h_no_prev_2a_msg
                  (Message.twoa b1 v1) hm_sent' (id (Eq.symm h_same_ballot_b1_b1')))
        | _ => simp;
    | twob b1 v1 a1 =>
      match b1, v1 with
      | none, none | some b1, none | none, some v1 => simp;
      | some b1, some v1 =>
        simp
        specialize hInv m' hm_sent'
        simp [hm'] at hInv
        exact h_sent_monotonic hInv

lemma msginv_is_inductive_phase2b
    (hInv: MsgInv sent Quorums)
    (h2b: Phase2b sent sent' a) : MsgInv sent' Quorums := by
  have h2b_copy := h2b
  unfold Phase2b at h2b
  rcases h2b with ⟨m2a, h_2a_sent, hmatch⟩
  cases m2a with
  | twoa b v =>
    simp [-Send] at hmatch
    rcases hmatch with ⟨hpo, hmatch⟩
    have h_sent_monotonic : sent ⊆ sent' := by exact send_monotonic hmatch
    unfold MsgInv at *
    intro m' hm_sent'
    by_cases h_m'_in_sent : m' ∈ sent
    · cases hm': m' with
        | onea b1 => simp
        | oneb b1 maxVBal maxVal a1 =>
          simp at hInv; simp [-Send]
          match maxVBal, maxVal with
          | none, none =>
            simp; specialize hInv m' h_m'_in_sent; simp [hm'] at hInv;
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
              have hf : b1 < b1 := by
                rw [hb_eq] at hb_lower
                exact Nat.lt_of_le_of_lt (hpo ha_eq) hb_lower
              simp at hf
            · exact h_not_voted
          | some maxVBal, none | none, some maxVal =>
            simp; specialize hInv m' h_m'_in_sent; simp [hm'] at hInv
          | some maxVBal, some maxVal =>
            simp [-Send]; specialize hInv m' h_m'_in_sent; simp [hm'] at hInv
            constructor
            · exact votedForIn_monotonic sent sent' h_sent_monotonic hInv.left
            · intro b' hb_lower hb_upper x
              have h_not_voted := hInv.right
              specialize h_not_voted b'
              simp [hb_lower, hb_upper] at h_not_voted
              specialize h_not_voted x
              unfold VotedForIn at *
              simp [hmatch]; simp at h_not_voted
              constructor
              · intro hb_eq hv_eq ha_eq
                have h_inv_right := hInv.right
                specialize h_inv_right b' hb_lower hb_upper x
                specialize hpo m' h_m'_in_sent; simp [hm'] at hpo
                have h_b1_le_b : b1 ≤ b := hpo ha_eq
                rw [hb_eq] at hb_upper
                have hf : b1 < b1 := by exact Nat.lt_of_le_of_lt (hpo ha_eq) hb_upper
                simp at hf
              · exact h_not_voted
        | twoa b1 v1 =>
          simp at hInv; simp [-Send]
          specialize hInv m' h_m'_in_sent; simp [hm'] at hInv
          apply And.intro
          · exact safeAt_is_inductive_phase2b sent sent' Quorums h2b_copy hInv.left
          · have h_inv_right := hInv.right
            intro m2 h_m2_in_sent'
            specialize h_inv_right m2
            cases m2 <;>  simp [*] at *;
                          apply h_inv_right at h_m2_in_sent';
                          exact h_m2_in_sent'
        | twob b1 v1 a1 =>
          match b1, v1 with
          | none, none | some b1, none | none, some v1 => simp
          | some b1, some v1 =>
            simp
            specialize hInv m' h_m'_in_sent
            simp [hm'] at hInv
            exact h_sent_monotonic hInv
    · have m'_eq_twob : m' = Message.twob b v a := by simp [*] at *; exact hm_sent'
      simp [m'_eq_twob]
      exact h_sent_monotonic h_2a_sent
  | _ => simp [*] at *

/-- THEOREM Invariant in CL. -/
theorem Invariant {σ: ℕ → Set Message}
    (hSpec : PaxosSpec Quorums σ) : ∀ n, MsgInv (σ n) Quorums := by
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
