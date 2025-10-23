-- Effort: 2h
import Paxos.Spec
import Paxos.Prop

open Paxos.Spec
open Paxos.Prop

variable (sent sent' : Set Message)
variable (Quorums : Set (Set Acceptor))


-- `SafeAt` with variable renamed to match the Ivy invariant (with `b2` be the larger ballot and `b1` the smaller one). This is exactly the same as `SafeAt` in `Paxos.Prop`, just with different variable names.
def SafeAt_variable_renamed (v2 : Value) (b2 : Ballot) : Prop :=
  ∀ b1 < b2,
    ∃ Q ∈ Quorums,
      ∀ a ∈ Q, VotedForIn sent a v2 b1 ∨ WontVoteIn sent a b1

-- Ivy invariant (choosable proposal) for `2a`, with `v2` and `b2` being free variables. In the invariant they will be supplied by the `phase2a` message.
-- conjecture forall R1:round, R2:round, V1:value, V2:value, Q:quorum. ~le(R2,R1) & proposal(R2,V2) & V1 ~= V2 ->
--     exists N:node, R3:round, RMAX:round, V:value. member(N,Q) & ~le(R3,R1) & one_b_max_vote(N,R3,RMAX,V) & ~vote(N,R1,V1)
def choosable_proposal (v2 : Value) (b2 : Ballot) : Prop :=
  ∀ b1 < b2, ∀ Q ∈ Quorums, ∃ a ∈ Q, ∀ v1 ≠ v2,
      ¬ VotedForIn sent a v1 b1 ∧
      ∃ m ∈ sent, match m with
                  | Message.oneb b' _ _ a' => a' = a ∧ b' > b1
                  | _                      => false

-- Needed this axiom to say: If a set `Q` intersects with every quorum, then `Q` is also a quorum. This is independent from the quorum assumption. For example, let `Qs = {{1, 2, 3}, {1}}`, then `Qs` satisfies the quorum assumption, but the set `{1, 2}` intersects with every quorum, but is not in `Qs`.
axiom CompleteQuorum (Q: Set Acceptor) (h: ∀ Q1 ∈ Quorums, Q ∩ Q1 ≠ ∅): Q ∈ Quorums

lemma choosable_proposal_implies_safeat (h: choosable_proposal sent Quorums v b) : SafeAt_variable_renamed sent Quorums v b := by
  intro b1 hb1                    -- b1 < b
  unfold choosable_proposal at h
  specialize h b1 hb1
  -- Give a shorter name to the inner hypothesis
  let R (a: Acceptor) : Prop :=
    ∀ v1 ≠ v,
      ¬ VotedForIn sent a v1 b1 ∧
      ∃ m ∈ sent, match m with
                  | Message.oneb b' _ _ a' => a' = a ∧ b' > b1
                  | _                      => false
  -- First, we reorder the quantifiers so that we can build a quorum `Q_safe`.
  have h_reordered : ∃ Q ∈ Quorums, ∀ a ∈ Q, R a := by
      let Q_safe := {a | R a}
      have h_Qsafe_in_quorums : Q_safe ∈ Quorums := by
        simpa [R] using CompleteQuorum Quorums Q_safe (
          by
            intro Q1 h_Q1_in_quorums
            specialize h Q1 h_Q1_in_quorums
            rcases h with ⟨a, h_a_in_Q1, res⟩
            have h_a_in_Q_safe : a ∈ Q_safe := by
              unfold Q_safe R
              exact res
            -- At this point it should be easy enough for automation, however grind fails and apply did not help much.
            have h_a_in_inter : a ∈ Q_safe ∩ Q1 := by
              constructor
              · exact h_a_in_Q_safe
              · exact h_a_in_Q1
            exact ne_of_mem_of_not_mem' h_a_in_inter fun a => a
        )
      use Q_safe, h_Qsafe_in_quorums
      intro a h_a_in_Qsafe
      exact h_a_in_Qsafe
  -- Now we have `Q_safe`, use that to prove `SafeAt`.
  rcases h_reordered with ⟨Q1, h_Q1_in_quorums, h2⟩
  use Q1, h_Q1_in_quorums
  intro a h_a_in_Q1
  specialize h2 a h_a_in_Q1
  by_cases h_voted_for_v : VotedForIn sent a v b1
  · simp [h_voted_for_v]
  · right
    unfold WontVoteIn
    constructor
    · intro v2
      specialize h2 v2
      by_cases h_v2_eq_v : v2 = v
      · simp [h_v2_eq_v, h_voted_for_v]
      · simp [h_v2_eq_v, h2]
    · have h_exists_v1_not_v : ∃ (v1 : Value), v1 ≠ v := by
        use Nat.succ v
        grind
      rcases h_exists_v1_not_v with ⟨v1, h_v1_ne_v⟩
      specialize h2 v1 h_v1_ne_v
      let h2 := h2.right
      grind
