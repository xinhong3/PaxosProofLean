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

/- Ivy Spec (paxos_fol.ivy)

#lang ivy1.6

################################################################################
#
# Modules that should probably come from a standard library
#
################################################################################

################################################################################
#
# Module for axiomatizing a total order
#
################################################################################

module total_order(r) = {
    axiom r(X,X)                        # Reflexivity
    axiom r(X, Y) & r(Y, Z) -> r(X, Z)  # Transitivity
    axiom r(X, Y) & r(Y, X) -> X = Y    # Anti-symmetry
    axiom r(X, Y) | r(Y, X)             # Totality
}


################################################################################
#
# Types, relations and functions describing state of the network
#
################################################################################

type node
type value
type quorum
type round

individual none: round
relation le(X:round, Y:round)
instantiate total_order(le)

relation member(N:node, Q:quorum)
axiom forall Q1:quorum, Q2:quorum. exists N:node. member(N, Q1) & member(N, Q2)

relation one_a(R:round)
relation one_b_max_vote(N:node, R1:round, R2:round, V:value)
relation proposal(R:round, V:value) # 2a
relation vote(N:node, R:round, V:value) # 2b
relation decision(N:node, R:round, V:value) # got 2b from a quorum

init ~one_a(R)
init ~one_b_max_vote(N,R1,R2,V)
init ~proposal(R,V)
init ~vote(N,R,V)
init ~decision(N,R,V)

action send_1a = {
    # a proposer selects a round and sends a message asking nodes to join the round
    local r:round {
        assume r ~= none;
        one_a(r) := true
    }
}

action join_round = {
    # receive 1a and answer with 1b
    local n:node, r:round {
        assume r ~= none;
        assume one_a(r);
        assume ~(exists R:round,RMAX:round,V:value. one_b_max_vote(n,R,RMAX,V) & ~le(R,r));

        local maxr:round, v:value {
            # find the maximal vote in a round less than r
            assume ((maxr = none & forall MAXR:round,V:value. ~(~le(r,MAXR) & vote(n,MAXR,V))) |
                    (maxr ~= none & ~le(r,maxr) & vote(n,maxr,v) &
                    (forall MAXR:round,V:value. (~le(r,MAXR) & vote(n,MAXR,V)) -> le(MAXR,maxr))
                   ));
            # send the 1b message
            one_b_max_vote(n,r,maxr,v) := true
        }
    }
}

action propose = {
    # receive a quorum of 1b's and send a 2a (proposal)
    local r:round, q:quorum {
        assume r ~= none;
        assume ~proposal(r,V);
        assume forall N:node. member(N, q) -> exists R:round, V:value. one_b_max_vote(N,r,R,V);

        local maxr:round, v:value {
            # find the maximal max_vote in the quorum
            assume ((maxr = none & forall N:node,MAXR:round,V:value. ~(member(N, q) & one_b_max_vote(N,r,MAXR,V) & MAXR ~= none)) |
                    (maxr ~= none &
                    (exists N:node. member(N, q) & one_b_max_vote(N,r,maxr,v)) &
                    (forall N:node,MAXR:round,V:value. (member(N, q) & one_b_max_vote(N,r,MAXR,V) & MAXR ~= none) -> le(MAXR,maxr))
                    ));
            # propose value v
            proposal(r, v) := true
        }
    }
}

action cast_vote = {
    # receive a 2a and send 2b
    local n:node, v:value, r:round {
        assume r ~= none;
        assume ~(exists R:round,RMAX:round,V:value. one_b_max_vote(n,R,RMAX,V) & ~le(R,r));
        assume proposal(r, v);
        vote(n, r, v) := true
    }
}

action decide = {
    # get 2b from a quorum
    local n:node, r:round, v:value, q:quorum {
        assume r ~= none;
        assume member(N, q) -> vote(N, r, v);
        decision(n, r, v) := true
    }
}

export send_1a
export join_round
export propose
export cast_vote
export decide

# safety property:
conjecture (
    decision(N1,R1,V1) &
    decision(N2,R2,V2)
) -> V1 = V2

# proposals are unique per round
conjecture proposal(R,V1) & proposal(R,V2) -> V1 = V2

# only vote for proposed values
conjecture vote(N,R,V) -> proposal(R,V)

# decisions come from quorums of votes:
conjecture forall R:round, V:value. (exists N:node. decision(N,R,V)) -> exists Q:quorum. forall N:node. member(N, Q) -> vote(N,R,V)

# properties of one_b_max_vote
conjecture one_b_max_vote(N,R2,none,V1) & ~le(R2,R1) -> ~vote(N,R1,V2)
conjecture one_b_max_vote(N,R,RMAX,V) & RMAX ~= none -> ~le(R,RMAX) & vote(N,RMAX,V)
conjecture one_b_max_vote(N,R,RMAX,V) & RMAX ~= none & ~le(R,ROTHER) & ~le(ROTHER,RMAX) -> ~vote(N,ROTHER,VOTHER)

# properties of none
conjecture ~vote(N,none,V)

# Properties of choosable and proposal
conjecture forall R1:round, R2:round, V1:value, V2:value, Q:quorum. ~le(R2,R1) & proposal(R2,V2) & V1 ~= V2 ->
    exists N:node, R3:round, RMAX:round, V:value. member(N,Q) & ~le(R3,R1) & one_b_max_vote(N,R3,RMAX,V) & ~vote(N,R1,V1)

# restrict size of domain
# axiom exists V1,V2. forall V:value. V=V1 | V=V2
# axiom exists R1,R2,R3 . forall R:round. R=R1 | R=R2 | R=R3

-/
