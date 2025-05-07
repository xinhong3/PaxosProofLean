import Mathlib.Tactic

namespace Paxos.Spec
open Set
open Classical

-- Types Definition --
abbrev Acceptor := String   -- Acceptor
abbrev Value := Nat         -- Value
abbrev Ballot := Int        -- Ballot is defined to be Int to include -1 as empty ballot

-- Special Ballot (empty) --
abbrev ballot_neg_one := -1

-- We define Message as an inductive type --
inductive Message where
| onea  (bal : Ballot) : Message
| oneb  (bal : Ballot) (maxVBal : Ballot) (maxVal : Option Value) (acc : Acceptor) : Message -- maxVBal could be 0, and maxVal could be none
| twoa  (bal : Ballot) (val : Value) : Message
| twob  (bal : Ballot) (val : Option Value) (acc : Acceptor) : Message                       -- val is of Option becuase last_voted defintion

/-  Line 16 - 18
ASSUME QuorumAssumption ==
          /\ Quorums \subseteq SUBSET Acceptors
          /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}
-/
variable (Quorums: Set (Set Acceptor)) -- Quorums is a set of sets of acceptors
axiom QuorumAssumption {Q₁: Set Acceptor} {Q₂: Set Acceptor} (h1: Q₁ ∈ Quorums) (h2: Q₂ ∈ Quorums): Q₁ ∩ Q₂ ≠ ∅

/- Line 22 - 24
VARIABLES sent

vars == <<sent>>
-/
variable (sent sent': Set Message) -- sent' is added here to model the next state

/- Line 26
Send(m) == sent' = sent \cup {m}
-/
@[simp]
def Send (m : Message) (sent₁ : Set Message) := sent₁ ∪ {m}

/- Line 30
Init == sent = {} -/
def Init : Prop := sent = ∅

/--
Phase 1a: A 1a message with ballot b is sent by some proposer (to all processes).
-/
@[simp]
def Phase1a (b : Ballot) : Prop :=
  sent' = Send (Message.onea b) sent

/-- Get the maximum ballot and value that an acceptor has voted for.

However, instead of returning a tuple for the ballot and value, we return a set of 2b messages.
Note: last_voted(a) is used in the [github repo](https://github.com/DistAlgo/proofs/blob/master/basic-paxos/PaxosHistVarNFM18.tla#L47). However, in the paper (https://arxiv.org/pdf/1802.09687), the name is max_prop. Here we use max_prop because it is more informative.
-/
def max_prop (a : Acceptor): Set Message :=
  let twobs := {m ∈ sent | ∃ b v, m = Message.twob b v a}
  if twobs ≠ ∅ then
    { m₁ ∈ twobs | ∀m₂ ∈ twobs, ∃ b₁ b₂ v₁ v₂,
      m₁ = Message.twob b₁ v₁ a ∧ m₂ = Message.twob b₂ v₂ a ∧ b₁ ≥ b₂}
  else {Message.twob (-1) none a}

/-- Phase 1b: For an acceptor a, if there is a 1a message m with ballot m.bal that is higher than the highest it
has seen, a sends a 1b message with m.bal alongwith the highest-numbered pair it has voted for.

The If-then-else is used to simplify the definition, because we need to assert in the case of the guard not being satisfied, `sent' = sent`.

In first order logic we would write this as: `(A → B) ∧ (¬A → C)`, where `A` is the guard condition, `B` is the action to be taken if the guard is satisfied, and `C` is the action to be taken if the guard is not satisfied. In Lean, we can use `if-then-else` to express this in a more compact way, so `A` only appears once: `if A then B else C`.
-/
def Phase1b (a : Acceptor) : Prop :=
  ∃ m ∈ sent, ∃r ∈ max_prop sent a,
    match m, r with
    | Message.onea b, Message.twob rbal rval _a => -- max_prop_bal might be -1 and max_prop_val could be none
       if (∀m2 ∈ sent, match m2 with
       | Message.oneb b2 _ _ a' => (a' = a) → (b > b2)
       | Message.twob b2 _ a' => (a' = a) → (b > b2)
       | _ => True)
       then sent' = Send (Message.oneb b rbal rval a) sent
       else sent' = sent
    | _, _ => False

/-- Phase 2a: If there is no 2a message in sent with ballot b, and a quorum of acceptors has sent a set S of 1b
messages with ballot b, a proposer sends a 2a message with ballot b and value v, where v is the value with
the highest ballot in S, or is any value in V if no acceptor that responded in S has voted for anything.

The choice of using if-then-else if to make the definition shorter, similar to the Phase1b definition. However, we have nested guard conditions, so multiple if-then-else are used.
-/
def Phase2a (b : Ballot) : Prop :=
  if (¬∃ m ∈ sent, match m with
                | Message.twoa b' _ => b' = b
                | _                 => False)
  then
    if φ : ∃ (v : Value) (Q : Set Acceptor) (S : Set Message), Q ∈ Quorums ∧ S ⊆ { m ∈ sent | match m with | Message.oneb b' _ _ _ => b' = b | _ => False}
      ∧ (∀ a ∈ Q, ∃ m ∈ S, match m with | Message.oneb _ _ _ a' => a' = a | _ => False)
      ∧ ((∀ m ∈ S, match m with | Message.oneb _ maxV _ _ => maxV = -1 | _ => True)
          ∨ ∃ (c : Ballot), 0 ≤ c ∧ c ≤ b - 1
              ∧ (∀ m ∈ S, match m with | Message.oneb _ maxV _ _ => maxV ≤ c | _ => True)
              ∧ (∃ m ∈ S, match m with | Message.oneb _ maxV maxVal _ => maxV = c ∧ maxVal = v | _ => False))
    then let v := choose φ; sent' = Send (Message.twoa b v) sent
    else
      sent' = sent
  else
    sent' = sent

/-- Phase 2b: For an acceptor a, if there is a 2a message m with ballot m.bal that is higher than or equal to the
highest it has seen, a sends a 2b message with m.bal and m.val.
-/
def Phase2b (a : Acceptor) : Prop :=
  ∃ m ∈ sent, match m with
    | Message.twoa b v =>
      if (∀ m₂ ∈ sent, match m₂ with
         | Message.oneb b₂ _ _ a' => a' = a → b ≥ b₂
         | Message.twob b₂ _ a' => a' = a → b ≥ b₂
         | _ => True)
      then sent' = Send (Message.twob b v a) sent
      else sent' = sent
    | _ => sent' = sent

/--
Next == \/ \E b \in Ballots : Phase1a(b) \/ Phase2a(b)
        \/ \E a \in Acceptors : Phase1b(a) \/ Phase2b(a)
** The lean code below is equivalent to the above definition, written in a more proof-friendly way for rcases to work
-/
def Next : Prop :=
   (∃b, Phase1a sent sent' b)
 ∨ (∃a, Phase1b sent sent' a)
 ∨ (∃b, Phase2a Quorums sent sent' b)
 ∨ (∃a, Phase2b sent sent' a)

end Paxos.Spec
