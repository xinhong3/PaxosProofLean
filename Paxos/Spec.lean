import Mathlib.Tactic

namespace Paxos.Spec
open Set
open Classical

/-- Types Definition
    For simplicity, we hardwire Acceptor and Value to be String (instead of Type).
    We keep Ballot the same as TLA+ spec, which is natural numbers.
    For the empty ballot (defined as -1 in the TLAPS proof), we use none (Option Ballot).
 -/
abbrev Acceptor := String
abbrev Value := String
abbrev Ballot := Nat

/--
  Since we map the empty ballot (-1) to none, need to define `+` between Option Ballot and Nat.
-/
instance : HAdd (Option Ballot) Nat (Option Ballot) where
  hAdd
    | none,    0          => none         -- -1 + 0     = -1
    | none,    Nat.succ k => k            -- 0  + (k+1) = k
    | some a,  b          => a + b        -- a  +  b    = a + b


/- Examples of using the defined operations on Ballot and Option Ballot -/

-- #eval (none: Option Ballot) + (1: Ballot)
-- #eval (0: Ballot) ≤ (1: Ballot)
-- #eval (some 0: Option Ballot) ≤ (some 1: Option Ballot)
-- #eval (none: Option Ballot) + 1 ≤ (none: Option Ballot)

-- Minimal example, I was trying to prove this using linarith but it didn't work. This is used to prove the inductiveness of Phase 2a.
example {b b1: Ballot} (h1: b1 ≤ b) (h2: b ≤ b1 - 1) (h3: b1 > 0) : False := by
  have h2' : b < b1 := by exact (Nat.lt_iff_le_pred h3).mpr h2
  have hf : b1 < b1 := by exact Nat.lt_of_le_of_lt h1 h2'
  simp at hf

@[simp]
theorem ballot_none_plus_one_leq_ballot {b : Ballot} : (none : Option Ballot) + (1 : Ballot) ≤ some b := by
  dsimp [HAdd.hAdd]
  exact Nat.zero_le b

/- Message is defined as an inductive type -/
inductive Message where
| onea  (bal : Ballot)
| oneb  (bal : Ballot) (maxVBal : Option Ballot) (maxVal : Option Value) (acc : Acceptor) -- `maxVBal` and `maxVal` are defined to be Option, they correspond to no previous twob messages.
| twoa  (bal : Ballot) (val : Value)
| twob  (bal : Option Ballot) (val : Option Value) (acc : Acceptor)                       -- Both `bal` and `val` are Option type because `max_prop`. This is a modification from the TLA proof.
deriving DecidableEq, Repr

/-  Line 16 - 18
ASSUME QuorumAssumption ==
          /\ Quorums \subseteq SUBSET Acceptors
          /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}
-/
variable (Quorums: Set (Set Acceptor)) -- Quorums is a set of sets of acceptors
axiom QuorumAssumption (h1: Q₁ ∈ Quorums) (h2: Q₂ ∈ Quorums): Q₁ ∩ Q₂ ≠ ∅

/- Line 22 - 24
VARIABLES sent

vars == <<sent>>
-/
variable (sent sent': Set Message) -- sent' is added here to model the next state

/- Line 26
Send(m) == sent' = sent \cup {m}
-/
@[simp]
def Send (m : Message) (sent : Set Message) := sent ∪ {m}

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
  let twobs := {m ∈ sent | ∃ (b: Ballot) (v: Value), m = Message.twob b v a}          -- The twob messages should have concrete ballot and value, not Option type. We explicitly write out the types.
  if twobs ≠ ∅ then
    { m₁ ∈ twobs | ∀m₂ ∈ twobs, ∃ (b₁ b₂: Ballot) (v₁ v₂: Value),                     -- Same as above
      m₁ = Message.twob b₁ v₁ a ∧ m₂ = Message.twob b₂ v₂ a ∧ b₁ ≥ b₂}
  else {Message.twob none none a}                                                     -- For -1 ballot, we use `none`. At the same time, returning `none` as the value.

/-- Phase 1b: For an acceptor a, if there is a 1a message m with ballot m.bal that is higher than the highest it
has seen, a sends a 1b message with m.bal alongwith the highest-numbered pair it has voted for.

The If-then-else is used to simplify the definition, because we need to assert in the case of the guard not being satisfied, `sent' = sent`.

In first order logic we would write this as: `(A → B) ∧ (¬A → C)`, where `A` is the guard condition, `B` is the action to be taken if the guard is satisfied, and `C` is the action to be taken if the guard is not satisfied. In Lean, we can use `if-then-else` to express this in a more compact way, so `A` only appears once: `if A then B else C`.
-/
def Phase1b (a : Acceptor) : Prop :=
  ∃ m ∈ sent, ∃r ∈ max_prop sent a,
    match m, r with
    | Message.onea b, Message.twob rbal rval _a =>          -- rbal and rval are Option type, they could both be none.
       if (∀m2 ∈ sent, match m2 with
       | Message.oneb b2 _ _ a' => (a' = a) → (b > b2)
       | Message.twob b2 _ a' => (a' = a) → (b > b2)
       | _ => True)
       then sent' = Send (Message.oneb b rbal rval a) sent  -- rbal and rval are Option type, they could both be none.
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
    if φ : ∃ (v : Value) (Q : Set Acceptor) (S : Set Message), Q ∈ Quorums ∧ S ⊆ { m ∈ sent | match m with | Message.oneb b' _ _ _ => b' = b | _ => False}  -- S is the set of 1b messages with ballot b
      ∧ (∀ a ∈ Q, ∃ m ∈ S, match m with | Message.oneb _ _ _ a' => a' = a | _ => False)         -- for all acceptors in Q, there is a corresponding 1b message in S.
      ∧ ((∀ m ∈ S, match m with | Message.oneb _ maxVBal _ _ => maxVBal = none | _ => True)     -- for all 1b messages, either that maxVal is -1 (no acceptor has voted for anything)
          ∨ ∃ (c : Ballot), 0 ≤ c ∧ c ≤ b - (1 : Nat)                                             -- or there is a 1b message with ballot c (the 'highest ballot') that is less than b
              ∧ (∀ m ∈ S, match m with | Message.oneb _ maxVBal _ _ => maxVBal ≤ c | _ => True)   -- and for all 1b messages, the maxV is less than or equal to c
              ∧ (∃ m ∈ S, match m with | Message.oneb _ maxVBal maxVal _ => maxVBal = c ∧ maxVal = v | _ => False)) -- and there is a 1b message with ballot c and value v
    then let v := choose φ; sent' = Send (Message.twoa b v) sent                                -- because `φ` is true, we can choose such value `v`.
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

/--
The Specification of Paxos. `σ` represents the trace of the system, which is mapping between `ℕ` and `Set Message`.

The initial state is `Init (σ 0)`, and the next state is defined by `Next Quorums (σ i) (σ (i+1))` for all `i`. The disjunction allows for the stuttering step.

This is Spec == Init /\ [][Next]_vars. Naming it PaxosSpec to avoid confusion with the `Spec` namespace.
-/
def PaxosSpec (σ : ℕ → Set Message) : Prop :=
  Init (σ 0) ∧ (∀ i, Next Quorums (σ i) (σ (i+1)) ∨ (σ i) = (σ (i+1)))

end Paxos.Spec
