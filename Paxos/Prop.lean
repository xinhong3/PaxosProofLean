import Paxos.Spec

namespace Paxos.Prop
open Paxos.Spec

variable (sent sent' : Set Message)
variable (Quorums : Set (Set Acceptor))

/-- VotedForIn(a, v, b) means that acceptor a has sent some 2b message m with m.val
equal to v and m.bal equal to b. This specifies that acceptor a has voted the pair ⟨v, b⟩.-/
def VotedForIn (a : Acceptor) (v : Value) (b : Ballot) : Prop :=
  ∃ m ∈ sent, m = Message.twob b v a

/-- ChosenIn(v, b) means that every acceptor in some quorum Q has voted the pair hv, bi. -/
def ChosenIn (v: Value) (b: Ballot) : Prop :=
  ∃ Q ∈ Quorums, ∀ a ∈ Q, VotedForIn sent a v b

/-- Chosen(v) means that for some ballot b, ChosenIn(v, b) holds. -/
def Chosen (v : Value) : Prop :=
  ∃ b : Ballot, ChosenIn sent Quorums v b

/-- WontVoteIn(a, b) means that acceptor a has seen a higher ballot than b,
and did not and will not vote any value with ballot b. -/
def WontVoteIn (a : Acceptor) (b : Ballot) : Prop :=
     (∀ v : Value, ¬VotedForIn sent a v b)
   ∧ (∃ m ∈ sent, match m with
                  | Message.oneb b' _ _ a' => a' = a ∧ b' > b
                  | Message.twob b' _ a'   => a' = a ∧ b' > b
                  | _                      => false)

/-- SafeAt(v, b) means that no value except perhaps v has been or will be chosen
in any ballot lower than b. -/
def SafeAt (v : Value) (b : Ballot) : Prop :=
  ∀ b2 < b,
    ∃ Q ∈ Quorums,
      ∀ a ∈ Q, VotedForIn sent a v b2 ∨ WontVoteIn sent a b2

/-- Message invariants for 1b, 2a, and 2b messages. -/
def MsgInv : Prop :=
  ∀ m ∈ sent, match m with
    | Message.oneb b maxVBal maxVal a  =>
        (match maxVBal, maxVal with
          | some rbal, some rval         => VotedForIn sent a rval rbal
          | option_rbal, option_rval     => option_rbal = none ∧ option_rval = none)
      ∧ (∀ (b' : Ballot), (b' ≥ (maxVBal + (1: Nat)) ∧ (b' < b))
          → ¬(∃ v : Value, VotedForIn sent a v b'))
    | Message.twoa b v                 =>   (SafeAt sent Quorums v b)
                                          ∧ (∀ m2 ∈ sent, match m2 with
                                             | Message.twoa b' _ => (b' = b → m2 = m)
                                             | _                 => True)
    | Message.twob (some b) (some v) _ =>   Message.twoa b v ∈ sent
    | _ => True

def Consistency : Prop :=
  ∀ (v1 v2 : Value), Chosen sent Quorums v1 ∧ Chosen sent Quorums v2 → v1 = v2

end Paxos.Prop
