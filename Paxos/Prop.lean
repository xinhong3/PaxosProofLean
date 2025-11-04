/- Agreement property and invariants for Basic Paxos
   in https://arxiv.org/pdf/1802.09687, Appendix A, by Chand and Liu, referred to as CL.
   ! indicates the differences of this spec from the spec in CL
-/
import Paxos.Spec

namespace Paxos.Prop
open Paxos.Spec

variable (sent sent' : Set Message)
variable (Quorums : Set (Set Acceptor))

def VotedForIn (a : Acceptor) (v : Value) (b : Ballot) : Prop :=
  ∃ m ∈ sent, m = Message.twob b v a

def ChosenIn (v: Value) (b: Ballot) : Prop :=
  ∃ Q ∈ Quorums, ∀ a ∈ Q, VotedForIn sent a v b

def Chosen (v : Value) : Prop :=
  ∃ b : Ballot, ChosenIn sent Quorums v b

def WontVoteIn (a : Acceptor) (b : Ballot) : Prop :=
  (∀ v : Value, ¬VotedForIn sent a v b)
  ∧ (∃ m ∈ sent, match m with
                 | Message.oneb b' _ _ a' => a' = a ∧ b' > b
                 | Message.twob b' _ a'   => a' = a ∧ b' > b
                 | _                      => false)

def SafeAt (v : Value) (b : Ballot) : Prop :=
  ∀ b2 < b, ∃ Q ∈ Quorums, ∀ a ∈ Q, VotedForIn sent a v b2 ∨ WontVoteIn sent a b2

/-- Message invariants for 1b, 2a, and 2b messages. -/
--! The added case below is because we define `maxVBal` and `maxVal` to be `Option` type.
--! We need to say if they are not both `some ... `, then they must be `none`.
def MsgInv : Prop :=
  ∀ m ∈ sent,
    match m with
    | Message.oneb b maxVBal maxVal a =>
        (match maxVBal, maxVal with
          | some rbal, some rval         => VotedForIn sent a rval rbal
          | option_rbal, option_rval     => option_rbal = none ∧ option_rval = none) --!added.
      ∧ (∀ (b' : Ballot), (b' ≥ (maxVBal + (1: Nat)) ∧ (b' < b))
          → ¬(∃ v : Value, VotedForIn sent a v b'))
    | Message.twoa b v                 =>   (SafeAt sent Quorums v b)
                                          ∧ (∀ m2 ∈ sent,
                                              match m2 with
                                              | Message.twoa b' _ => (b' = b → m2 = m)
                                              | _                 => True)
    | Message.twob (some b) (some v) _ =>   Message.twoa b v ∈ sent
    | _ => True

def Agree : Prop :=
  ∀ (v1 v2 : Value), Chosen sent Quorums v1 ∧ Chosen sent Quorums v2 → v1 = v2

end Paxos.Prop
