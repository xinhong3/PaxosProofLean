import Paxos.Spec
open Paxos.Spec

open Set
open Classical

inductive Message' where
| onea  (bal : Ballot)
| oneb  (bal : Ballot) (maxVBal : Option Ballot) (maxVal : Option Value) (acc : Acceptor)
| twoa  (bal : Ballot) (val : Value)
| twob  (bal : Ballot) (val : Value) (acc : Acceptor) -- Removed Option for Ballot and Value.
deriving DecidableEq, Repr

variable (sent sent': Finset Message')      -- Changed Set to Finset, so we can prove twobs.Finite later. And in general we should use Finset instead of Set in the proofs.
instance [LinearOrder Ballot] : LinearOrder (Option Ballot) := WithBot.linearOrder

/-- Returns a pair representing the maximum ballot and value from the twob messages sent by the acceptor -/
noncomputable def max_prop' (a : Acceptor): Option (Ballot × Value) :=
  let twobs := {(b, v) | ∃m ∈ sent, m = Message'.twob b v a}
  if h: twobs ≠ ∅ then
    have h_nonempty : twobs.Nonempty := nonempty_iff_ne_empty.mpr h
    have h_finite : twobs.Finite := by sorry  -- Need to prove that twobs is finite, this should not be hard since the cardinality of twobs is bounded by the number of messages sent.
    some (Classical.choose ((Set.exists_max_image twobs (fun x => x.1) h_finite) h_nonempty))
  else none

def Phase1b' (a : Acceptor) : Prop :=
  let r := max_prop' sent a
  ∃m ∈ sent, ∃b : Ballot, m = Message'.onea b ∧
      (∀m2 ∈ sent, match m2 with
        | Message'.oneb b2 _ _ a' => (a' = a) → (b > b2)
        | Message'.twob b2 _ a' => (a' = a) → (b > b2)
        | _ => True) ∧
          match r with
            | some (rbal, rval) => sent' = sent ∪ {(Message'.oneb b rbal rval a)}
            | none => sent' = sent ∪ {(Message'.oneb b none none a)}
