/-
  Basic Paxos specification, translated from the spec in TLA+
  in https://arxiv.org/pdf/1802.09687, Appendix A, by Chand and Liu, referred to as CL.
-/
import Mathlib.Tactic

namespace Paxos.Spec
open Set
open Classical

/- Types for acceptors, values. and ballots.
   For Ballot, initial dummy value uses -1 in CL; we use "none" as in Option type in Lean.-/
abbrev Ballot := Nat

/-- Define `+` between `Option Ballot` and `Nat`. This is for the 2a invariant
(`b' ≥ (maxVBal + (1: Nat)`). The empty ballot (-1) in CL is mapped to `none`. -/
instance : HAdd (Option Ballot) Nat (Option Ballot) where
  hAdd
  | none,    0          => none         -- -1 + 0     = -1
  | none,    Nat.succ k => some k       -- 0  + (k+1) = k
  | some a,  b          => some (a + b) -- a  +  b    = a + b

/- Protocol parameters. Acceptors, Values and Quorums are defined as TLA+'s CONSTANT in CL. -/
structure ProtocolParams where
  Acceptor : Type
  Value    : Type
  Acceptors : Set Acceptor
  Values : Set Value
  Quorums : Set (Set Acceptor)

variable (P : ProtocolParams)

/- Quorums and QuorumAssumption. -/
axiom QuorumAssumption :
  (P.Quorums ⊆ { Q : Set P.Acceptor | Q ⊆ P.Acceptors }) ∧
  (∀ Q₁ ∈ P.Quorums, ∀ Q₂ ∈ P.Quorums, Q₁ ∩ Q₂ ≠ ∅)

/-- Message defintion. In twob `bal` and `val` are defined to be `Option`. This is to
ensure type compatibility with `max_prop`. -/
inductive Message where
  | onea (bal : Ballot)
  | oneb (bal : Ballot) (maxVBal : Option Ballot) (maxVal : Option P.Value) (acc : P.Acceptor)
  | twoa (bal : Ballot) (val : P.Value)
  | twob (bal : Option Ballot) (val : Option P.Value) (acc : P.Acceptor)

/- History variable `sent`, and added primed variable to represent the next state. -/
variable (sent sent' : Set (Message P))

/-- `Send(m) == sent' = sent ∪ {m}` in CL. We use a functional update. -/
@[simp]
def Send (m : Message P) := sent ∪ {m}

@[simp]
def Phase1a (b : Ballot) : Prop :=
  sent' = Send P sent (Message.onea b)

/-- Get the proposal of the highest ballot that an acceptor has voted for. In CL, when
`twobs` is empty it returns a record with `bal` and `val` begin set to dummy values.
Otherwise, it returns a set of `2b` messages. Here we always return a set of `2b` messages
to ensure the type compatibility. -/
def max_prop (a : P.Acceptor) : Set (Message P) :=
  let twobs := { m ∈ sent | ∃ (b : Ballot) (v : P.Value), m = Message.twob (some b) (some v) a }
  if twobs ≠ ∅ then
    {m₁ ∈ twobs | ∀ m₂ ∈ twobs, match m₁, m₂ with
                                | Message.twob b₁ _ _, Message.twob b₂ _ _ => b₁ ≥ b₂
                                | _, _ => True}
  else {Message.twob none none a}  -- return `none` for both `maxVBal` and `maxVal`.

def Phase1b (a : P.Acceptor) : Prop :=
  ∃ m ∈ sent, ∃ r ∈ max_prop P sent a,
    match m, r with
    | Message.onea b, Message.twob rbal rval _ =>
        (∀ m₂ ∈ sent, match m₂ with
                      | Message.oneb b₂ _ _ a' => a' = a → b > b₂
                      | Message.twob b₂ _ a'   => a' = a → b > b₂
                      | _                      => True)
        ∧ sent' = Send P sent (Message.oneb b rbal rval a)
    | _, _ => False

def Phase2a (b : Ballot) : Prop :=
  (¬∃ m ∈ sent, match m with
                | Message.twoa b' _ => b' = b
                | _                 => False)
  ∧ ∃ (v : P.Value) (Q : Set P.Acceptor) (S : Set (Message P)), v ∈ P.Values ∧ Q ∈ P.Quorums ∧
      S ⊆ { m ∈ sent | match m with | Message.oneb b' _ _ _ => b' = b | _ => False}
        ∧ (∀ a ∈ Q, ∃ m ∈ S, match m with | Message.oneb _ _ _ a' => a' = a | _ => False)
        ∧ ((∀ m ∈ S, match m with
                     | Message.oneb _ maxVBal _ _ => maxVBal = none
                     | _ => True)
          ∨ ∃ (c : Ballot), 0 ≤ c ∧ c ≤ b - (1 : Nat)
              ∧ (∀ m ∈ S, match m with
                          | Message.oneb _ maxVBal _ _ => maxVBal ≤ c
                          | _ => True)
              ∧ (∃ m ∈ S, match m with
                          | Message.oneb _ maxVBal maxVal _ => maxVBal = c ∧ maxVal = v
                          | _ => False))
        ∧ sent' = Send P sent (Message.twoa b v)

def Phase2b (a : P.Acceptor) : Prop :=
  ∃ m ∈ sent, match m with
              | Message.twoa b v =>
                  (∀ m2 ∈ sent, match m2 with
                                | Message.oneb b2 _ _ a' => a' = a → b ≥ b2
                                | Message.twob b2 _ a' => a' = a → b ≥ b2
                                | _ => True)
                  ∧ sent' = Send P sent (Message.twob (some b) (some v) a)
              | _ => False

def Init : Prop := sent = ∅

def Next : Prop :=
  (∃ b, Phase1a P sent sent' b ∨ Phase2a P sent sent' b)
  ∨ (∃ a, Phase1b P sent sent' a ∨ Phase2b P sent sent' a)

/-- `Spec == Init /\ [][Next]_vars` in CL. We model the temporal formula using trace.
It is named `PaxosSpec` to avoid name clashes with the `Spec` namespace.
`σ` represents the trace of the system, which is mapping from `ℕ` to `Set Message`.
  1. The initial state is `Init (σ 0)`.
  2. The next state is defined by the relation (allowing stuttering)
  `Next Quorums (σ i) (σ (i+1)) ∨ (σ i) = (σ (i+1))`.

See the post by Igor Konnov for using trace to model temporal formulas:
https://protocols-made-fun.com/lean/2025/06/10/lean-epfd-completeness.html-/
def PaxosSpec (σ : ℕ → Set (Message P)) : Prop :=
  Init P (σ 0) ∧ (∀ i, Next P (σ i) (σ (i+1)) ∨ (σ i) = (σ (i+1)))

end Paxos.Spec
