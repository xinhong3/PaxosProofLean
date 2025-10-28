/-
  Lean translation of Paxos TLA Spec.
  TLA Spec is available at https://arxiv.org/pdf/1802.09687, Appendix A.
  --! denotes the difference this specificaiton and the TLA spec.
-/
import Mathlib.Tactic

namespace Paxos.Spec
open Set
open Classical

/- Types Definition. In TLA these are defined as constants.
   Ballot is defined as `Nat`, which is the same as in TLA.
   --! Acceptor and Value are hardwired to `Nat`.
-/
abbrev Acceptor := Nat      -- hardwired to Nat
abbrev Value := Nat         -- hardwired to Nat
abbrev Ballot := Nat        -- same as TLA+, empty ballot are represented by `none`.

/-- Define `+` between `Option Ballot` and `Nat`.
    This is for the 2a invariant (`b' ≥ (maxVBal + (1: Nat)`), needed because we mapped
    `-1` to `none`.
-/
instance : HAdd (Option Ballot) Nat (Option Ballot) where
  hAdd
    | none,    0          => none         -- -1 + 0     = -1
    | none,    Nat.succ k => k            -- 0  + (k+1) = k
    | some a,  b          => a + b        -- a  +  b    = a + b

/-- Message is defined as an inductive type -/
--! in oneb `maxVBal` and `maxVal` are defined to be `Option` type.
--! in twob `bal` and `val` are also defined to be `Option` type. This is to ensure type
--!   compatibility with `max_prop`.
inductive Message where
| onea  (bal : Ballot)
| oneb  (bal : Ballot) (maxVBal : Option Ballot) (maxVal : Option Value) (acc : Acceptor)
| twoa  (bal : Ballot) (val : Value)
| twob  (bal : Option Ballot) (val : Option Value) (acc : Acceptor)
deriving DecidableEq, Repr

/- Quorums and QuorumAssumption. Same as in TLA. -/

variable (Quorums: Set (Set Acceptor)) -- Quorums is a set of sets of acceptors
axiom QuorumAssumption (h1: Q₁ ∈ Quorums) (h2: Q₂ ∈ Quorums): Q₁ ∩ Q₂ ≠ ∅

--  History variable `sent`.
--! An extra variable `sent'` is added to represent the 'primed' variable in TLA.
variable (sent sent': Set Message)

/-- Definition of `Send`. Same as in TLA. -/
@[simp]
def Send (m : Message) (sent : Set Message) : Set Message := sent ∪ {m}

/-- Phase 1a. Same as in TLA. -/
@[simp]
def Phase1a (b : Ballot) : Prop :=
  sent' = Send (Message.onea b) sent

/-- Get the maximum ballot and value that an acceptor has voted for.
--! In TLA, when `twobs` is empty it returns a record with `bal` and `val` begin set to
--!  False. Otherwise, it returns a set of `2b` messages. Here we always return a set
--!  of `2b` messages to ensure the type compatibility.
-/
def max_prop (a : Acceptor): Set Message :=
  let twobs := {m ∈ sent | ∃ (b: Ballot) (v: Value), m = Message.twob b v a}
  if twobs ≠ ∅ then
      {m₁ ∈ twobs | ∀m₂ ∈ twobs, ∃ (b₁ b₂: Ballot) (v₁ v₂: Value),
                      m₁ = Message.twob b₁ v₁ a ∧ m₂ = Message.twob b₂ v₂ a ∧ b₁ ≥ b₂}
  else {Message.twob none none a}  -- return `none` for both `maxVBal` and `maxVal`.

/-- Phase1b. Same as in TLA except using pattern matching and conditional (`if-else`).
--! Need the conditional to say when the guard is not satisfied: `sent' = sent`.
-/
def Phase1b (a : Acceptor) : Prop :=
  ∃ m ∈ sent, ∃r ∈ max_prop sent a,
    match m, r with
    | Message.onea b, Message.twob rbal rval _a =>
       if (∀m2 ∈ sent, match m2 with
       | Message.oneb b2 _ _ a' => (a' = a) → (b > b2)
       | Message.twob b2 _ a' => (a' = a) → (b > b2)
       | _ => True)
       then sent' = Send (Message.oneb b rbal rval a) sent
       else sent' = sent
    | _, _ => False

/-- Phase 2a. Same as in TLA except using pattern matching and conditional (`if-else`).
--- We also have nested `if-else` in Phase2a because in the second one we need
     `Classical.choose` to pick `v` from the existential statement.
-/
def Phase2a (b : Ballot) : Prop :=
  if (¬∃ m ∈ sent, match m with
                | Message.twoa b' _ => b' = b
                | _                 => False)
  then if φ :
      ∃ (v : Value) (Q : Set Acceptor) (S : Set Message), Q ∈ Quorums ∧
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
        then let v := Classical.choose φ; sent' = Send (Message.twoa b v) sent
    else sent' = sent
  else sent' = sent

/-- Phase 2b. Same as in TLA. -/
def Phase2b (a : Acceptor) : Prop := ∃ m ∈ sent,
  match m with
  | Message.twoa b v =>
      if (∀ m2 ∈ sent, match m2 with
         | Message.oneb b2 _ _ a' => a' = a → b ≥ b2
         | Message.twob b2 _ a' => a' = a → b ≥ b2
         | _ => True)
      then sent' = Send (Message.twob b v a) sent
      else sent' = sent
  | _ => sent' = sent

/-- Init. Same as in TLA. -/
def Init : Prop := sent = ∅

/-- Next. Same as in TLA. -/
def Next : Prop :=    (∃b, Phase1a sent sent' b ∨ Phase2a Quorums sent sent' b)
                    ∨ (∃a, Phase1b sent sent' a ∨ Phase2b sent sent' a)

/--
    This is `Spec == Init /\ [][Next]_vars` in TLA+.
    --! We model the temporal logic formula using trace.
    --! named `PaxosSpec` to avoid name clashes with the `Spec` namespace.
    `σ` represents the trace of the system, which is mapping from `ℕ` to `Set Message`.
      1. The initial state is `Init (σ 0)`
      2. The next state is defined by the relation (allowing stuttering)
         `Next Quorums (σ i) (σ (i+1)) ∨ (σ i) = (σ (i+1))`.
-/
def PaxosSpec (σ : ℕ → Set Message) : Prop :=
  Init (σ 0) ∧ (∀ i, Next Quorums (σ i) (σ (i+1)) ∨ (σ i) = (σ (i+1)))

end Paxos.Spec
