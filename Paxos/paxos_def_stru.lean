import Mathlib.Tactic
import Smt
import Mathlib.Data.Set.Basic

set_option diagnostics true
namespace DefTypes

-- Types Definition --
abbrev Acceptor := String   -- Acceptor
abbrev Value := Nat         -- Value
abbrev Ballot := Int        -- Ballot is defined to be Int to include -1 as empty ballot

-- Special Ballot (empty) --
abbrev ballot_neg_one := -1

end DefTypes

namespace MsgDefStructure
open DefTypes

structure Message where
  type: String

structure onea extends Message where
  bal : Ballot

structure oneb extends Message where
  bal     : Ballot
  maxVBal : Ballot
  maxVal  : Option Value
  acc     : Acceptor

structure twoa extends Message where
  bal : Ballot
  val : Value

structure twob extends Message where
  bal : Ballot
  val : Option Value
  acc : Acceptor

instance : Coe onea Message where
  coe x := x.toMessage

end MsgDefStructure

namespace Spec
open DefTypes MsgDefStructure Set Classical

variable (Quorums : Set (Set Acceptor)) (sent sent': Set Message)

axiom QuorumAssumption {Q₁: Set Acceptor} {Q₂: Set Acceptor} (h1: Q₁ ∈ Quorums) (h2: Q₂ ∈ Quorums): Q₁ ∩ Q₂ ≠ ∅

-- The following lemma simply says that we can pick a acceptor from the intersection
@[simp]
lemma pick_from_quorum_int {Q₁: Set Acceptor} {Q₂: Set Acceptor} (h1: Q₁ ∈ Quorums) (h2: Q₂ ∈ Quorums): ∃a: Acceptor, a ∈ Q₁ ∩ Q₂ := by
  have hne := QuorumAssumption Quorums h1 h2
  rcases ((Iff.mpr nonempty_iff_ne_empty) hne) with ⟨aa, haa⟩ -- This took me
  exact Exists.intro aa haa

@[simp]
def Send (m : Message) (sent : Set Message) := sent ∪ {m}

@[simp]
lemma send_monotonic {sent sent': Set Message} {x: Message} (h: sent' = Send x sent) : sent ⊆ sent' := by
  unfold Send at h; intro X hX; rw [h]; exact mem_union_left {x} hX

@[simp]
def Phase1a (b : Ballot) (sent sent': Set Message) : Prop :=
  sent' = Send (onea.mk { type := "1a" } b : Message) sent
def twobsFor (sent : Set Message) (a : Acceptor) : Set Message :=
  sent.filter fun m =>
    match m with
    | Message.twob tb => tb.acc = a
    | _               => false

def last_voted (sent: Set Message) (a : Acceptor): Set Message :=
  let twobs := {m ∈ sent | ∃ b v, m = Message.twob b v a}
  if twobs ≠ ∅ then
    { m ∈ twobs | ∀m₂ ∈ twobs,
    match m, m₂ with
       | Message.twob b _ _, Message.twob b₂ _ _ => b >= b₂
       | _, _                                    => false }
  else {Message.twob (-1) none a}

@[simp]
theorem mem_last_voted_is_twob {m : Message} {a : Acceptor}:
  m ∈ last_voted sent a → ∃ (b : Ballot) (v : Option Value), m = Message.twob b v a := by
  dsimp [last_voted] at *
  let twobs := { m | m ∈ sent ∧ ∃ b v, m = Message.twob b v a }
  split_ifs with h_nonempty
  · simp only [Set.mem_sep, Set.mem_setOf, exists_prop, and_assoc] at *
    intro hm; simp at hm
    simp [hm]
  · intro h_mem
    simp only [Set.mem_setOf, exists_prop, and_assoc] at h_mem
    rcases h_mem with ⟨_h_sent, ⟨b, v, rfl⟩, _⟩
    exact ⟨b, v, rfl⟩

def Phase1b (a : Acceptor) (sent sent': Set Message) : Prop :=
  ∃ m ∈ sent, ∃r ∈ last_voted sent a,
    match m, r with
    | Message.onea b, Message.twob rbal v _ => -- Notice that rbal might be -1 and v could be none
       (∀m2 ∈ sent, match m2 with
       | Message.oneb b2 _ _ a' => (a' = a) → (b > b2)
       | Message.twob b2 _ a' => (a' = a) → (b > b2)
       | _ => True)
       → sent' = Send (Message.oneb b rbal v a) sent
    | _, _ => False


def Phase2a (b : Ballot) (sent sent' : Set Message) : Prop :=
  (¬ ∃ m ∈ sent, match m with | Message.twoa b' _ => b' = b | _ => false)
  ∧ (∃v: Value, ∃Q ∈ Quorums, ∃S, S ⊆ { m ∈ sent | match m with | Message.oneb b' _ _ _ => b' = b | _ => false}
      ∧ (∀ a ∈ Q, ∃ m ∈ S, match m with| Message.oneb _ _ _ a' => a' = a | _ => false)
      ∧ (∀ m ∈ S, match m with| Message.oneb _ maxVBal _ _ => maxVBal = -1 | _ => True)
            ∨ (∃c: Ballot, (c ≥ 0 ∧ c ≤ b - 1)
               ∧  (∀ m ∈ S, match m with | Message.oneb _ maxVBal _ _ => maxVBal ≤ c | _ => True)
               ∧  (∃ m ∈ S, match m with | Message.oneb _ maxVBal maxVal _ => maxVBal = c ∧ maxVal = v | _ => False))
      ↔ sent' = Send (Message.twoa b v) sent)

def Phase2b (a : Acceptor) (sent sent' : Set Message) : Prop :=
  ∃ m ∈ sent, match m with
    | Message.twoa b v =>
      (∀ m₂ ∈ sent,
         match m₂ with
         | Message.oneb b₂ _ _ a' => a' = a → b ≥ b₂
         | Message.twob b₂ _ a' => a' = a → b ≥ b₂
         | _ => True)
      → sent' = Send (Message.twob b v a) sent
    | _ => False

def Init (sent: Set Message): Prop := sent = ∅
def Next : Prop :=
   (∃b, Phase1a b sent sent')
 ∨ (∃a, Phase1b a sent sent')
 ∨ (∃b, Phase2a Quorums b sent sent')
 ∨ (∃a, Phase2b a sent sent')

lemma next_imp_mono_sent (hNext: Next Quorums sent sent') : sent ⊆ sent' := by
  unfold Next at hNext
  rcases hNext with (hPhase1a | hPhase1b | hPhase2a | hPhase2b)
  · rcases hPhase1a with ⟨b', hM, ha⟩; exact send_monotonic rfl
  · rcases hPhase1b with ⟨a', M, ⟨hM_sent, ⟨R, hR, hMR_match⟩⟩⟩
    by_cases h_m_onea : ∃b, M = Message.onea b
    · simp [h_m_onea] at hMR_match;
    · sorry
  · sorry
  · sorry

def VotedForIn (a : Acceptor) (v : Value) (b : Ballot) : Prop :=
  ∃ m ∈ sent, m = Message.twob b v a

-- An simple lemma states that VotedForIn is monotonic -- once it's true, adding new messages can't make it false
lemma monotonic_votedForIn {a : Acceptor} {v : Value} {b : Ballot} {sent sent': Set Message} (h1: sent ⊆ sent'): VotedForIn sent a v b → VotedForIn sent' a v b := by
  intro h1
  rcases h1 with ⟨m, hm, Hmatch⟩
  use m
  refine (and_iff_right ?h.ha).mpr Hmatch
  apply h1; exact hm


def WontVoteIn (sent : Set Message) (a : Acceptor) (b : Ballot) : Prop :=
  (∀ v, ¬ VotedForIn sent a v b) ∧
  (
    (∃ b' maxVBal maxVal, Message.oneb b' maxVBal maxVal a ∈ sent ∧ b' > b) ∨
    (∃ b' val,Message.twob b' val a ∈ sent ∧ b' > b)
  )

def WontVoteIn' (sent : Set Message) (a : Acceptor) (b : Ballot) : Prop :=
  (∀ v : Value, ¬VotedForIn sent a v b) ∧               -- has not voted
  (∃ m ∈ sent,                                            -- and will not ever be voted in
    match m with
    | Message.oneb b' _ _ a' => a' = a ∧ b' > b           -- either a 1b message with ballot greater than b
    | Message.twob b' _ a'   => a' = a ∧ b' > b           -- or a 2b message with ballot greater than b
    | _                      => false)

lemma WontVoteIn_iff_WontVoteIn' (sent : Set Message) (a : Acceptor) (b : Ballot) :
  WontVoteIn' sent a b ↔ WontVoteIn sent a b := by
  unfold WontVoteIn WontVoteIn'
  constructor
  · intro h
    -- `h : (∀ v, ¬VotedForIn sent a v b) ∧ (∃ m ∈ sent, match m with ...)`
    -- So we can split the top-level ∧
    have h_not := h.left
    have h_ex  := h.right
    -- Build the ∧ for WontVoteIn'
    apply And.intro
    · exact h_not
    · -- Now prove the disjunction of the two existentials
      rcases h_ex with ⟨m, hm_sent, hmatch⟩
      -- Case-analyze the message shape
      cases m with
      | oneb b' maxVBal maxVal a' =>
        -- From `hmatch : a' = a ∧ b' > b`
        obtain ⟨rfl_a, rfl_b⟩ := hmatch
        rw [rfl_a] at hm_sent
        -- Left side: exist 1b
        exact Or.inl ⟨b', maxVBal, maxVal, hm_sent, rfl_b⟩
      | twob b' val a' =>
        -- From `hmatch : a' = a ∧ b' > b`
        obtain ⟨rfl_a, rfl_b⟩ := hmatch
        rw [rfl_a] at hm_sent
        -- Right side: exist 2b
        exact Or.inr ⟨b', val, hm_sent, rfl_b⟩
      | _ => -- other constructors give `False` in the match
        simp at hmatch
  · intro h'
    -- `h' : (∀ v, ¬VotedForIn sent a v b) ∧ ((∃ b' ... ) ∨ (∃ b' ...))`
    have h_not' := h'.left
    have h_or   := h'.right
    -- Build the ∧ for WontVoteIn
    apply And.intro
    · exact h_not'
    · -- Prove `∃ m ∈ sent, match m ...`
      cases h_or with
      | inl h_1=>
        rcases h_1 with ⟨b', maxVBal, maxVal, h1, hb⟩
        -- Use a 1b message
        use Message.oneb b' maxVBal maxVal a, h1
      | inr h_2 =>
        rcases h_2 with ⟨b', val, h1, hb⟩
        -- Use a 2b message
        use Message.twob b' val a, h1

lemma monotonic_WontVoteIn {a : Acceptor} {b : Ballot} {sent sent' : Set Message}
  (h_phase1a : Phase1a b sent sent') -- typically, sent' = sent ∪ { new_message }
  (h_wv : WontVoteIn' sent a b)
  : WontVoteIn' sent' a b := by
  have h_subset : sent ⊆ sent' := by unfold Phase1a Send at *; exact send_monotonic h_phase1a
  unfold WontVoteIn Phase1a Send at *
  rcases h_wv with ⟨h_not_voted, ⟨m, hm_sent, h_match⟩⟩
  ·
    have h_left : ∀ (v : Value), ¬VotedForIn sent' a v b := by
      have h_wv_left := h_not_voted -- modify this
      intro v
      specialize h_wv_left v
      unfold VotedForIn at *
      by_contra h_c
      have h_nc : ∃ m ∈ sent, m = Message.twob b v a := by
        rw [h_phase1a] at h_c
        sorry
      exact h_wv_left h_nc

-- Phase1a, no change for VotedForIn
example {sent sent' : Set Message} {a : Acceptor} {b : Ballot}
(h1 : Phase1a b sent sent') (hnv : ∀ v : Value, ¬VotedForIn sent a v b) : ∀ v, ¬VotedForIn sent' a v b := by
  intro v hVoted
  unfold Phase1a VotedForIn at *
  specialize hnv v
  simp [*] at *
  exact hnv hVoted

-- Phase1b, no change for VotedForIn
example {sent sent' : Set Message} {a : Acceptor} {b : Ballot}
(h1 : Phase1b a sent sent') (hnv : ∀ v : Value, ¬VotedForIn sent a v b) : ∀ v, ¬VotedForIn sent' a v b := by
  intro v hVoted
  unfold Phase1b VotedForIn at *
  specialize hnv v
  simp [*] at *
  /-∃ m ∈ sent,
  ∃ r ∈ last_voted sent a,
    match m, r with
    | Message.onea b, Message.twob rbal v acc =>
      (∀ m2 ∈ sent,
          match m2 with
          | Message.oneb b2 maxVBal maxVal a' => a' = a → b2 < b
          | Message.twob b2 val a' => a' = a → b2 < b
          | x => True) →
        sent' = insert (Message.oneb b rbal v a) sent
    | x, x_1 => False-/
  rcases h1 with ⟨m, hmsent, r, hrsent, hmatch⟩
example {sent sent' : Set Message} {a : Acceptor} (b : Ballot)
  (h1 : Phase1b a sent sent') (hnv : ∀ v : Value, ¬ VotedForIn sent a v b) :
  ∀ v, ¬ VotedForIn sent' a v b := by
  intro v hVoted
  unfold Phase1b VotedForIn at *
  specialize hnv v
  simp [*] at *
  -- pull apart the Phase1b witness
  rcases h1 with ⟨m, hmsent, r, hrsent, hmatch⟩

  cases m with
  | onea b1 =>
    cases r with
    | twob rbal rval acc =>
      simp at hmatch

      /- state at this point, how to make a cace on the premise of hmatch

      Quorums : Set (Set Acceptor)
sent✝ sent'✝ sent sent' : Set Message
a : Acceptor
b : Ballot
v : Value
hVoted : Message.twob b (some v) a ∈ sent'
hnv : Message.twob b (some v) a ∉ sent
bal✝ : Ballot
hmsent : Message.onea bal✝ ∈ sent
rbal : Ballot
rval : Option Value
acc : Acceptor
hrsent : Message.twob rbal rval acc ∈ last_voted sent a
hmatch : (∀ m2 ∈ sent,
    match m2 with
    | Message.oneb b2 maxVBal maxVal a' => a' = a → b2 < bal✝
    | Message.twob b2 val a' => a' = a → b2 < bal✝
    | x => True) →
  sent' = insert (Message.oneb bal✝ rbal rval a) sent
⊢ False


      -/
    | _ => simp at hrsent
  | _ => sorry

def SafeAt (v : Value) (b : Ballot) : Prop :=
  ∀ b2 : Ballot, b2 < b →
    ∃ Q ∈ Quorums, ∀ a ∈ Q, VotedForIn sent a v b2 ∨ WontVoteIn sent a b2

def ChosenIn (v: Value) (b: Ballot) : Prop :=
  ∃ Q ∈ Quorums, ∀ a ∈ Q, VotedForIn sent a v b

def Chosen (v : Value) : Prop :=
  ∃ b : Ballot, ChosenIn Quorums sent v b

def Consistency : Prop :=
  ∀ (v1 v2 : Value), Chosen Quorums sent v1 ∧ Chosen Quorums sent v2 → v1 = v2

def MsgInv (sent : Set Message) : Prop :=
  ∀ m ∈ sent,
    match m with
    | Message.oneb b maxVBal maxVal a =>
      match maxVal with
          | none => True
          | some v₀ => VotedForIn sent a v₀ maxVBal
      ∧
      (∀ (b' : Ballot),
         ((b' ≥ maxVBal + 1) ∧ (b' ≤ b - 1)) →
         ¬ (∃ v : Value, VotedForIn sent a v b'))
    | Message.twoa b v =>
      (SafeAt Quorums sent v b)
      ∧ (∀ m2 ∈ sent,
            match m2 with
            | Message.twoa b' _ => (b' = b → m2 = m)
            | _                  => True)
    | Message.twob b (some v) _ => Message.twoa b v ∈ sent
    | _ => True

lemma VotedInv (h1: MsgInv Quorums sent) : ∀ a, ∀ v, ∀ b, VotedForIn sent a v b → SafeAt Quorums sent v b := by
  unfold MsgInv VotedForIn at *
  intros a v b h; simp at h
  apply h1 at h; simp at h
  apply h1 at h; simp at h
  exact h.left
