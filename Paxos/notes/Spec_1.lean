import Mathlib.Tactic
import Smt
import Smt.auto
import Mathlib.Data.Set.Basic

section Paxos
open Set
open Classical

-- Types Definition --
abbrev Acceptor := String   -- Acceptor
abbrev Value := Nat         -- Value
abbrev Ballot := Int        -- Ballot is defined to be Int to include -1 as empty ballot

-- Empty Ballot and Value used in Phase1b --
abbrev EMPTY_BALLOT := -1
abbrev EMPTY_VALUE : Value := 0

-- We define Message as an inductive type --
inductive Message where
| onea  (bal : Ballot) : Message
| oneb  (bal : Ballot) (maxVBal : Ballot) (maxVal : Option Value) (acc : Acceptor) : Message -- maxVBal could be 0, and maxVal could be none
| twoa  (bal : Ballot) (val : Value) : Message
| twob  (bal : Ballot) (val : Option Value) (acc : Acceptor) : Message                       -- val is of Option becuase last_voted defintion

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
  sent' = Send (Message.onea b) sent

def last_voted (sent: Set Message) (a : Acceptor): Set Message :=
  let twobs := {m ∈ sent | ∃ b v, m = Message.twob b v a}
  if twobs ≠ ∅ then
    { m ∈ twobs | ∀m₂ ∈ twobs, ∃ b₁ b₂ v₁ v₂,
      m = Message.twob b₁ v₁ a
    ∧ m₂ = Message.twob b₂ v₂ a
    ∧ b₁ ≥ b₂}
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
      if (∀m2 ∈ sent, match m2 with
       | Message.oneb b2 _ _ a' => (a' = a) → (b > b2)
       | Message.twob b2 _ a' => (a' = a) → (b > b2)
       | _ => True) then sent' = Send (Message.oneb b rbal v a) sent
       else sent' = sent
    | _, _ => sent' = sent

def Phase2a (b : Ballot) (sent sent' : Set Message) : Prop :=
  (¬∃ m ∈ sent, match m with
    | Message.twoa b' _ => b' = b
    | _ => false)
  ∧ (∃v: Value, ∃Q ∈ Quorums, ∃S, S ⊆ {m ∈ sent | match m with
                                                  | Message.oneb b' _ _ _ => b' = b
                                                  | _ => false}
      ∧ (∀ a ∈ Q, ∃ m ∈ S, match m with| Message.oneb _ _ _ a' => a' = a | _ => false)
      ∧ (∀ m ∈ S, match m with| Message.oneb _ maxVBal _ _ => maxVBal = -1 | _ => True)
            ∨ (∃c: Ballot, (c ≥ 0 ∧ c ≤ b - 1)
               ∧  (∀ m ∈ S, match m with | Message.oneb _ maxVBal _ _ => maxVBal ≤ c | _ => True)
               ∧  (∃ m ∈ S, match m with | Message.oneb _ maxVBal maxVal _ => maxVBal = c ∧ maxVal = v | _ => False))
      ↔ sent' = Send (Message.twoa b v) sent)
def Phase2a' (b : Ballot) (sent sent' : Set Message) : Prop :=
  if (¬∃ m ∈ sent, match m with
                | Message.twoa b' _ => b' = b
                | _                 => False)
  then
    if φ : ∃ (v : Value) (Q : Set Acceptor) (S : Set Message),
      Q ∈ Quorums
      ∧ S ⊆ { m ∈ sent | match m with | Message.oneb b' _ _ _ => b' = b | _ => False }
      ∧ (∀ a ∈ Q, ∃ m ∈ S, match m with | Message.oneb _ _ _ a' => a' = a | _ => False)
      ∧ ((∀ m ∈ S, match m with | Message.oneb _ maxV _ _ => maxV = -1 | _ => True)
          ∨ ∃ (c : Ballot), 0 ≤ c ∧ c ≤ b - 1
              ∧ (∀ m ∈ S, match m with | Message.oneb _ maxV _ _ => maxV ≤ c | _ => True)
              ∧ (∃ m ∈ S, match m with | Message.oneb _ maxV maxVal _ => maxV = c ∧ maxVal = v | _ => False)) then
      let v := choose φ
      sent' = Send (Message.twoa b v) sent
      else
        sent' = sent
    else
      sent' = sent

def Phase2b (a : Acceptor) (sent sent' : Set Message) : Prop :=
  ∃ m ∈ sent, match m with
    | Message.twoa b v =>
      if (∀ m₂ ∈ sent,
         match m₂ with
         | Message.oneb b₂ _ _ a' => a' = a → b ≥ b₂
         | Message.twob b₂ _ a' => a' = a → b ≥ b₂
         | _ => True)
      then sent' = Send (Message.twob b v a) sent
      else sent' = sent
    | _ => sent' = sent

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
example {sent sent' : Set Message} {a : Acceptor} {b : Ballot} (h1 : Phase1a b sent sent') (hnv : ∀ v : Value, ¬VotedForIn sent a v b) : ∀ v, ¬VotedForIn sent' a v b := by
  intro v hVoted
  unfold Phase1a VotedForIn at *
  specialize hnv v
  simp [*] at *
  exact hnv hVoted

-- Phase1b, no change for VotedForIn
example (h1 : Phase1b a sent sent') (hnv : ∀ v : Value, ¬VotedForIn sent a v b) : ∀ v, ¬VotedForIn sent' a v b := by
  intro v hVoted
  unfold Phase1b VotedForIn at *
  specialize hnv v
  simp [*] at *
  rcases h1 with ⟨m, hm_sent, r, hr_last, hcase⟩
  -- two‐way split on (m,r)
  cases m with
    | onea b₁ =>
      cases r with
        | twob rbal1 v1 a1 =>
          have l1: a1 = a := by apply mem_last_voted_is_twob at hr_last; simp at hr_last; exact hr_last
          simp [l1] at hcase
          by_cases hq1 : ∀ m2 ∈ sent,
              match m2 with
              | Message.oneb b2 maxVBal maxVal a' => a' = a → b2 < b₁
              | Message.twob b2 val a'           => a' = a → b2 < b₁
              | _                                => True
          · rw [if_pos hq1] at hcase; simp [hcase] at hVoted; exact hnv hVoted
          · simp [hq1] at hcase; simp [hcase] at *; exact hnv hVoted
        | _ => simp [hr_last] at hcase; simp [hcase] at *; exact hnv hVoted;
    | _ => simp [hr_last] at hcase; simp [hcase] at *; exact hnv hVoted

-- Phase2a, no change for VotedForIn
example (h1: Phase2a' Quorums b sent sent') (hnv: ∀ v : Value, ¬VotedForIn sent a v b) : ∀ v, ¬VotedForIn sent' a v b := by
  intro v hVoted
  unfold Phase2a' VotedForIn at *
  specialize hnv v
  simp [*] at *
  by_cases h_not_sent_2a : ∀ x ∈ sent,
      ¬match x with
        | Message.twoa b' val => b' = b
        | x => False
  · simp [if_pos h_not_sent_2a] at h1
    -- Get the condition of the if statement for h1
    by_cases h_guard : ∃ v, ∃ Q ∈ Quorums, ∃ x ⊆ {m | m ∈ sent ∧ match m with | Message.oneb b' maxVBal maxVal acc => b' = b | x => False}, (∀ a ∈ Q,
              ∃ m ∈ x,
                match m with
                | Message.oneb bal maxVBal maxVal a' => a' = a
                | x => False) ∧ ((∀ m ∈ x, match m with | Message.oneb bal maxV maxVal acc => maxV = -1 | x => True) ∨
              ∃ c, 0 ≤ c ∧ c ≤ b - 1 ∧
                    (∀ m ∈ x,
                        match m with
                        | Message.oneb bal maxV maxVal acc => maxV ≤ c
                        | x => True) ∧
                      ∃ m ∈ x,
                        match m with
                        | Message.oneb bal maxV maxVal acc => maxV = c ∧ maxVal = some v
                        | x => False)
    · simp [*] at h1
      simp [h1] at hVoted
      exact hnv hVoted
    · simp [*] at *
      simp [h1] at hVoted
      exact hnv hVoted
  · simp [if_neg h_not_sent_2a] at h1
    simp [h1] at *
    exact hnv hVoted

-- Phase2b
example (h1: Phase2b a sent sent') (hnv: ∀ v: Value, ¬VotedForIn sent a v b) : ∀ v, ¬VotedForIn sent' a v b := by
  intro v hVoted
  unfold Phase2b VotedForIn at *
  specialize hnv v
  -- simp [*] at hVoted
  rcases h1 with ⟨m, hm_sent, hmatch⟩
  -- two‐way split on (m,r)
  cases m with
    | twoa b1 v1 =>
      by_cases hq1 : ∀ m₂ ∈ sent,
        match m₂ with
        | Message.oneb b₂ maxVBal maxVal a' => a' = a → b₂ ≤ b1
        | Message.twob b₂ val a' => a' = a → b₂ ≤ b1
        | x => True
      · simp [hm_sent] at hmatch
        rw [if_pos hq1] at hmatch
        simp [hmatch] at hVoted
        rcases hVoted with (h_eq_bv | h_voted_in_prev)
        · -- how to convert some v to v or vice versa?
          rcases h_eq_bv with ⟨rfl, rfl⟩
          simp [Option.get_some] at hnv
          have hm_sent' : Message.twob b (some v) a ∈ sent := by sorry
          exact hnv hm_sent'
        · exact hnv h_voted_in_prev
      · simp [hm_sent] at hmatch
        rw [if_neg hq1] at hmatch
        simp [hmatch] at *
        exact hnv hVoted
    | _ => simp [hmatch] at *; exact hnv hVoted


def SafeAt (v : Value) (b : Ballot) : Prop :=
  ∀ b2 : Ballot, b2 < b →
    ∃ Q ∈ Quorums, ∀ a ∈ Q, VotedForIn sent a v b2 ∨ WontVoteIn sent a b2

def ChosenIn (v: Value) (b: Ballot) : Prop :=
  ∃ Q ∈ Quorums, ∀ a ∈ Q, VotedForIn sent a v b

def Chosen (v : Value) : Prop :=
  ∃ b : Ballot, ChosenIn Quorums sent v b

def Consistency : Prop :=
  ∀ (v1 v2 : Value), Chosen Quorums sent v1 ∧ Chosen Quorums sent v2 → v1 = v2

-- Message Invariant in HisVar
-- MsgInv ==
--  \A m \in sent :
--    /\ m.type = "1b" => /\ VotedForIn(m.acc, m.maxVal, m.maxVBal) \/ m.maxVBal = -1
--                        /\ \A b \in m.maxVBal+1..m.bal-1: ~\E v \in Value: VotedForIn(m.acc, v, b)
--    /\ m.type = "2a" => /\ SafeAt(m.val, m.bal)
--                        /\ \A m2 \in sent : (m2.type = "2a" /\ m2.bal = m.bal) => m2 = m
--    /\ m.type = "2b" => \E m2 \in sent : /\ m2.type = "2a"
--                                         /\ m2.bal  = m.bal
--                                         /\ m2.val  = m.val
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

lemma VotedOnce (hInv: MsgInv Quorums sent) (a1 a2: Acceptor) (b : Ballot) (v1 v2: Value) (h_voted_1: VotedForIn sent a1 v1 b) (h_voted_2 : VotedForIn sent a2 v2 b) : v1 = v2 := by
  unfold VotedForIn MsgInv at *
  have h_m_2a_1 : Message.twoa b v1 ∈ sent := by
    simp at h_voted_1; apply hInv at h_voted_1; simp at h_voted_1; exact h_voted_1
  apply hInv at h_m_2a_1; simp at h_m_2a_1
  have h_m_2a_2 : Message.twoa b v2 ∈ sent := by
    simp at h_voted_2; apply hInv at h_voted_2; simp at h_voted_2; exact h_voted_2
  apply h_m_2a_1.right at h_m_2a_2; simp at h_m_2a_2
  exact h_m_2a_2.symm
theorem SafeAtStable (sent sent' : Set Message) (hInv : MsgInv Quorums sent) (hNext : Next Quorums sent sent')
  (v : Value) (b : Ballot) (hSafe : SafeAt Quorums sent v b) : SafeAt Quorums sent' v b := by
  have h_sent_sub : sent ⊆ sent' := by exact next_imp_mono_sent Quorums sent sent' hNext
  unfold Next at hNext
  rcases hNext with ⟨b, h1a⟩ | ⟨a, h1b⟩ | ⟨b, h2a⟩ | ⟨a, h2b⟩
  · -- Proving SaftAt' for phase1a
    unfold SafeAt at *
    intro x hxb
    specialize hSafe x hxb
    rcases hSafe with ⟨Q, hQ, hProp⟩
    have hV : ∀ a ∈ Q, VotedForIn sent a v x → VotedForIn sent' a v x := by
      intro a ha
      exact fun a_1 ↦ monotonic_votedForIn h_sent_sub a_1
    have hW : ∀ a ∈ Q, WontVoteIn sent a x → WontVoteIn sent' a x := by sorry
    use Q
    constructor
    · exact hQ
    · intro a ha
      cases hProp a ha with
      | inl hVoted => left; exact hV a ha hVoted
      | inr hWont => right; exact hW a ha hWont
  · -- Proving SafeAt' for Phase1b
    unfold SafeAt at *
    intro x hxb
    specialize hSafe x hxb
    rcases hSafe with ⟨Q, hQ, hProp⟩
    have hV : ∀ a ∈ Q, VotedForIn sent a v x → VotedForIn sent' a v x := by
      exact fun a a_1 a_2 ↦ monotonic_votedForIn h_sent_sub a_2   -- suggested by apply?
    have hW : ∀ a ∈ Q, WontVoteIn sent a x → WontVoteIn sent' a x := by
      intro A hA hWont
      unfold WontVoteIn at *
      sorry
    use Q
    refine (and_iff_left ?h.hb).mpr hQ
    intro A hA
    specialize hProp A hA         -- get rid of ∀ in hProp
    specialize hV A hA
    cases hProp with
    | inl hVotedInPrev => exact Or.inl (hV hVotedInPrev);
    | inr hWontVoteInPrev => exact Or.inr (hW A hA hWontVoteInPrev)
  · sorry   -- Proving SafeAt' for Phase2a
  · sorry   -- Proving SafeAt' for Phase2b

example {b: Ballot} {v: Value} {a: Acceptor} (h1: Message.twoa b v ∈ sent) (h2: MsgInv Quorums sent) : SafeAt Quorums sent v b := by
  unfold MsgInv at *
  apply h2 at h1
  simp at h1
  exact h1.left

example {b: Ballot} {v: Value} {a: Acceptor} (h1: Message.twob b v a ∈ sent) (h2: MsgInv Quorums sent) : SafeAt Quorums sent v b := by
  have M := Message.twob b v a
  have h_e_two_a : (Message.twoa b v) ∈ sent := by
    unfold MsgInv at *
    specialize h2 (Message.twob b v a)
    apply h2 at h1; simp at h1; exact h1
  unfold MsgInv at *; specialize h2 (Message.twoa b v)
  simp at h2
  exact (h2 h_e_two_a).left



theorem Consistent (hInv : MsgInv Quorums sent) : Consistency Quorums sent := by
  unfold Consistency
  intros v1 v2 hChosen
  rcases hChosen with ⟨hCh1, hCh2⟩
  rcases hCh1 with ⟨b1, hChosenIn1⟩
  rcases hCh2 with ⟨b2, hChosenIn2⟩
  -- We prove the following symmetrical result for it to be used later in the proof
  have Consistent_ChosenIn_Diff_Bal (b1: Ballot) (v1: Value) (b2: Ballot) (v2: Value) (hChosenIn1: ChosenIn Quorums sent v1 b1) (hChosenIn2: ChosenIn Quorums sent v2 b2) (h_ls: b1 < b2) : v1 = v2 := by
      have h_safe_b2 : SafeAt Quorums sent v2 b2 := by
        -- By VotedInv, QuorumAssumption DEF ChosenIn, Inv
        unfold ChosenIn at hChosenIn2
        rcases hChosenIn2 with ⟨Q2, hQ2, hVotedQ2⟩
        have ⟨aa, haa⟩ := pick_from_quorum_int Quorums hQ2 hQ2
        refine VotedInv Quorums sent hInv ?a v2 b2 ?_
        · exact aa
        · specialize hVotedQ2 aa; exact (hVotedQ2 haa.left)
      unfold SafeAt at h_safe_b2
      specialize h_safe_b2 b1
      have hsb1 := h_safe_b2 h_ls
      rcases hsb1 with ⟨Q1, hQ1, hqsb1⟩
      unfold ChosenIn at hChosenIn1
      rcases hChosenIn1 with ⟨Q2, hQ2, hvotedin1⟩
      have ⟨aa, haa⟩ := pick_from_quorum_int Quorums hQ1 hQ2
      have haa_voted_v1_b1 : VotedForIn sent aa v1 b1 := by exact hvotedin1 aa haa.right
      have haa_safe_b1 : VotedForIn sent aa v2 b1 ∨ WontVoteIn sent aa b1 := by exact hqsb1 aa haa.left
      cases haa_safe_b1 with
      | inl haa_voted_v2_b1 => exact VotedOnce Quorums sent hInv aa aa b1 v1 v2 haa_voted_v1_b1 haa_voted_v2_b1
      | inr haa_wont_vote_b1 =>
        unfold WontVoteIn at haa_wont_vote_b1
        rcases haa_wont_vote_b1 with ⟨haa_not_vote_b1, _⟩
        exact (haa_not_vote_b1 v1 haa_voted_v1_b1).elim

  by_cases h_eq : b1 = b2
  · unfold ChosenIn at *
    rcases hChosenIn1 with ⟨Q1, hQ1, hProp1⟩
    rcases hChosenIn2 with ⟨Q2, hQ2, hProp2⟩
    have ⟨aa, haa⟩ := pick_from_quorum_int Quorums hQ1 hQ2
    specialize hProp1 aa
    specialize hProp2 aa
    have hv1 := hProp1 (And.left haa); have hv2 := hProp2 (And.right haa)
    rw [←h_eq] at hv2
    exact VotedOnce Quorums sent hInv aa aa b1 v1 v2 hv1 hv2
  by_cases h_lt: b1 < b2
  · exact Consistent_ChosenIn_Diff_Bal b1 v1 b2 v2 hChosenIn1 hChosenIn2 h_lt
  · have h_nlt: b2 < b1 := by
      have h_total := lt_trichotomy b1 b2
      rcases h_total with (h_total_left | h_total_mid | h_total_r)
      · exact (h_lt h_total_left).elim
      · exact (h_eq h_total_mid).elim
      · exact h_total_r
    exact id (Consistent_ChosenIn_Diff_Bal b2 v2 b1 v1 hChosenIn2 hChosenIn1 h_nlt).symm
end Paxos
