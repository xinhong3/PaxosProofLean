import Paxos.Spec
import Paxos.Prop

namespace Paxos.Example
open Paxos.Spec

set_option diagnostics true

noncomputable def SentSimple1 : Set Message :=
  {Message.onea 1}

def SentSimple1Fin : Finset Message := {Message.onea 1}

variable (S : Set Message)

-- this single instance now works for *any* such S,
-- as long as desugaring S turns into a finite disjunction of `· = …`
@[instance]
noncomputable def decidable_mem_of_finite_literal (m : Message) : Decidable (m ∈ S) := by
  exact Classical.propDecidable (m ∈ S)
  -- unfold S so that `(m ∈ S)` becomes `… = m` ∨ `… = m` ∨ ⋯
  -- now each equality is decidable by DecidableEq, and finite Ors are decidable

#eval Message.onea 1 ∈ SentSimple1Fin

-- #eval Message.onea 1 ∈ SentSimple1
-- failed to compile definition, compiler IR check failed at '_eval._closed_0'. Error: depends on declaration 'Paxos.Example.decidable_mem_of_finite_literal', which has no executable code; consider marking definition as 'noncomputable
