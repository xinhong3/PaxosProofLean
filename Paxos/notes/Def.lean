import Mathlib.Tactic
import Smt

open Set
open Classical

namespace Paxos.Def.TypeDef
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

end Paxos.Def.TypeDef
