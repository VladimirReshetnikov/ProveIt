import PCFM.Boolean
import PCFM.Trace
import PCFM.Observer

/-!
# Backward viability: implementation blueprint

The mathematical construction is fully specified in the paper.  The remaining
Lean choice is the bounded table representation.  This file records exact
interfaces without adding axioms or placeholders.
-/

namespace LeanProofs.IPRA.Framework

/-
Recommended records:

structure FiniteRelation (n : Nat) where
  leftBound rightBound : PTm n
  rel : Fm PTm (n + 2)
  relQF : rel.QF

structure ViabilityProblem (n : Nat) where
  horizon : PTm n
  candidateBound : PTm (n + 1)  -- time-indexed
  good : Fm PTm (n + 2)         -- time, candidate
  step : Fm PTm (n + 3)         -- time, candidate, successor
  terminal : Fm PTm (n + 1)
  qf payloads ...

def viabilityTable : PR ...
def selectPath : PR ...

theorem viabilityTable_spec : ...
theorem selectPath_spec : ...
theorem noPath_of_not_viable : ...
-/

end LeanProofs.IPRA.Framework
