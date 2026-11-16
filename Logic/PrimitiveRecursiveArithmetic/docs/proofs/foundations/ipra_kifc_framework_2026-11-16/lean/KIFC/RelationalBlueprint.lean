import KIFC.SearchBlueprint

/-!
# Finite relational viability blueprint

The intended object representation is a rectangular Boolean table.  Reverse
row computation is a `LoopCertificate`; path extraction uses generated least
search certificates.
-/

namespace LeanProofs.KIFC

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm

/-- Object-facing contract of a generated finite relation tower. -/
structure RelationTowerCertificate (n : ℕ) where
  pre : Fm PTm n
  horizon : PTm n
  width : PTm n
  viabilityTable : PTm n
  anyStartViable : Fm PTm n
  selectedPath : PTm n
  pathValid : Fm PTm n
  recurrenceSound : [pre] ⊢[PRAAx] anyStartViable ⟶ pathValid
  terminalSound : [pre, pathValid] ⊢[PRAAx] pathValid

/-- Exact stable observer over a bounded relation, stated at the level needed
by graph composition. -/
structure ExactObserverCertificate (n : ℕ) where
  pre : Fm PTm n
  selectedValid : Fm PTm n
  output : PTm n
  observerIndependent : Fm PTm n
  selected : [pre] ⊢[PRAAx] selectedValid
  stable : [pre, selectedValid] ⊢[PRAAx] observerIndependent

/-!
Completion path:

1. define rectangular table lookup/write symbols and their equations;
2. define the reverse recurrence `W_H`, `W_i` with generated `anyB` folds;
3. prove the row invariant by `LoopCertificate.compile`;
4. define a bounded tuple path checker and prove viability iff suffix checker;
5. generate least viable start/successor searches;
6. derive path-checker acceptance and cut it into the consumer proof;
7. add exact and rational-diameter observer elimination.
-/

end LeanProofs.KIFC
