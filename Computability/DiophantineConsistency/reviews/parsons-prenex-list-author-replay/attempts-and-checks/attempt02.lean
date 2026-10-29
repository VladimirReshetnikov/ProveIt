import DiophantineConsistency.ParsonsPrenexList

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ParsonsRule DiophantineConsistency.ParsonsPrenexList

example : asFormula (aggregate []) = (⊥ : Proposition ℒₒᵣ) := rfl
example (ps : List Packed) :
    asFormula (aggregate ps) = DiophantineConsistency.ParsonsStructure.disjoin (ps.map asFormula) :=
  aggregate_source ps
#print axioms aggregate_source
#print axioms aggregate_bounded
#print axioms matrix_bounded
#print axioms forward
#print axioms backward
#check forward
#check backward
