import DiophantineConsistency.PRABoundedSearchCode

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRAFiniteFunctionCodes DiophantineConsistency.PRAIsZero
  DiophantineConsistency.PRABoundedSearchCode

example : eval (searchCode isZeroCode) (0 ::ᵥ List.Vector.nil) = 0 := by decide
example : eval (searchCode isZeroCode) (1 ::ᵥ List.Vector.nil) = 1 := by decide
example : eval (searchCode isZeroCode) (4 ::ᵥ List.Vector.nil) = 1 := by decide
#print axioms DiophantineConsistency.PRABoundedSearchCode.searchCode_primrec
#print axioms DiophantineConsistency.PRABoundedSearchCode.modelSearchZero
#print axioms DiophantineConsistency.PRABoundedSearchCode.modelSearchStep
#print axioms DiophantineConsistency.PRABoundedSearchCode.modelSearchStepEquation
#check DiophantineConsistency.PRABoundedSearchCode.modelSearchStepEquation
