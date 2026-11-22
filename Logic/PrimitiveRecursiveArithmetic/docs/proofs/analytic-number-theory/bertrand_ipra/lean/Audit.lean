import Bertrand

/-! Closed computation checks and dependency inspection for the public results. -/

example : Bertrand.witness 1 = 2 := by decide
example : Bertrand.witness 2 = 3 := by decide
example : Bertrand.witness 3 = 5 := by decide
example : Bertrand.witness 4 = 5 := by decide
example : Bertrand.witness 14 = 17 := by decide
example : Bertrand.witness 25 = 29 := by decide

#print axioms Bertrand.strong
#print axioms Bertrand.strict
#print axioms Bertrand.closed_right
#print axioms Bertrand.least
#print axioms Bertrand.consecutive
#print axioms Bertrand.nthPrime_exhaustive
