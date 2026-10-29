import DiophantineConsistency.ParsonsGuardClosure
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ParsonsGuardPrefix DiophantineConsistency.ParsonsGuardClosure
example (A : ArithmeticSemiformula ℕ 3) (h : Hierarchy 𝚺 1 A) : Guard (∀⁰* A) := closure A h
#print axioms closure
#check closure
