import DiophantineConsistency.PRATermCompilation

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRAFiniteFunctionCodes DiophantineConsistency.PRALanguage
  DiophantineConsistency.PRATheory DiophantineConsistency.PRATermCompilation

def testTerm : TermN 2 :=
  applyCode Code.succ (fun _ => applyCode addCode ![.bvar 0, .bvar 1])

example : eval (compileTerm testTerm) (3 ::ᵥ 5 ::ᵥ List.Vector.nil) = 9 := by decide
example (n : ℕ) (t : TermN n) : PRA ⊢ compiledEquation t := PRA_proves_compiledEquation t
#print axioms DiophantineConsistency.PRATermCompilation.modelCompile
#print axioms DiophantineConsistency.PRATermCompilation.compiledTerm_primrec
#print axioms DiophantineConsistency.PRATermCompilation.PRA_proves_compiledEquation
#check DiophantineConsistency.PRATermCompilation.PRA_proves_compiledEquation
