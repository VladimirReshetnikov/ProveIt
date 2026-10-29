import DiophantineConsistency.PRAEqualityCode

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRAFiniteFunctionCodes DiophantineConsistency.PRALanguage
  DiophantineConsistency.PRATheory DiophantineConsistency.PRAOpenFormulaCompiler
  DiophantineConsistency.PRAOpenFormulaCoverage DiophantineConsistency.PRAEqualityCode

def sampleFormula : Semisentence language 2 :=
  (Semiformula.rel Language.ORing.Rel.lt ![.bvar 0, .bvar 1]) ⋏
    (Semiformula.nrel Language.ORing.Rel.eq ![.bvar 0, .bvar 1])

example : eval equalityCode (3 ::ᵥ 3 ::ᵥ List.Vector.nil) = 1 := by decide
example : eval equalityCode (3 ::ᵥ 5 ::ᵥ List.Vector.nil) = 0 := by decide
example : eval equalityCode (5 ::ᵥ 3 ::ᵥ List.Vector.nil) = 0 := by decide
example (n : ℕ) (φ : Semisentence language n) (h : φ.Open) :
    ∃ c : Code n, Primrec (eval c) ∧ PRA ⊢ characteristicSentence c φ :=
  DiophantineConsistency.PRAEqualityCode.PRA_proves_openCharacteristic φ h
example : ∃ c : Code 2, Primrec (eval c) ∧ PRA ⊢ characteristicSentence c sampleFormula :=
  DiophantineConsistency.PRAEqualityCode.PRA_proves_openCharacteristic sampleFormula (by simp [sampleFormula, Semiformula.Open])
#print axioms DiophantineConsistency.PRAEqualityCode.PRA_proves_equalityBit
#print axioms DiophantineConsistency.PRAEqualityCode.PRA_proves_equalityCorrect
#print axioms DiophantineConsistency.PRAEqualityCode.PRA_proves_openCharacteristic
#check DiophantineConsistency.PRAEqualityCode.PRA_proves_openCharacteristic
