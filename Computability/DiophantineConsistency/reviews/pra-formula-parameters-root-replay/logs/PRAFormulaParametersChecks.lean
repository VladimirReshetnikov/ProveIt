import DiophantineConsistency.PRAFormulaParameters

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRAFiniteFunctionCodes DiophantineConsistency.PRALanguage
  DiophantineConsistency.PRATheory DiophantineConsistency.PRAOpenFormulaCoverage
  DiophantineConsistency.PRAFormulaParameters

def parameterFormula : Semiproposition language 1 :=
  Semiformula.rel Language.ORing.Rel.eq ![.bvar 0, .fvar 3]

example : parameterFormula.Open := by simp [parameterFormula, Semiformula.Open]
example : parameterFormula.fvSup = 4 := by decide
example (φ : Semiproposition language 1) (h : φ.Open) :
    ∃ c : Code (1 + φ.fvSup), Primrec (eval c) ∧
      PRA ⊢ characteristicSentence c (packParameters φ) :=
  PRA_proves_packedOpenCharacteristic φ h
#print axioms DiophantineConsistency.PRAFormulaParameters.packParameters_eval
#print axioms DiophantineConsistency.PRAFormulaParameters.PRA_proves_packedOpenCharacteristic
#check DiophantineConsistency.PRAFormulaParameters.packParameters_eval
