import DiophantineConsistency.PRAOpenFormulaCoverage

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRAFiniteFunctionCodes DiophantineConsistency.PRALanguage
  DiophantineConsistency.PRATheory DiophantineConsistency.PRAOpenFormulaCompiler
  DiophantineConsistency.PRAOpenFormulaCoverage

def sampleFormula : Semisentence language 2 :=
  (Semiformula.rel Language.ORing.Rel.lt ![.bvar 0, .bvar 1]) ⋏
    (Semiformula.nrel Language.ORing.Rel.eq ![.bvar 0, .bvar 1])

example : sampleFormula.Open := by simp [sampleFormula, Semiformula.Open]
example (eqCode : Code 2) (hb : PRA ⊢ eqBitSentence eqCode)
    (hc : PRA ⊢ eqCorrectSentence eqCode) :
    ∃ c : Code 2, Primrec (eval c) ∧ PRA ⊢ characteristicSentence c sampleFormula :=
  PRA_proves_openCharacteristic eqCode hb hc sampleFormula (by simp [sampleFormula, Semiformula.Open])
#print axioms DiophantineConsistency.PRAOpenFormulaCoverage.parseFormula_open
#print axioms DiophantineConsistency.PRAOpenFormulaCoverage.PRA_proves_openCharacteristic
#check DiophantineConsistency.PRAOpenFormulaCoverage.PRA_proves_openCharacteristic
