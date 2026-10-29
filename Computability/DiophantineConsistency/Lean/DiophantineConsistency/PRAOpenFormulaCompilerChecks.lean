import DiophantineConsistency.PRAOpenFormulaCompiler

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRAFiniteFunctionCodes DiophantineConsistency.PRALanguage
  DiophantineConsistency.PRATheory DiophantineConsistency.PRAOpenFormulaCompiler

def sample : OpenFormula 2 :=
  .and (.less (.bvar 0) (.bvar 1)) (.not (.equal (.bvar 0) (.bvar 1)))

example (c : Code 2) (hb : PRA ⊢ eqBitSentence c) (hc : PRA ⊢ eqCorrectSentence c) :
    PRA ⊢ formulaCorrectSentence c sample := PRA_proves_formulaCorrect c sample hb hc
#print axioms DiophantineConsistency.PRAOpenFormulaCompiler.formulaHolds_eval
#print axioms DiophantineConsistency.PRAOpenFormulaCompiler.modelCompileFormula
#print axioms DiophantineConsistency.PRAOpenFormulaCompiler.PRA_proves_formulaCorrect
#check DiophantineConsistency.PRAOpenFormulaCompiler.PRA_proves_formulaCorrect
