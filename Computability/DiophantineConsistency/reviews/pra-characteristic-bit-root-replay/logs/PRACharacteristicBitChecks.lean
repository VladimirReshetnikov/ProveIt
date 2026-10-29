import DiophantineConsistency.PRACharacteristicBit

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRAFiniteFunctionCodes DiophantineConsistency.PRALanguage
  DiophantineConsistency.PRATheory DiophantineConsistency.PRAOpenFormulaCoverage
  DiophantineConsistency.PRAFormulaParameters DiophantineConsistency.PRACharacteristicBit

example (φ : Semiproposition language 1) (h : φ.Open) :
    ∃ c : Code (1 + φ.fvSup), Primrec (eval c) ∧ PRA ⊢ bitSentence c ∧
      PRA ⊢ characteristicSentence c (packParameters φ) :=
  PRA_proves_packedOpenBooleanCharacteristic φ h
#print axioms DiophantineConsistency.PRACharacteristicBit.PRA_proves_compiledBit
#print axioms DiophantineConsistency.PRACharacteristicBit.PRA_proves_openBooleanCharacteristic
#print axioms DiophantineConsistency.PRACharacteristicBit.PRA_proves_packedOpenBooleanCharacteristic
#check DiophantineConsistency.PRACharacteristicBit.PRA_proves_packedOpenBooleanCharacteristic
