import DiophantineConsistency.PRABoundedFormula
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRAFiniteFunctionCodes DiophantineConsistency.PRALanguage
  DiophantineConsistency.PRATheory DiophantineConsistency.PRACharacteristicBit
  DiophantineConsistency.PRABoundedCharacteristic DiophantineConsistency.PRABoundedFormula

def sample : Semisentence language 1 :=
  ∃⁰[(Semiformula.rel Language.ORing.Rel.lt ![.bvar 0, .bvar 1])]
    (Semiformula.rel Language.ORing.Rel.eq ![.bvar 0, .bvar 0])
example : Hierarchy 𝚺 0 sample := by simp [sample, LO.FirstOrder.bexs]
example : ∃ c : Code 1, Primrec (eval c) ∧ PRA ⊢ bitSentence c ∧ PRA ⊢ oneCorrectSentence c sample :=
  PRA_proves_boundedBooleanCharacteristic sample (by simp [sample, LO.FirstOrder.bexs])
#print axioms represent
#print axioms hasCharacteristic
#print axioms PRA_proves_boundedBooleanCharacteristic
#check PRA_proves_boundedBooleanCharacteristic
