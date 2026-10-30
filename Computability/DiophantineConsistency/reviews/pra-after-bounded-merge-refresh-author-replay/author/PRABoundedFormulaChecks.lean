import DiophantineConsistency.PRABoundedFormula
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRAFiniteFunctionCodes DiophantineConsistency.PRALanguage
  DiophantineConsistency.PRATheory DiophantineConsistency.PRACharacteristicBit
  DiophantineConsistency.PRABoundedCharacteristic DiophantineConsistency.PRABoundedFormula

def sample : Semisentence language 1 :=
  ∃⁰[(Semiformula.rel Language.ORing.Rel.lt ![.bvar 0, .bvar 1])]
    (Semiformula.rel Language.ORing.Rel.eq ![.bvar 0, .bvar 0])
theorem sample_bounded : Hierarchy 𝚺 0 sample := by
  change Hierarchy 𝚺 0 (∃⁰[“x. x < !!((.bvar 1) : TermN 2)”]
    (Semiformula.rel Language.ORing.Rel.eq ![.bvar 0, .bvar 0]))
  exact Hierarchy.bexs (by simp) (by simp)
example : ∃ c : Code 1, Primrec (eval c) ∧ PRA ⊢ bitSentence c ∧ PRA ⊢ oneCorrectSentence c sample :=
  PRA_proves_boundedBooleanCharacteristic sample sample_bounded
#print axioms represent
#print axioms hasCharacteristic
#print axioms PRA_proves_boundedBooleanCharacteristic
#check PRA_proves_boundedBooleanCharacteristic
