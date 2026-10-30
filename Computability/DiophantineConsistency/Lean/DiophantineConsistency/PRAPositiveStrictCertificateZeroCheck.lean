import DiophantineConsistency.PRAPositiveStrictCertificate
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRAPositiveStrictCertificate
  DiophantineConsistency.PRAConditionalSigmaNormalization

example : Certificate (⊤ : ArithmeticSemiformula ℕ 1) := by
  apply positive_certificate
  exact .bounded (by simp)

example : (codeDescriptor (DiophantineConsistency.PRAFiniteFunctionCodes.Code.zero 2)).arity = 0 := rfl

example : Certificate (∃⁰ (Semiformula.rel Language.ORing.Rel.eq ![#1, &0] : ArithmeticSemiformula ℕ 2)) := by
  apply positive_certificate
  exact .exs (.bounded (by simp))
