import DiophantineConsistency.PRABoundedTermCharacteristic

/-! Bounded existential characteristic codes via Boolean complementation. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRABoundedExistential
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAOpenFormulaCompiler PRAIsZero
  PRACharacteristicBit PRABooleanOps PRABoundedCharacteristic PRABoundedTermCharacteristic

theorem neg_termBoundedBy {n : ℕ} (φ : Semisentence language (n+1)) (t : TermN n) :
    ∼(termBoundedBy (∼φ) t) = ∃⁰[(Semiformula.rel Language.ORing.Rel.lt ![.bvar 0, Rew.bShift t])] φ := by
  simp [termBoundedBy_eq, ball, bexs, Semiformula.imp_eq]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

theorem modelNegateBit {n : ℕ} (c : Code n) : M↓[language] ⊧ bitSentence (notCode c) := by
  apply (PRACharacteristicBit.bitSentence_iff _).mpr
  intro e
  rw [modelNotCode]
  exact modelIsZeroBit _

theorem modelNegateCorrect {n : ℕ} (c : Code n) (φ : Semisentence language n)
    (h : M↓[language] ⊧ nonzeroCorrectSentence c φ) :
    M↓[language] ⊧ oneCorrectSentence (notCode c) (∼φ) := by
  apply (oneCorrectSentence_iff _ _).mpr
  intro e
  rw [modelNotCode, modelIsZeroCharacter]
  have hc := (nonzeroCorrectSentence_iff c φ).mp h e
  change (Structure.func (L := language) c e =
    Structure.func (L := language) (Code.zero 0) Fin.elim0 ↔
      Semiformula.EvalAux (inferInstance : Structure language M) Empty.elim e (∼φ))
  rw [Semiformula.EvalAux_neg]
  tauto

end models

theorem PRA_negateCharacteristic {n : ℕ} (c : Code n) (φ : Semisentence language n)
    (hbit : PRA ⊢ bitSentence c) (hcorrect : PRA ⊢ oneCorrectSentence c φ) :
    PRA ⊢ bitSentence (notCode c) ∧ PRA ⊢ oneCorrectSentence (notCode c) (∼φ) := by
  have hnz := PRA_proves_nonzeroCorrect c φ hbit hcorrect
  constructor
  · apply Theory.Proof.complete_on_eq_models.{0,0}
    intro M _ _ _ _
    exact modelNegateBit c
  · apply Theory.Proof.complete_on_eq_models.{0,0}
    intro M _ _ _ _
    exact modelNegateCorrect c φ (models_of_provable (inferInstance : M↓[language] ⊧* PRA) hnz)

theorem PRA_boundedTermExistentialStep {n : ℕ} (c : Code (n+1))
    (φ : Semisentence language (n+1)) (t : TermN n)
    (hbit : PRA ⊢ bitSentence c) (hcorrect : PRA ⊢ oneCorrectSentence c φ) :
    ∃ d : Code n, Primrec (eval d) ∧ PRA ⊢ bitSentence d ∧
      PRA ⊢ oneCorrectSentence d (∃⁰[(Semiformula.rel Language.ORing.Rel.lt ![.bvar 0, Rew.bShift t])] φ) := by
  obtain ⟨hnbit,hncorrect⟩ := PRA_negateCharacteristic c φ hbit hcorrect
  obtain ⟨d,_,hdbit,hdcorrect⟩ := PRA_boundedTermStep (notCode c) (∼φ) t hnbit hncorrect
  obtain ⟨hrbit,hrcorrect⟩ := PRA_negateCharacteristic d (termBoundedBy (∼φ) t) hdbit hdcorrect
  refine ⟨notCode d, eval_primrec _, hrbit, ?_⟩
  simpa [neg_termBoundedBy] using hrcorrect

end DiophantineConsistency.PRABoundedExistential
