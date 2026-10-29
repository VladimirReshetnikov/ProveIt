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
  simp [termBoundedBy_eq, ball, bexs]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

theorem modelNegateBit {n : ℕ} (c : Code n) : M↓[language] ⊧ bitSentence (notCode c) := by
  simp only [models_iff, bitSentence, Semiformula.eval_allClosure]
  intro e
  have h : IsBit (Structure.func (L := language) (notCode c) e) := by
    rw [modelNotCode]
    exact modelIsZeroBit _
  change Semiformula.EvalAux (inferInstance : Structure language M) Empty.elim e _
  simp [Semiformula.EvalAux, eqRel, applyCode, vars, Function.comp_def]
  have hz : (fun i : Fin 0 => Semiterm.val e Empty.elim (Fin.elim0 i : TermN n)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  rw [hz]
  exact h

theorem modelNegateCorrect {n : ℕ} (c : Code n) (φ : Semisentence language n)
    (h : M↓[language] ⊧ nonzeroCorrectSentence c φ) :
    M↓[language] ⊧ oneCorrectSentence (notCode c) (∼φ) := by
  simp only [models_iff, nonzeroCorrectSentence, Semiformula.eval_allClosure, LogicalConnective.iff] at h
  simp only [models_iff, oneCorrectSentence, Semiformula.eval_allClosure, LogicalConnective.iff]
  intro e
  have hc := h e
  have hv : (Semiterm.val (L := language) e Empty.elim ∘ vars n) = e := by funext i; rfl
  have hz : (Semiterm.val (L := language) e Empty.elim ∘ Fin.elim0) = (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  simp [Semiformula.eval_nrel, eqRel, applyCode, Semiterm.val_func, hv, hz] at hc
  simp [Semiformula.eval_rel, eqRel, applyCode, Semiterm.val_func, hv, hz, modelNotCode,
    modelIsZeroCharacter] at hc ⊢
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
