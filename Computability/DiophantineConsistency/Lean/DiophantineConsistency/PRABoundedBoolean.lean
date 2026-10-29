import DiophantineConsistency.PRABoundedExistential

/-! Boolean steps for candidate-PRA characteristic codes. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace DiophantineConsistency.PRABoundedBoolean
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAOpenFormulaCompiler
  PRACharacteristicBit PRABooleanOps PRABoundedCharacteristic PRABoundedExistential

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

theorem modelAndBit {n : ℕ} (c d : Code n) (hc : M↓[language] ⊧ bitSentence c)
    (hd : M↓[language] ⊧ bitSentence d) : M↓[language] ⊧ bitSentence (andCode c d) := by
  apply (PRACharacteristicBit.bitSentence_iff _).mpr
  intro e
  rw [modelAndCode]
  exact (modelMulBit _ _ ((PRACharacteristicBit.bitSentence_iff c).mp hc e)
    ((PRACharacteristicBit.bitSentence_iff d).mp hd e)).1

theorem modelAndCorrect {n : ℕ} (c d : Code n) (φ ψ : Semisentence language n)
    (hcbit : M↓[language] ⊧ bitSentence c) (hdbit : M↓[language] ⊧ bitSentence d)
    (hc : M↓[language] ⊧ oneCorrectSentence c φ) (hd : M↓[language] ⊧ oneCorrectSentence d ψ) :
    M↓[language] ⊧ oneCorrectSentence (andCode c d) (φ ⋏ ψ) := by
  simp only [models_iff, oneCorrectSentence, Semiformula.eval_allClosure, LogicalConnective.iff] at hc hd ⊢
  intro e
  have hb1 := (PRACharacteristicBit.bitSentence_iff c).mp hcbit e
  have hb2 := (PRACharacteristicBit.bitSentence_iff d).mp hdbit e
  have h1 := hc e
  have h2 := hd e
  have hv : (Semiterm.val (L := language) e Empty.elim ∘ vars n) = e := by funext i; rfl
  have hz : (Semiterm.val (L := language) e Empty.elim ∘ Fin.elim0) = (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  simp [Semiformula.eval_rel, eqRel, applyCode, Semiterm.val_func, hv, hz] at h1 h2 ⊢
  rw [modelAndCode]
  have hm := (modelMulBit _ _ hb1 hb2).2
  tauto

end models

theorem PRA_andCharacteristic {n : ℕ} (c d : Code n) (φ ψ : Semisentence language n)
    (hcbit : PRA ⊢ bitSentence c) (hdbit : PRA ⊢ bitSentence d)
    (hc : PRA ⊢ oneCorrectSentence c φ) (hd : PRA ⊢ oneCorrectSentence d ψ) :
    PRA ⊢ bitSentence (andCode c d) ∧ PRA ⊢ oneCorrectSentence (andCode c d) (φ ⋏ ψ) := by
  constructor
  · apply Theory.Proof.complete_on_eq_models.{0,0}
    intro M _ _ _ _
    exact modelAndBit c d (models_of_provable (inferInstance : M↓[language] ⊧* PRA) hcbit)
      (models_of_provable (inferInstance : M↓[language] ⊧* PRA) hdbit)
  · apply Theory.Proof.complete_on_eq_models.{0,0}
    intro M _ _ _ _
    exact modelAndCorrect c d φ ψ (models_of_provable (inferInstance : M↓[language] ⊧* PRA) hcbit)
      (models_of_provable (inferInstance : M↓[language] ⊧* PRA) hdbit)
      (models_of_provable (inferInstance : M↓[language] ⊧* PRA) hc)
      (models_of_provable (inferInstance : M↓[language] ⊧* PRA) hd)

theorem PRA_orCharacteristic {n : ℕ} (c d : Code n) (φ ψ : Semisentence language n)
    (hcbit : PRA ⊢ bitSentence c) (hdbit : PRA ⊢ bitSentence d)
    (hc : PRA ⊢ oneCorrectSentence c φ) (hd : PRA ⊢ oneCorrectSentence d ψ) :
    ∃ k : Code n, PRA ⊢ bitSentence k ∧ PRA ⊢ oneCorrectSentence k (φ ⋎ ψ) := by
  obtain ⟨hcb,hcc⟩ := PRA_negateCharacteristic c φ hcbit hc
  obtain ⟨hdb,hdc⟩ := PRA_negateCharacteristic d ψ hdbit hd
  obtain ⟨hab,hac⟩ := PRA_andCharacteristic (notCode c) (notCode d) (∼φ) (∼ψ) hcb hdb hcc hdc
  obtain ⟨hb,hc'⟩ := PRA_negateCharacteristic (andCode (notCode c) (notCode d)) (∼φ ⋏ ∼ψ) hab hac
  refine ⟨notCode (andCode (notCode c) (notCode d)), hb, ?_⟩
  simpa using hc'

end DiophantineConsistency.PRABoundedBoolean
