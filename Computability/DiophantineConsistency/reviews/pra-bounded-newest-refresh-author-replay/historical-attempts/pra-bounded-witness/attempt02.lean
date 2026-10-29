import DiophantineConsistency.PRABoundedFormula
import DiophantineConsistency.HerbrandAllInstantiation

/-! Candidate-PRA witnessing for actual Foundation bounded matrices. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRABoundedWitness
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRACharacteristicBit
  PRABoundedCharacteristic PRABoundedFormula PRAHerbrandSelection HerbrandAllInstantiation

def characteristicMatrix {n : ℕ} (c : Code n) : Semisentence language n :=
  Semiformula.rel Language.ORing.Rel.eq ![applyCode c (vars n), applyCode oneCode Fin.elim0]

theorem characteristicMatrix_open {n : ℕ} (c : Code n) : (characteristicMatrix c).Open := by
  simp [characteristicMatrix, Semiformula.Open]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

omit [M↓[language] ⊧* PRA] in
theorem modelCharacteristicMatrix {n : ℕ} (c : Code n) (φ : Semisentence language n)
    (h : M↓[language] ⊧ oneCorrectSentence c φ) (e : Fin n → M) :
    (characteristicMatrix c).Eval e Empty.elim ↔ φ.Eval e Empty.elim := by
  simp only [models_iff, oneCorrectSentence, Semiformula.eval_allClosure, LogicalConnective.iff] at h
  have hc := h e
  simpa [characteristicMatrix, Semiformula.eval_rel, eqRel, iff_def] using hc

theorem modelCharacteristicExistential {n : ℕ} (c : Code (n+1)) (φ : Semisentence language (n+1))
    (hc : M↓[language] ⊧ oneCorrectSentence c φ) (h : M↓[language] ⊧ (∀⁰* ∃⁰ φ)) :
    M↓[language] ⊧ (∀⁰* ∃⁰ characteristicMatrix c) := by
  simp only [models_iff, Semiformula.eval_allClosure, Semiformula.eval_ex] at h ⊢
  intro e
  obtain ⟨x,hx⟩ := h e
  exact ⟨x, (modelCharacteristicMatrix c φ hc (x :> e)).mpr hx⟩

theorem modelWitnessMatrix {n : ℕ} (c : Code (n+1)) (φ : Semisentence language (n+1))
    (w : Code n) (hc : M↓[language] ⊧ oneCorrectSentence c φ)
    (h : M↓[language] ⊧ (∀⁰* openMatrixAt (characteristicMatrix c) w)) :
    M↓[language] ⊧ (∀⁰* openMatrixAt φ w) := by
  simp only [models_iff, Semiformula.eval_allClosure] at h ⊢
  intro e
  have hi := h e
  rw [openMatrixAt, Semiformula.eval_substs] at hi ⊢
  exact (modelCharacteristicMatrix c φ hc _).mp hi

end models

/-- Every candidate-PRA ∀∃ theorem with a Foundation Σ₀ matrix has a fixed
primitive-recursive witness whose instance is provable in candidate PRA. -/
theorem PRA_boundedWitness {n : ℕ} (φ : Semisentence language (n+1)) (hφ : Hierarchy 𝚺 0 φ)
    (h : PRA ⊢ (∀⁰* ∃⁰ φ)) :
    ∃ w : Code n, Primrec (eval w) ∧ PRA ⊢ (∀⁰* openMatrixAt φ w) := by
  obtain ⟨c,_,_,hc⟩ := PRA_proves_boundedBooleanCharacteristic φ hφ
  have hex : PRA ⊢ (∀⁰* ∃⁰ characteristicMatrix c) := by
    apply Theory.Proof.complete_on_eq_models.{0,0}
    intro M _ _ _ _
    exact modelCharacteristicExistential c φ
      (models_of_provable (inferInstance : M↓[language] ⊧* PRA) hc)
      (models_of_provable (inferInstance : M↓[language] ⊧* PRA) h)
  obtain ⟨w,hpr,hw⟩ := PRA_witness_of_exists (characteristicMatrix c) (characteristicMatrix_open c) hex
  refine ⟨w,hpr,?_⟩
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelWitnessMatrix c φ w
    (models_of_provable (inferInstance : M↓[language] ⊧* PRA) hc)
    (models_of_provable (inferInstance : M↓[language] ⊧* PRA) hw)

end DiophantineConsistency.PRABoundedWitness
