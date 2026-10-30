import DiophantineConsistency.ParsonsPositiveRule
import DiophantineConsistency.PRAPeanoMinusTranslation
/-! Proof translation conditional on admissibility of the positive induction
rule; no positive-induction schema is assumed of PRA models. -/
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsPositiveComparison
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory PRAPeanoMinusTranslation ParsonsRule ParsonsBasePositive

/-- The missing induction-rule adapter is stated as a transformer of actual
candidate-PRA proofs, not as an induction axiom holding in every model. -/
def PositiveAdmissible : Prop := ∀ (φ : ArithmeticSemiformula ℕ 1), Positive φ →
    (PRA ⊢ (Semiformula.lMap embedding (base φ)).univCl) →
    (PRA ⊢ (Semiformula.lMap embedding (step φ)).univCl) →
    PRA ⊢ (Semiformula.lMap embedding (∀⁰ φ)).univCl

private theorem mapped_of_valid (φ : Proposition ℒₒᵣ)
    (h : ∀ (M : Type) [Nonempty M] [Structure language M] [Structure.Eq language M]
      [M↓[language] ⊧* PRA], ∀ f : ℕ → M,
      @Semiformula.Evalf ℕ ℒₒᵣ M ((inferInstance : Structure language M).lMap embedding) f φ) :
    PRA ⊢ (Semiformula.lMap embedding φ).univCl := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  simp only [models_iff, Semiformula.eval_univCl]
  intro f
  exact Semiformula.eval_lMap.mpr (h M f)

private theorem valid_of_mapped {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
    [M↓[language] ⊧* PRA] {φ : Proposition ℒₒᵣ}
    (h : PRA ⊢ (Semiformula.lMap embedding φ).univCl) (f : ℕ → M) :
    @Semiformula.Evalf ℕ ℒₒᵣ M ((inferInstance : Structure language M).lMap embedding) f φ := by
  have hm := models_of_provable (inferInstance : M↓[language] ⊧* PRA) h
  simp only [models_iff, Semiformula.eval_univCl] at hm
  exact Semiformula.eval_lMap.mp (hm f)

theorem comparison (hadmit : PositiveAdmissible) {φ : Proposition ℒₒᵣ}
    (p : ParsonsPositiveRule.Proof 𝗣𝗔⁻ φ) : PRA ⊢ (Semiformula.lMap embedding φ).univCl := by
  induction p with
  | logical d =>
      apply mapped_of_valid
      intro M _ _ _ _ f
      letI : Structure ℒₒᵣ M := (inferInstance : Structure language M).lMap embedding
      simpa using Derivation.sound f d
  | «axiom» h =>
      apply mapped_of_valid
      intro M _ _ _ _ f
      letI : Structure ℒₒᵣ M := (inferInstance : Structure language M).lMap embedding
      have hp := PRA_proves_peanoMinusAxiom h
      have hm := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hp
      have ho := Semiformula.models_lMap.mp hm
      simpa [models_iff] using ho
  | mp a b ha hb =>
      apply mapped_of_valid
      intro M _ _ _ _ f
      letI : Structure ℒₒᵣ M := (inferInstance : Structure language M).lMap embedding
      have h₁ := valid_of_mapped ha f
      have h₂ := valid_of_mapped hb f
      simp only [LogicalConnective.HomClass.map_imply] at h₁
      exact h₁ h₂
  | generalize a ha =>
      apply mapped_of_valid
      intro M _ _ _ _ f
      letI : Structure ℒₒᵣ M := (inferInstance : Structure language M).lMap embedding
      simp only [Semiformula.eval_all]
      intro x
      have hx := valid_of_mapped ha (x :>ₙ f)
      simpa [Rewriting.free] using hx
  | specialize t a ha =>
      apply mapped_of_valid
      intro M _ _ _ _ f
      letI : Structure ℒₒᵣ M := (inferInstance : Structure language M).lMap embedding
      have hf := valid_of_mapped ha f
      simp only [Semiformula.eval_all] at hf
      simpa using hf (t.val ![] f)
  | induction h a b ha hb => exact hadmit _ h ha hb
end DiophantineConsistency.ParsonsPositiveComparison
