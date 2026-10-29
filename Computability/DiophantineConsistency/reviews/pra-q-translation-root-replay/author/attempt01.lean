import DiophantineConsistency.PRAQOrder

/-! Translating all Foundation Robinson Q theorems into candidate PRA. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAQProofTranslation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory PRAQOrder

/-- Every Q theorem has a candidate-PRA proof of its mapped sentence. This is
an existence result via first-order soundness and completeness. -/
theorem PRA_proves_qTheorem {σ : Sentence ℒₒᵣ} (h : RobinsonQ ⊢ σ) :
    PRA ⊢ Semiformula.lMap embedding σ := by
  apply Theory.Proof.complete_on_eq_models.{0, 0}
  intro M _ _ _ _
  letI : Structure ℒₒᵣ M := (inferInstance : Structure language M).lMap embedding
  have hQ : M↓[ℒₒᵣ] ⊧* RobinsonQ := by
    constructor
    intro φ hφ
    have hp := PRA_proves_all_Q hφ
    have hm := Theory.models_of_provable (inferInstance : M↓[language] ⊧* PRA) hp
    exact Semiformula.models_lMap.mp hm
  have hσ := Theory.models_of_provable hQ h
  exact Semiformula.models_lMap.mpr hσ

end DiophantineConsistency.PRAQProofTranslation
