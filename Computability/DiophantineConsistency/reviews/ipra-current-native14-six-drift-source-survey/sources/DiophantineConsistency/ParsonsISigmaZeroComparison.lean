import DiophantineConsistency.ParsonsHierarchyMap
import DiophantineConsistency.ParsonsMapInduction
import DiophantineConsistency.PRABoundedInduction
import DiophantineConsistency.PRAPeanoMinusTranslation
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsISigmaZeroComparison
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory PRABoundedInduction PRAPeanoMinusTranslation

/-- Every actual Foundation IΣ₀ theorem translates to candidate PRA. -/
theorem comparison {σ : ArithmeticSentence} (h : 𝗜𝚺₀ ⊢ σ) :
    PRA ⊢ Semiformula.lMap embedding σ := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  letI : Structure ℒₒᵣ M := (inferInstance : Structure language M).lMap embedding
  have hPA : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := by
    constructor
    intro τ hτ
    have hp := PRA_proves_peanoMinusAxiom hτ
    have hm := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hp
    exact Semiformula.models_lMap.mp hm
  have hInd : ∀ (A : ArithmeticSemiformula ℕ 1), Hierarchy 𝚺 0 A →
      ∀ f : ℕ → M, (succInd A).Evalf f := by
    intro A hA f
    have hmapped : Hierarchy 𝚺 0 (Semiformula.lMap embedding A) := ParsonsHierarchyMap.hierarchy hA
    have hp := PRA_proves_boundedInduction (Semiformula.lMap embedding A) hmapped
    have hm := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hp
    simp only [models_iff, Semiformula.eval_univCl] at hm
    have hv := hm f
    rw [← ParsonsMapInduction.map_succInd] at hv
    exact Semiformula.eval_lMap.mp hv
  have hI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := by
    constructor
    intro τ hτ
    rcases hτ with hτ | hτ
    · exact Theory.models (T := 𝗣𝗔⁻) M hτ
    · obtain ⟨A,hA,rfl⟩ := hτ
      simp only [models_iff, Semiformula.eval_univCl]
      exact hInd A hA
  have hσ := models_of_provable hI h
  exact Semiformula.models_lMap.mpr hσ
end DiophantineConsistency.ParsonsISigmaZeroComparison
