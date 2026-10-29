import DiophantineConsistency.ParsonsBoundedProof
import DiophantineConsistency.ParsonsHierarchyMap
import DiophantineConsistency.ParsonsMapInduction
import DiophantineConsistency.PRABoundedInduction
import DiophantineConsistency.PRAPeanoMinusTranslation
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsBoundedComparison
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory PRABoundedInduction PRAPeanoMinusTranslation

/-- Every bounded-rule proof translates to an actual candidate-PRA theorem
of the universally closed language-mapped conclusion. -/
theorem comparison {φ : Proposition ℒₒᵣ} (p : ParsonsBoundedProof.Proof 𝗣𝗔⁻ φ) :
    PRA ⊢ (Semiformula.lMap embedding φ).univCl := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  letI : Structure ℒₒᵣ M := (inferInstance : Structure language M).lMap embedding
  have hPA : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := by
    constructor
    intro σ hσ
    have hp := PRA_proves_peanoMinusAxiom hσ
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
  have hv := ParsonsBoundedProof.sound hPA hInd p
  simp only [models_iff, Semiformula.eval_univCl]
  intro f
  exact Semiformula.eval_lMap.mpr (hv f)
end DiophantineConsistency.ParsonsBoundedComparison
