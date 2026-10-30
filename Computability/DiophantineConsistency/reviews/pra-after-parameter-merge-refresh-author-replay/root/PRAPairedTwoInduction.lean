import DiophantineConsistency.PRAPairedInductionSemantics
import DiophantineConsistency.PRABoundedOneInduction
/-! Eliminate two parameter-dependent bounded Σ₁ induction instances by
combining them into one bounded induction instance using the pair graph. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace DiophantineConsistency.PRAPairedTwoInduction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAOpenOneInduction
  PRABoundedOneInduction PRAPairedInductionMatrix PRAPairedInductionSemantics

def twoAxioms (ψ₀ ψ₁ : Semisentence language 3) : Theory language :=
  {(succInd (openSigma ψ₀)).univCl, (succInd (openSigma ψ₁)).univCl}

theorem PRA_proves_goal_of_two_boundedSuccInd
    (ψ₀ ψ₁ : Semisentence language 3) (h₀ : Hierarchy 𝚺 0 ψ₀)
    (h₁ : Hierarchy 𝚺 0 ψ₁) (θ : Semiproposition language 1) (hθ : θ.Open)
    (p : (PRA ∪ twoAxioms ψ₀ ψ₁) ⊢ (∃⁰ θ).univCl) :
    PRA ⊢ (∃⁰ θ).univCl := by
  have hp : (PRA ∪ {(succInd (openSigma (pairedMatrix ψ₀ ψ₁))).univCl}) ⊢ (∃⁰ θ).univCl := by
    letI : 𝗘𝗤 language ⪯ (PRA ∪ {(succInd (openSigma (pairedMatrix ψ₀ ψ₁))).univCl}) :=
      Entailment.WeakerThan.ofSubset (fun _ h => Or.inl (Or.inl (Or.inl (Or.inl h))))
    apply Theory.Proof.complete_on_eq_models.{0,0}
    intro M _ _ _ hBoth
    letI : M↓[language] ⊧* PRA := by
      constructor
      intro σ hσ
      exact hBoth.models _ (Or.inl hσ)
    have hpair : M↓[language] ⊧ (succInd (openSigma (pairedMatrix ψ₀ ψ₁))).univCl :=
      hBoth.models _ (Or.inr rfl)
    have hPlus : M↓[language] ⊧* (PRA ∪ twoAxioms ψ₀ ψ₁) := by
      constructor
      intro σ hσ
      rcases hσ with hσ | hσ
      · exact (inferInstance : M↓[language] ⊧* PRA).models _ hσ
      · simp only [twoAxioms, Set.mem_insert_iff, Set.mem_singleton_iff] at hσ
        rcases hσ with hσ | hσ
        · subst σ
          exact modelPairedSuccInd_zero ψ₀ ψ₁ hpair
        · subst σ
          exact modelPairedSuccInd_one ψ₀ ψ₁ hpair
    exact models_of_provable hPlus p
  exact PRA_proves_goal_of_boundedSuccInd (pairedMatrix ψ₀ ψ₁)
    (pairedMatrix_bounded ψ₀ ψ₁ h₀ h₁) θ hθ hp
end DiophantineConsistency.PRAPairedTwoInduction
