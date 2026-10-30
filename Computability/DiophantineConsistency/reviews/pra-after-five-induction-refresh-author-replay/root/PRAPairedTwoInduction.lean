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
    apply PRA_proof_of_model_axiom_replacement _ _ _ ?_ p
    intro M _ _ _ _ hpair
    constructor
    intro σ hσ
    simp only [twoAxioms, Set.mem_insert_iff, Set.mem_singleton_iff] at hσ
    rcases hσ with hσ | hσ
    · subst σ
      exact modelPairedSuccInd_zero ψ₀ ψ₁ hpair
    · subst σ
      exact modelPairedSuccInd_one ψ₀ ψ₁ hpair
  exact PRA_proves_goal_of_boundedSuccInd (pairedMatrix ψ₀ ψ₁)
    (pairedMatrix_bounded ψ₀ ψ₁ h₀ h₁) θ hθ hp
end DiophantineConsistency.PRAPairedTwoInduction
