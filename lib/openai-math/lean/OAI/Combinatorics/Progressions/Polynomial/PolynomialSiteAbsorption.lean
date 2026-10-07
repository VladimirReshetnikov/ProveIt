import OAI.Combinatorics.Progressions.Estimates.AbsorbedSiteTests
import OAI.Combinatorics.Progressions.Fourier.FactoredPolynomialCharacter

namespace OAI

section

namespace Erdos3.VectorPolynomial

open CircleFourier
open scoped BigOperators

theorem exists_absorbed_polynomial_site_tests {A I K S G : Type*} {W : A → Type*}
    [Fintype A] [Fintype S] [DecidableEq S]
    [∀ a, AddCommGroup (W a)] [∀ a, Module ℝ (W a)]
    (h : A → ℕ) (site : S → K → ℝ)
    (Λ : ∀ a, VectorPolynomial K ℝ (W a) →ₗ[ℝ] ℝ)
    (hfactor : ∀ a, ∃ M : (S → W a) →ₗ[ℝ] ℝ,
      ∀ q, Homogeneous (h a) q → Λ a (substitute dehomogenizingSubstitution q) =
        M (siteEvaluation (fun s (i : Option K) => i.elim 1 (site s)) q))
    (p : ∀ a, VectorPolynomial I ℝ (W a)) (hp : ∀ a, DegreeLE (1 : I → ℕ) (h a) (p a))
    (f : G → I → MvPolynomial K ℝ) (hf : ∀ g i, (f g i).totalDegree ≤ 1)
    (low : G → ℝ) (test : S → (I → ℝ) → ℂ) (htest : ∀ s x, ‖test s x‖ ≤ 1) :
    ∃ test' : S → (I → ℝ) → ℂ, (∀ s x, ‖test' s x‖ ≤ 1) ∧ ∀ g,
      character ((low g + ∑ a, Λ a (substitute (f g) (p a)) : ℝ) : CircleFourier.Circle) *
        (∏ s, test s (fun i => MvPolynomial.aeval (site s) (f g i))) =
      character (low g : CircleFourier.Circle) *
        (∏ s, test' s (fun i => MvPolynomial.aeval (site s) (f g i))) := by
  classical
  choose M hM using hfactor
  let χ : A → S → (I → ℝ) → ℂ := fun a s x => siteFunctionalCharacter (M a) s (eval x (p a))
  refine ⟨absorbedSiteTests χ test, ?_, ?_⟩
  · intro s x
    rw [absorbedSiteTests_norm χ (fun a s x => siteFunctionalCharacter_norm _ _ _) test]
    exact htest s x
  · intro g
    apply absorb_factored_phases χ test
      (fun g s i => MvPolynomial.aeval (site s) (f g i))
      (fun a g => Λ a (substitute (f g) (p a))) _ low g
    intro a g
    exact homogeneously_factored_polynomial_character (h a) site (Λ a) (M a) (hM a) (p a) (hp a) (f g) (hf g)

end Erdos3.VectorPolynomial

end

end OAI
