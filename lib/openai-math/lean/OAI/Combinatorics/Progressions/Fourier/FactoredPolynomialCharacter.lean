import OAI.Combinatorics.Progressions.Estimates.HomogenizedModeFactorization

namespace OAI

section

namespace Erdos3.VectorPolynomial

open CircleFourier
open scoped BigOperators

theorem factored_polynomial_mode_character {I K S W : Type*} [Fintype S] [DecidableEq S]
    [AddCommGroup W] [Module ℝ W] (h : ℕ) (site : S → K → ℝ)
    (Λ : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ) (M : (S → W) →ₗ[ℝ] ℝ)
    (hfactor : ∀ q, DegreeLE (1 : K → ℕ) h q → Λ q = M (siteEvaluation site q))
    (p : VectorPolynomial I ℝ W) (hp : DegreeLE (1 : I → ℕ) h p)
    (f : I → MvPolynomial K ℝ) (hf : ∀ i, (f i).totalDegree ≤ 1) :
    character (Λ (substitute f p) : CircleFourier.Circle) =
      ∏ s, siteFunctionalCharacter M s (eval (fun i => MvPolynomial.aeval (site s) (f i)) p) := by
  rw [hfactor _ (degreeLE_substitute_affine f hf p hp), character_linear_site_sum]
  apply Finset.prod_congr rfl
  intro s _
  change siteFunctionalCharacter M s (eval (site s) (substitute f p)) = _
  rw [eval_substitute]

theorem homogeneously_factored_polynomial_character {I K S W : Type*} [Fintype S] [DecidableEq S]
    [AddCommGroup W] [Module ℝ W] (h : ℕ) (site : S → K → ℝ)
    (Λ : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ) (M : (S → W) →ₗ[ℝ] ℝ)
    (hfactor : ∀ q, Homogeneous h q → Λ (substitute dehomogenizingSubstitution q) =
      M (siteEvaluation (fun s (i : Option K) => i.elim 1 (site s)) q))
    (p : VectorPolynomial I ℝ W) (hp : DegreeLE (1 : I → ℕ) h p)
    (f : I → MvPolynomial K ℝ) (hf : ∀ i, (f i).totalDegree ≤ 1) :
    character (Λ (substitute f p) : CircleFourier.Circle) =
      ∏ s, siteFunctionalCharacter M s (eval (fun i => MvPolynomial.aeval (site s) (f i)) p) :=
  factored_polynomial_mode_character h site Λ M
    ((homogeneous_site_factorization_iff h site Λ M).mp hfactor) p hp f hf

end Erdos3.VectorPolynomial

end

end OAI
