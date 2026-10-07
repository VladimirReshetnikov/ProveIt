import OAI.Combinatorics.Progressions.Linear.BooleanJetMatrixFactor

namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem homogeneous_factorization_to_bounded_site {K S J : Type*} [Fintype J]
    (U : Submodule ℝ (J → ℝ)) (h : ℕ) (site : S → K → ℝ)
    (frequency : (K →₀ ℕ) → J → ℝ) (M : (S → U) →ₗ[ℝ] ℝ)
    (hf : ∀ p : VectorPolynomial (Option K) ℝ U, Homogeneous h p →
      affineModeLift (coefficientFunctional frequency) (map U.subtype p) =
        M (siteEvaluation (fun s (k : Option K) => k.elim 1 (site s)) p)) :
    ∀ p : VectorPolynomial K ℝ U, DegreeLE (1 : K → ℕ) h p →
      coefficientFunctional frequency (map U.subtype p) = M (siteEvaluation site p) := by
  let L := (coefficientFunctional frequency).comp (map U.subtype)
  have hlift : ∀ p, Homogeneous h p → affineModeLift L p =
      M (siteEvaluation (fun s (k : Option K) => k.elim 1 (site s)) p) := by
    simpa only [L, affineModeLift_comp_map, LinearMap.comp_apply] using hf
  exact (homogeneous_site_factorization_iff h site L M).mp hlift

end Erdos3.VectorPolynomial

end

end OAI
