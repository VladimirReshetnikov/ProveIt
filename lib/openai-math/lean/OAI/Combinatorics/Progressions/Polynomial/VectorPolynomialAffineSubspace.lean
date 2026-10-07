import OAI.Combinatorics.Progressions.Lattices.LayerSamplingRankAffine

namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {I K R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem coefficients_substitute_nonzero_mem (W : Submodule R V)
    (f : I → MvPolynomial K R) (P : VectorPolynomial I R V)
    (hP : ∀ β, β ≠ 0 → coefficients P β ∈ W)
    (α : K →₀ ℕ) (hα : α ≠ 0) :
    coefficients (substitute f P) α ∈ W := by
  classical
  rw [coefficients_substitute]
  apply Submodule.sum_mem
  intro β hβ
  by_cases hβ0 : β = 0
  · subst β
    simp [MvPolynomial.coeff_one, Ne.symm hα]
  · exact W.smul_mem _ (hP β hβ0)

theorem coefficients_residueAffine_nonzero_mem {V : Type*}
    [AddCommGroup V] [Module ℝ V] (W : Submodule ℝ V)
    (q : ℕ) (r : I → ℤ) (P : VectorPolynomial I ℝ V)
    (hP : ∀ β, β ≠ 0 → coefficients P β ∈ W)
    (α : I →₀ ℕ) (hα : α ≠ 0) :
    coefficients (residueAffine q r P) α ∈ W :=
  coefficients_substitute_nonzero_mem W _ P hP α hα

end Erdos3.VectorPolynomial

end

end OAI
