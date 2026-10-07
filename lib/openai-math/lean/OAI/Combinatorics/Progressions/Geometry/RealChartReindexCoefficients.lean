/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Polynomial.RealPolynomialChartSubstitution

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

variable {σ τ R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem coefficients_substitute_reindex (e : τ ≃ σ)
    (P : VectorPolynomial σ R V) (α : τ →₀ ℕ) :
    coefficients (substitute (fun i => MvPolynomial.X (e.symm i)) P) α =
      coefficients P (α.mapDomain e) := by
  have hα : (α.mapDomain e).mapDomain e.symm = α := by
    ext i
    simp only [Finsupp.mapDomain_equiv_apply, Equiv.symm_symm, Equiv.symm_apply_apply]
  induction P using TensorProduct.inductionOn with
  | tmul p v =>
    simp only [substitute_tmul, coefficients_tmul]
    change (MvPolynomial.aeval (MvPolynomial.X ∘ e.symm) p).coeff α • v = _
    rw [← MvPolynomial.rename_eq_aeval]
    exact congrArg (fun c : R => c • v)
      (by simpa only [hα] using
        MvPolynomial.coeff_rename_mapDomain e.symm e.symm.injective p (α.mapDomain e))
  | add p q hp hq => simp only [map_add, Finsupp.add_apply, hp, hq]

variable [Module ℚ V] [Module ℝ V] [IsScalarTower ℚ ℝ V]

theorem coefficients_realChartSubstitute_reindex (e : τ ≃ σ)
    (P : VectorPolynomial σ ℚ V) (α : τ →₀ ℕ) :
    coefficients (realChartSubstitute (fun i => MvPolynomial.X (e.symm i)) P) α =
      coefficients P (α.mapDomain e) := by
  simp only [realChartSubstitute, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.restrictScalars_apply, coefficients_realCoefficientEquiv_symm,
    coefficients_substitute_reindex, coefficients_realCoefficientEquiv]

@[simp] theorem coefficients_zero_realChartSubstitute_reindex (e : τ ≃ σ)
    (P : VectorPolynomial σ ℚ V) :
    coefficients (realChartSubstitute (fun i => MvPolynomial.X (e.symm i)) P) 0 =
      coefficients P 0 := by
  simp only [coefficients_realChartSubstitute_reindex, Finsupp.mapDomain_zero]

end Erdos3.VectorPolynomial

end

end OAI
