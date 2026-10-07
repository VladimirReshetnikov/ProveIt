import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import OAI.Combinatorics.Progressions.Estimates.RealSymbolGradeQuotientSplitting

namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

theorem realifyFunctional_eq_finsupp_sum_basis {V ι : Type*} [AddCommGroup V] [Module ℚ V]
    (b : Basis ι ℚ V) (θ : V →ₗ[ℚ] ℚ) (x : ℝ ⊗[ℚ] V) :
    realifyFunctional θ x =
      ((b.baseChange ℝ).repr x).sum (fun i a => a * (θ (b i) : ℝ)) := by
  classical
  calc
    realifyFunctional θ x = realifyFunctional θ
        (((b.baseChange ℝ).repr x).sum (fun i a => a • (b.baseChange ℝ) i)) :=
      congrArg (realifyFunctional θ) ((b.baseChange ℝ).linearCombination_repr x).symm
    _ = _ := by
      simp only [Finsupp.sum, map_sum, map_smul, Basis.baseChange_apply,
        realifyFunctional_tmul, one_mul, smul_eq_mul]

namespace NilpotentLieFiltration

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (v : σ → ℕ)
    (θ : F.AssociatedGraded →ₗ[ℚ] ℚ) (r : ℕ)
    (hθ : ∀ i, ω i ≠ r → θ (F.associatedGradedBasis b ω hF i) = 0)

include hθ

theorem coeff_scalarSymbolPolynomial_of_weight_ne
    (g : F.RealPolynomialSymbolGroup v) (α : σ →₀ ℕ) (hα : Finsupp.weight v α ≠ r) :
    (F.scalarSymbolPolynomial b ω hF v θ g).coeff α = 0 := by
  classical
  rw [F.coeff_scalarSymbolPolynomial,
    realifyFunctional_eq_finsupp_sum_basis (F.associatedGradedBasis b ω hF)]
  unfold Finsupp.sum
  apply Finset.sum_eq_zero
  intro i _
  dsimp only
  by_cases hi : ω i = r
  · rw [F.realGradedSymbolPolynomial_coordinate_of_ne b ω hF v g.coord α i
      (by simpa only [hi] using hα), zero_mul]
  · rw [hθ i hi, Rat.cast_zero, mul_zero]

theorem scalarSymbolPolynomial_isWeightedHomogeneous
    (g : F.RealPolynomialSymbolGroup v) :
    (F.scalarSymbolPolynomial b ω hF v θ g).IsWeightedHomogeneous v r := by
  intro α hα
  by_contra hne
  exact hα (F.coeff_scalarSymbolPolynomial_of_weight_ne b ω hF v θ r hθ g α hne)

theorem scalarSymbolPolynomial_coeff_zero_of_pos (hr : 0 < r)
    (g : F.RealPolynomialSymbolGroup v) :
    (F.scalarSymbolPolynomial b ω hF v θ g).coeff 0 = 0 :=
  F.coeff_scalarSymbolPolynomial_of_weight_ne b ω hF v θ r hθ g 0 (by
    simpa only [map_zero] using (Nat.ne_of_gt hr).symm)

theorem scalarSymbolPolynomial_constantCoeff_eq_zero_of_pos (hr : 0 < r)
    (g : F.RealPolynomialSymbolGroup v) :
    MvPolynomial.constantCoeff (F.scalarSymbolPolynomial b ω hF v θ g) = 0 := by
  rw [MvPolynomial.constantCoeff_eq]
  exact F.scalarSymbolPolynomial_coeff_zero_of_pos b ω hF v θ r hθ hr g

end NilpotentLieFiltration
end Erdos3

end

end OAI
