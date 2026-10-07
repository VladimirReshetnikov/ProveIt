import OAI.Combinatorics.Progressions.Estimates.RealPolarizedLogDiagonal
import OAI.Combinatorics.Progressions.Linear.RealComparisonCoefficientProjections

namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped TensorProduct BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def realComparisonLog (p : F.realification.adaptedLieSubalgebra) :
    VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.comparisonSubalgebra π) :=
  ∑ a ∈ (coefficients p.val).support, monomial a (F.realComparisonCoefficient π p a)

theorem realComparisonLog_coefficient (p : F.realification.adaptedLieSubalgebra) (a : σ →₀ ℕ) :
    coefficients (F.realComparisonLog π p) a = F.realComparisonCoefficient π p a := by
  classical
  simp only [realComparisonLog, map_sum, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single a]
  · rw [coefficients_monomial, Finsupp.single_eq_same]
  · intro b _ hba
    rw [coefficients_monomial]
    exact Finsupp.single_eq_of_ne (Ne.symm hba)
  · intro ha
    rw [coefficients_monomial, Finsupp.single_eq_same]
    exact F.realComparisonCoefficient_zero_value π p a (Finsupp.notMem_support_iff.mp ha)

theorem realComparisonLog_adapted (p : F.realification.adaptedLieSubalgebra) :
    (F.comparisonFiltration π).realification.Adapted (fun _ => 1) (F.realComparisonLog π p) := by
  apply ((F.comparisonFiltration π).realification.adapted_iff_coefficients _ _).mpr
  intro a
  rw [F.realComparisonLog_coefficient]
  exact F.realComparisonCoefficient_mem π p a

theorem realComparisonLog_eval (p : F.realification.adaptedLieSubalgebra) (x : σ → ℚ) :
    eval x (F.realComparisonLog π p) =
      ∑ a ∈ (coefficients p.val).support,
        (a.prod fun i n => x i ^ n) • F.realComparisonCoefficient π p a := by
  simp only [realComparisonLog, map_sum, eval_monomial]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem realComparisonLog_first (p : F.realification.adaptedLieSubalgebra)
    (hp : coefficients p.val 0 = 0) :
    VectorPolynomial.map ((realificationLieHom (F.comparisonFirst π)).toLinearMap.restrictScalars ℚ)
      (F.realComparisonLog π p) = p.val := by
  apply coefficients.injective
  ext a
  rw [coefficients_map, F.realComparisonLog_coefficient]
  exact F.realComparisonCoefficient_first π p hp a

theorem realComparisonLog_first_eval (p : F.realification.adaptedLieSubalgebra)
    (hp : coefficients p.val 0 = 0) (x : σ → ℚ) :
    realificationLieHom (F.comparisonFirst π) (eval x (F.realComparisonLog π p)) = eval x p.val := by
  change ((realificationLieHom (F.comparisonFirst π)).toLinearMap.restrictScalars ℚ)
    (eval x (F.realComparisonLog π p)) = _
  rw [← eval_map, F.realComparisonLog_first π p hp]

theorem realComparisonLog_second_ambient (p : F.realification.adaptedLieSubalgebra)
    (hp : coefficients p.val 0 = 0) (x : σ → ℚ) :
    F.realSquarefreeInclusion π
        (realificationLieHom (F.comparisonSecond π) (eval x (F.realComparisonLog π p))) =
      realBlockPolynomialEval π p.val x := by
  rw [F.realComparisonLog_eval]
  simp only [map_sum, map_rat_smul, F.realComparisonCoefficient_second π p hp]
  rfl

theorem realComparisonLog_second_eval (p : F.realification.adaptedLieSubalgebra)
    (hp : coefficients p.val 0 = 0) (x : σ → ℚ) :
    realificationLieHom (F.comparisonSecond π) (eval x (F.realComparisonLog π p)) =
      eval (fun j => x (π j)) (F.realPolarizedLog π p) := by
  apply F.realSquarefreeInclusion_injective π
  rw [F.realComparisonLog_second_ambient π p hp, F.realPolarizedLog_diagonal π p hp]

end Erdos3.MultidegreeLieFiltration

end

end OAI
