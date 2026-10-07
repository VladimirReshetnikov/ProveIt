import OAI.Combinatorics.Progressions.Polynomial.RealPolarizedPolynomialOrbit

namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem realPolarizedCoefficient_self (p : F.realification.adaptedLieSubalgebra)
    (a : SquarefreeIndex ι) (ha : a.val ≠ 0) :
    realSquarefreePolynomialEquiv (F.realSquarefreeInclusion π (F.realPolarizedCoefficient π p a)) a =
      (multidegreeFactorial (blockDegree π a.val) : ℚ) •
        coefficients p.val (blockExponent π a.val) := by
  rw [F.realPolarizedCoefficient_inclusion π p a ha, map_rat_smul, Pi.smul_apply,
    realSquarefreeMonomial_self]

theorem realPolarizedCoefficient_ne (p : F.realification.adaptedLieSubalgebra)
    (a c : SquarefreeIndex ι) (hac : a ≠ c) :
    realSquarefreePolynomialEquiv (F.realSquarefreeInclusion π (F.realPolarizedCoefficient π p a)) c = 0 := by
  by_cases ha : a.val = 0
  · rw [F.realPolarizedCoefficient_zero π p a ha, map_zero, map_zero, Pi.zero_apply]
  · rw [F.realPolarizedCoefficient_inclusion π p a ha, map_rat_smul, Pi.smul_apply,
      realSquarefreeMonomial_ne a c hac, smul_zero]

theorem realPolarizedLog_eval_coefficient (p : F.realification.adaptedLieSubalgebra)
    (x : ι → ℚ) (c : SquarefreeIndex ι) :
    realSquarefreePolynomialEquiv (F.realSquarefreeInclusion π (eval x (F.realPolarizedLog π p))) c =
      (c.val.prod fun i n => x i ^ n) •
        realSquarefreePolynomialEquiv (F.realSquarefreeInclusion π (F.realPolarizedCoefficient π p c)) c := by
  classical
  let C : (ℝ ⊗[ℚ] F.SquarefreeAlgebra π) →ₗ[ℝ] (ℝ ⊗[ℚ] L) := (LinearMap.proj c).comp
    (realSquarefreePolynomialEquiv.toLinearMap.comp (F.realSquarefreeInclusion π))
  change C (eval x (F.realPolarizedLog π p)) = _
  rw [F.realPolarizedLog_eval, map_sum]
  simp only [LinearMap.map_smul_of_tower]
  rw [Finset.sum_eq_single c]
  · rfl
  · intro a _ hac
    have hz : C (F.realPolarizedCoefficient π p a) = 0 := F.realPolarizedCoefficient_ne π p a c hac
    rw [hz, smul_zero]
  · simp

end Erdos3.MultidegreeLieFiltration

end

end OAI
