import OAI.Combinatorics.Progressions.Geometry.RealPolarizedCoefficientCoordinates
import OAI.Combinatorics.Progressions.Polynomial.BlockMonomialWeight

namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem realPolarizedLog_diagonal (p : F.realification.adaptedLieSubalgebra)
    (hp : coefficients p.val 0 = 0) (x : σ → ℚ) :
    F.realSquarefreeInclusion π (eval (fun j => x (π j)) (F.realPolarizedLog π p)) =
      realBlockPolynomialEval π p.val x := by
  apply realSquarefreePolynomialEquiv.injective
  ext c
  rw [F.realPolarizedLog_eval_coefficient, realBlockPolynomialEval_coefficient,
    blockExponent_weight π c.val x]
  by_cases hc : c.val = 0
  · rw [F.realPolarizedCoefficient_zero π p c hc, map_zero, map_zero, Pi.zero_apply]
    simp only [smul_zero, hc, blockExponent_zero, hp]
  · rw [F.realPolarizedCoefficient_self π p c hc]

end Erdos3.MultidegreeLieFiltration

end

end OAI
