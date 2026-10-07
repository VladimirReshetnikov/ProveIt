/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.ComparisonAmbient

namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem realComparisonCoefficient_first (p : F.realification.adaptedLieSubalgebra)
    (hp : coefficients p.val 0 = 0) (a : σ →₀ ℕ) :
    realificationLieHom (F.comparisonFirst π) (F.realComparisonCoefficient π p a) =
      coefficients p.val a := by
  by_cases ha : a = 0
  · subst a
    rw [F.realComparisonCoefficient_zero_index, map_zero, hp]
  · rw [realComparisonCoefficient, dite_eq_right ha, F.realComparisonGraphLift_first]

theorem realComparisonCoefficient_second (p : F.realification.adaptedLieSubalgebra)
    (hp : coefficients p.val 0 = 0) (a : σ →₀ ℕ) :
    F.realSquarefreeInclusion π
        (realificationLieHom (F.comparisonSecond π) (F.realComparisonCoefficient π p a)) =
      (factorialBlockMonomial π (fun i => a i)).baseChange ℝ (coefficients p.val a) := by
  by_cases ha : a = 0
  · subst a
    rw [F.realComparisonCoefficient_zero_index, map_zero, map_zero, hp, map_zero]
  · rw [realComparisonCoefficient, dite_eq_right ha, F.realComparisonGraphLift_second]

end Erdos3.MultidegreeLieFiltration

end

end OAI
