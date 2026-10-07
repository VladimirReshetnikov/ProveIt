import OAI.Combinatorics.Progressions.Estimates.AllocatedProfileDimensions

namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedModularGeneralLateFloorScale_budget (A : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {P Qw Pmin geometryBudget : ℝ},
      0 ≤ P → 0 ≤ Qw → 0 ≤ Pmin → 0 ≤ geometryBudget →
      geometryBudget ≤ (P + A) ^ A →
      allocatedWitnessScaleLog geometryBudget Qw + (1 + geometryBudget ^ 2) * Pmin ≤
        (P + Qw + Pmin + C) ^ C := by
  let U : Polynomial ℕ := (Polynomial.X + Polynomial.C A) ^ A
  let poly : Polynomial ℕ :=
    (1 + U ^ 2) * (5 * U + 49) + U ^ 2 * Polynomial.X +
      (1 + U ^ 2) * Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨C, hC, ?_⟩
  intro P Qw Pmin geometryBudget hP hQw hPmin hgeometry hbound
  have hsum : 0 ≤ P + Qw + Pmin := by positivity
  have hPsum : P ≤ P + Qw + Pmin := by linarith
  have hQsum : Qw ≤ P + Qw + Pmin := by linarith
  have hminsum : Pmin ≤ P + Qw + Pmin := by linarith
  have hgeometry' : geometryBudget ≤ (P + Qw + Pmin + A) ^ A :=
    hbound.trans (pow_le_pow_left₀ (show 0 ≤ P + (A : ℝ) by positivity)
      (by linarith only [hPsum]) A)
  have hpoly := hbudget (P + Qw + Pmin) hsum
  have hmono : allocatedWitnessScaleLog geometryBudget Qw + (1 + geometryBudget ^ 2) * Pmin ≤
      (1 + ((P + Qw + Pmin + A) ^ A) ^ 2) *
        (5 * (P + Qw + Pmin + A) ^ A + 49) +
      ((P + Qw + Pmin + A) ^ A) ^ 2 * (P + Qw + Pmin) +
      (1 + ((P + Qw + Pmin + A) ^ A) ^ 2) * (P + Qw + Pmin) := by
    unfold allocatedWitnessScaleLog allocatedScaleLog
    gcongr
  apply hmono.trans
  simpa [poly, U, Polynomial.eval₂_pow] using hpoly

end Erdos3.VectorPolynomial

end

end OAI
