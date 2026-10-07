import OAI.Combinatorics.Progressions.Estimates.AdaptedMarkedMapHeight
import OAI.Combinatorics.Progressions.Polynomial.PolynomialShearParameterBudget

namespace OAI

section

namespace Erdos3

def adaptedMapGeometryBudget (p : ℝ) : ℝ :=
  (p + 3) ^ 11 + (p + 4) ^ 11 + adaptedMarkedMapHeightBudget (p + 1) + p + 2

theorem adaptedMapGeometryBudget_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ adaptedMapGeometryBudget p := by
  unfold adaptedMapGeometryBudget adaptedMarkedMapHeightBudget
  positivity

theorem adaptedMapGeometryBudget_geometry {p : ℝ} (hp : 0 ≤ p) :
    (p + 3) ^ 11 ≤ adaptedMapGeometryBudget p := by
  have hinverse : 0 ≤ (p + 4) ^ 11 := by positivity
  have hmap : 0 ≤ adaptedMarkedMapHeightBudget (p + 1) := by
    unfold adaptedMarkedMapHeightBudget
    positivity
  unfold adaptedMapGeometryBudget
  linarith

theorem adaptedMapGeometryBudget_inverse {p : ℝ} (hp : 0 ≤ p) :
    (p + 4) ^ 11 ≤ adaptedMapGeometryBudget p := by
  have hgeometry : 0 ≤ (p + 3) ^ 11 := by positivity
  have hmap : 0 ≤ adaptedMarkedMapHeightBudget (p + 1) := by
    unfold adaptedMarkedMapHeightBudget
    positivity
  unfold adaptedMapGeometryBudget
  linarith

theorem adaptedMapGeometryBudget_markedMap {p : ℝ} (hp : 0 ≤ p) :
    adaptedMarkedMapHeightBudget (p + 1) ≤ adaptedMapGeometryBudget p := by
  have hgeometry : 0 ≤ (p + 3) ^ 11 := by positivity
  have hinverse : 0 ≤ (p + 4) ^ 11 := by positivity
  unfold adaptedMapGeometryBudget
  linarith

theorem adaptedMapGeometryBudget_parameter {p : ℝ} (hp : 0 ≤ p) :
    p + 2 ≤ adaptedMapGeometryBudget p := by
  have hgeometry : 0 ≤ (p + 3) ^ 11 := by positivity
  have hinverse : 0 ≤ (p + 4) ^ 11 := by positivity
  have hmap : 0 ≤ adaptedMarkedMapHeightBudget (p + 1) := by
    unfold adaptedMarkedMapHeightBudget
    positivity
  unfold adaptedMapGeometryBudget
  linarith

theorem exists_adaptedMapGeometryBudget_fixed_power :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      adaptedMapGeometryBudget p + 1 ≤ (p + 2) ^ C := by
  let P : Polynomial ℕ :=
    (Polynomial.X + 3) ^ 11 + (Polynomial.X + 4) ^ 11 +
      ((Polynomial.X + 1) + ((Polynomial.X + 1) + 4) ^ 5 +
        ((Polynomial.X + 1) + 2) ^ 4 + 2) ^ 4 + Polynomial.X + 2 + 1
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_fixed_power_budget P
  refine ⟨C, hC, fun p hp => ?_⟩
  simpa [P, adaptedMapGeometryBudget, adaptedMarkedMapHeightBudget, Polynomial.eval₂_pow]
    using hbound p hp

end Erdos3

end

end OAI
