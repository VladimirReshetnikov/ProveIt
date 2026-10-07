import OAI.Combinatorics.Progressions.Dynamics.AllocatedFixedPathSlicedNativeAmbientComparison

namespace OAI

section

namespace Erdos3

def forecastComparisonMeshPolynomial (t grid : ℝ) : ℝ :=
  (2 * t + 1) * (grid + t + 9) + 12 * t + 2 * grid + t + 12

def forecastComparisonFloorPolynomial (t source grid : ℝ) : ℝ :=
  (5 * t + 2 * source + 32) +
    (4 * t + grid + forecastComparisonMeshPolynomial t grid + 12)

theorem forecastComparisonMeshPolynomial_nonneg {t grid : ℝ}
    (ht : 0 ≤ t) (hgrid : 0 ≤ grid) :
    0 ≤ forecastComparisonMeshPolynomial t grid := by
  unfold forecastComparisonMeshPolynomial
  positivity

theorem forecastComparisonFloorPolynomial_nonneg {t source grid : ℝ}
    (ht : 0 ≤ t) (hsource : 0 ≤ source) (hgrid : 0 ≤ grid) :
    0 ≤ forecastComparisonFloorPolynomial t source grid := by
  unfold forecastComparisonFloorPolynomial
  have := forecastComparisonMeshPolynomial_nonneg ht hgrid
  positivity

theorem forecastJointGridMeshLog_le_comparisonPolynomial (d : ℕ)
    {t P E grid : ℝ} (ht : 0 ≤ t) (hd : (d : ℝ) ≤ 2 * t)
    (hP0 : 0 ≤ P) (hP : P ≤ grid) (hE0 : 0 ≤ E) (hE : E ≤ t) :
    forecastJointGridMeshLog d P (E + 4) ≤ forecastComparisonMeshPolynomial t grid := by
  have hmul : ((d : ℝ) + 1) * (P + (E + 4) + 5) ≤
      (2 * t + 1) * (grid + t + 9) :=
    mul_le_mul (by linarith only [hd]) (by linarith only [hP, hE])
      (by linarith only [hP0, hE0]) (by linarith only [ht])
  unfold forecastJointGridMeshLog forecastComparisonMeshPolynomial
  linarith only [hmul, hd, hP, hE]

theorem forecastJointGridAmbientLog_le_comparisonPolynomial (d : ℕ)
    {t P E V Pτ grid : ℝ} (ht : 0 ≤ t) (hd : (d : ℝ) ≤ 2 * t)
    (hP0 : 0 ≤ P) (hP : P ≤ grid) (hE0 : 0 ≤ E) (hE : E ≤ t)
    (hV : V ≤ 2 * t) (hPτ : Pτ ≤ t) :
    forecastJointGridAmbientLog d P (E + 4) V Pτ ≤
      4 * t + grid + forecastComparisonMeshPolynomial t grid + 12 := by
  have hmesh := forecastJointGridMeshLog_le_comparisonPolynomial d ht hd hP0 hP hE0 hE
  unfold forecastJointGridAmbientLog
  linarith only [hmesh, hP, hE, hV, hPτ]

theorem allocatedFixedPathSlicedAmbientFloorLog_le_comparisonPolynomial (d : ℕ)
    {t D P V cost E Pg PR source grid : ℝ}
    (ht : 0 ≤ t) (hd : (d : ℝ) ≤ 2 * t)
    (hD : D ≤ t) (hP : P ≤ source) (hV : V ≤ 2 * t)
    (hcost : cost ≤ t) (hE0 : 0 ≤ E) (hE : E ≤ t)
    (hPg0 : 0 ≤ Pg) (hPg : Pg ≤ grid) (hPR : PR ≤ t)
    (hsource : 0 ≤ source) (hgrid : 0 ≤ grid) :
    allocatedFixedPathSlicedAmbientFloorLog d D P V cost E Pg PR ≤
      forecastComparisonFloorPolynomial t source grid := by
  have hmesh := forecastJointGridMeshLog_le_comparisonPolynomial d ht hd hPg0 hPg hE0 hE
  have hfirst : D + 2 * P + V + cost + E + 32 ≤ 5 * t + 2 * source + 32 := by
    linarith only [hD, hP, hV, hcost, hE]
  have hsecond : forecastJointGridSamplerLog d Pg (E + 4) V PR + 1 ≤
      4 * t + grid + forecastComparisonMeshPolynomial t grid + 12 := by
    unfold forecastJointGridSamplerLog
    linarith only [hmesh, hPg, hE, hV, hPR]
  have hfirst0 : 0 ≤ 5 * t + 2 * source + 32 := by positivity
  have hsecond0 : 0 ≤ 4 * t + grid + forecastComparisonMeshPolynomial t grid + 12 := by
    have := forecastComparisonMeshPolynomial_nonneg ht hgrid
    positivity
  unfold allocatedFixedPathSlicedAmbientFloorLog forecastComparisonFloorPolynomial
  exact max_le (hfirst.trans (le_add_of_nonneg_right hsecond0))
    (hsecond.trans (le_add_of_nonneg_left hfirst0))

end Erdos3

end

end OAI
