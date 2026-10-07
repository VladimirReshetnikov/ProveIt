import OAI.Combinatorics.Progressions.Estimates.AllocatedProfileDimensions

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

noncomputable def spatialProjectionBudget {T : Type*} [Semiring T] (q : ℕ) (P : T) : T :=
  let j : T := q + 1
  let b := j * (P + 2) + j ^ 2 + j + (P + 2) + 2 * (P + 1) + comparisonProfileBound + 2
  2 * j ^ 2 + (2 * j + 4) * b + (j + 2 * (P + 1)) * (b + 4) + 4 + 4 * P + 12

theorem spatialProjectionBudget_nonneg (q : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ spatialProjectionBudget q P := by
  unfold spatialProjectionBudget
  positivity

theorem physicalSpatialLogAllowance_le_projection_budget {K : Type*} [Fintype K]
    {q : ℕ} (s : Fin q ↪ K) {P : ℝ} (hP : 0 ≤ P) (hK : (Fintype.card K : ℝ) ≤ P) :
    physicalSpatialLogAllowance s (P + 2) + 4 * P + 12 ≤ spatialProjectionBudget q P := by
  have hj : (Fintype.card (Unit ⊕ Fin q) : ℝ) = q + 1 := by simp [Nat.cast_add, add_comm]
  have hn : (Fintype.card (Option K) : ℝ) ≤ P + 1 := by
    simpa only [Fintype.card_option, Nat.cast_add, Nat.cast_one, add_comm] using add_le_add_right hK 1
  have hd : (Fintype.card (UnselectedColumn (physicalCubePivotIndex s)) : ℝ) ≤ P + 1 :=
    (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans hn
  have hf : (probabilityProfileLipschitz : ℝ) ≤ comparisonProfileBound := by
    apply (Nat.le_ceil _).trans
    unfold comparisonProfileBound
    push_cast
    linarith
  let b : ℝ := (q + 1) * (P + 2) + (q + 1) ^ 2 + (q + 1) +
    (P + 2) + 2 * (P + 1) + comparisonProfileBound + 2
  have hb : physicalSpatialCommonBudget (Fintype.card (Unit ⊕ Fin q))
      (Fintype.card (UnselectedColumn (physicalCubePivotIndex s))) (Fintype.card (Option K)) (P + 2) ≤ b := by
    unfold physicalSpatialCommonBudget affineProfileLogBound
    rw [hj]
    dsimp [b]
    nlinarith
  have hb0 : 0 ≤ physicalSpatialCommonBudget (Fintype.card (Unit ⊕ Fin q))
      (Fintype.card (UnselectedColumn (physicalCubePivotIndex s))) (Fintype.card (Option K)) (P + 2) :=
    (by linarith : 0 ≤ P + 2).trans (physicalSpatialCommonBudget_bounds _ _ _ (by linarith)).1
  unfold physicalSpatialLogAllowance coefficientLogAllowance spatialProjectionBudget
  dsimp only
  rw [hj]
  change 2 * ((q : ℝ) + 1) ^ 2 + (2 * ((q : ℝ) + 1) + 4) * _ +
    (((q : ℝ) + 1) + 2 * (Fintype.card (UnselectedColumn (physicalCubePivotIndex s)) : ℝ)) *
      (_ + 4) + 4 + 4 * P + 12 ≤ _
  gcongr

end Erdos3.BooleanCubeKernel

end

end OAI
