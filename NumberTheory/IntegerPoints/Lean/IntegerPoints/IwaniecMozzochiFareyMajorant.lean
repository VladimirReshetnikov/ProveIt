import IntegerPoints.IwaniecMozzochi

/-!
# Endpoint-safe Farey majorization for Iwaniec--Mozzochi

This module proves that the exact `InFareySet` contribution in `deltaCHM`
is contained in the endpoint-safe rectangular range
`[A / 4, 2A) × [C, 2C)`, and hence is bounded by `deltaCHMMajorant`.
-/

namespace LeanProofs.IntegerPoints

/-- A genuine Farey numerator belonging to a denominator block
`C ≤ c < 2C` lies in the endpoint-safe numerator majorant
`A / 4 ≤ a < 2A`, where `A = x C / M²`.

The weak lower endpoint is essential: `InFareySet` allows equality in (6.2). -/
theorem inFareySet_mem_fareyMajorantNumerators
    {x C H M : ℝ} {a c : ℕ}
    (hmain : InMainRange x H M)
    (hc : c ∈ fareyDenominators C)
    (hfarey : InFareySet x H M a c) :
    a ∈ fareyMajorantNumerators (Ascale x C M) := by
  have hx : 0 < x := zero_lt_one.trans_le hmain.1
  have hM : 0 < M :=
    (Real.rpow_pos_of_pos hx theta0).trans hmain.2.1
  rw [fareyDenominators, Finset.mem_Ico] at hc
  have hcLower : C ≤ (c : ℝ) := Nat.ceil_le.mp hc.1
  have hcUpper : (c : ℝ) < 2 * C := Nat.lt_ceil.mp hc.2
  rcases hfarey with ⟨_, _, _, haLower, haUpper⟩
  rw [fareyMajorantNumerators, Finset.mem_Ico]
  constructor
  · apply Nat.ceil_le.mpr
    calc
      Ascale x C M / 4 = C * x / (2 * M) ^ 2 := by
        unfold Ascale
        field_simp [hM.ne']
        ring
      _ ≤ (c : ℝ) * x / (2 * M) ^ 2 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcLower hx.le)
          (sq_nonneg (2 * M))
      _ ≤ (a : ℝ) := haLower
  · apply Nat.lt_ceil.mpr
    calc
      (a : ℝ) ≤ (c : ℝ) * x / M ^ 2 := haUpper
      _ < (2 * C) * x / M ^ 2 :=
        div_lt_div_of_pos_right
          (mul_lt_mul_of_pos_right hcUpper hx)
          (sq_pos_of_pos hM)
      _ = 2 * Ascale x C M := by
        unfold Ascale
        ring

/-- The restricted Farey contribution is nonnegative throughout the main
range whenever the dyadic scale `C` is positive. -/
theorem deltaCHM_nonneg
    {χ σ : ℝ → ℝ} {x C H M : ℝ}
    (hmain : InMainRange x H M) (hC : 0 < C) :
    0 ≤ deltaCHM χ σ x C H M := by
  have hx : 0 < x := zero_lt_one.trans_le hmain.1
  have hM : 0 < M :=
    (Real.rpow_pos_of_pos hx theta0).trans hmain.2.1
  have hH : 0 < H := zero_lt_one.trans_le hmain.2.2.2.1
  have hN : 0 < shiftLength x M := by
    unfold shiftLength
    positivity
  have hGC : 0 ≤ Gscale x H M / C := by
    unfold Gscale
    positivity
  unfold deltaCHM
  refine mul_nonneg hGC ?_
  exact Finset.sum_nonneg fun _c _hc ↦
    Finset.sum_nonneg fun _a _ha ↦ abs_nonneg _

/-- Dropping the `InFareySet` conditions other than coprimality gives the
rectangular nonnegative majorant in (6.11). -/
theorem deltaCHM_le_deltaCHMMajorant
    {χ σ : ℝ → ℝ} {x C H M : ℝ}
    (hmain : InMainRange x H M) (hC : 0 < C) :
    deltaCHM χ σ x C H M ≤ deltaCHMMajorant χ σ x C H M := by
  classical
  have hx : 0 < x := zero_lt_one.trans_le hmain.1
  have hM : 0 < M :=
    (Real.rpow_pos_of_pos hx theta0).trans hmain.2.1
  have hH : 0 < H := zero_lt_one.trans_le hmain.2.2.2.1
  have hN : 0 < shiftLength x M := by
    unfold shiftLength
    positivity
  have hGC : 0 ≤ Gscale x H M / C := by
    unfold Gscale
    positivity
  unfold deltaCHM deltaCHMMajorant
  refine mul_le_mul_of_nonneg_left ?_ hGC
  refine Finset.sum_le_sum fun c _hc ↦ ?_
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter] at ha ⊢
    rcases ha with ⟨haRange, hfarey⟩
    rcases hfarey with ⟨_, _, hac, _, _⟩
    exact ⟨haRange, hac⟩
  · intro _a _ha _hnot
    exact abs_nonneg _

end LeanProofs.IntegerPoints
