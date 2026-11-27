import GRHArticle.ProgressionFree.PolynomialReplacementSeries
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Raw tilted moments of one geometric degree factor

At degree `d > 0`, the geometric degree series is supported on multiples of `d`.
Reindexing along those multiples gives the mass and the first two raw moments
at a real tilt `z` with `0 ≤ z < 1`.
-/

namespace GRHArticle.ProgressionFree

private theorem hasSum_degreeGeometric_reindex {d : ℕ} (hd : 0 < d) {z a : ℝ}
    (weight : ℕ → ℝ) (hs : HasSum (fun k ↦ (z ^ d) ^ k * weight (d * k)) a) :
    HasSum (fun n ↦ (PowerSeries.coeff (R := ℕ) n (degreeGeometricSeries d) : ℝ) * z ^ n * weight n) a := by
  have hinj : Function.Injective (fun k : ℕ ↦ d * k) := fun _ _ h ↦ Nat.mul_left_cancel hd h
  apply (hinj.hasSum_iff (f := fun n ↦
    (PowerSeries.coeff (R := ℕ) n (degreeGeometricSeries d) : ℝ) * z ^ n * weight n) ?_).mp
  · simpa [Function.comp_def, degreeGeometricSeries, pow_mul] using hs
  · intro n hn
    have hnd : ¬ d ∣ n := fun ⟨k, hk⟩ ↦ hn ⟨k, hk.symm⟩
    simp [degreeGeometricSeries, hnd]

private theorem norm_degree_ratio_lt_one {d : ℕ} (hd : 0 < d) {z : ℝ}
    (hz₀ : 0 ≤ z) (hz₁ : z < 1) : ‖z ^ d‖ < 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hz₀ _)]
  exact pow_lt_one₀ hz₀ hz₁ hd.ne'

private theorem hasSum_sq_mul_geometric {r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r < 1) :
    HasSum (fun k : ℕ ↦ (k : ℝ) ^ 2 * r ^ k) (r * (1 + r) / (1 - r) ^ 3) := by
  have hnorm : ‖r‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hr₀] using hr₁
  let f (k : ℕ) := (k : ℝ) ^ 2 * r ^ k
  let g (k : ℕ) := (k : ℝ) * r ^ k
  let e (k : ℕ) := r ^ k
  have hf : Summable f := summable_pow_mul_geometric_of_norm_lt_one 2 hnorm
  have hg : HasSum g (r / (1 - r) ^ 2) := hasSum_coe_mul_geometric_of_norm_lt_one hnorm
  have he : HasSum e (1 - r)⁻¹ := hasSum_geometric_of_lt_one hr₀ hr₁
  let s := ∑' k, f k
  have hshift : ∑' k, f (k + 1) = s := by
    simpa [s, f] using hf.sum_add_tsum_nat_add 1
  have hterm (k : ℕ) : f (k + 1) = r * (f k + (2 * g k + e k)) := by
    simp only [f, g, e, Nat.cast_add, Nat.cast_one, pow_succ]
    ring
  have hshift' := ((hf.hasSum.add ((hg.mul_left 2).add he)).mul_left r).tsum_eq
  simp_rw [← hterm] at hshift'
  have hrec : s = r * (s + (2 * (r / (1 - r) ^ 2) + (1 - r)⁻¹)) :=
    hshift.symm.trans hshift'
  have hlinear : (1 - r) * s = r * (2 * (r / (1 - r) ^ 2) + (1 - r)⁻¹) := by
    linear_combination hrec
  have hden : 1 - r ≠ 0 := (sub_pos.mpr hr₁).ne'
  have hs : s = r * (1 + r) / (1 - r) ^ 3 := by
    calc
      s = ((1 - r) * s) / (1 - r) := by field_simp
      _ = _ := by rw [hlinear]; field_simp; ring
  exact hs ▸ hf.hasSum

/-- The tilted mass of one geometric degree factor is the geometric sum. -/
theorem hasSum_degreeGeometric_mass {d : ℕ} (hd : 0 < d) {z : ℝ} (hz₀ : 0 ≤ z) (hz₁ : z < 1) :
    HasSum (fun n ↦ (PowerSeries.coeff (R := ℕ) n (degreeGeometricSeries d) : ℝ) * z ^ n)
      (1 / (1 - z ^ d)) := by
  have hgeom := hasSum_geometric_of_lt_one (pow_nonneg hz₀ d) (pow_lt_one₀ hz₀ hz₁ hd.ne')
  simpa only [mul_one] using hasSum_degreeGeometric_reindex hd (fun _ ↦ 1) (by
    simpa only [mul_one, one_div] using hgeom)

/-- The first raw moment equals the mass times the normalized geometric mean. -/
theorem hasSum_degreeGeometric_first {d : ℕ} (hd : 0 < d) {z : ℝ} (hz₀ : 0 ≤ z) (hz₁ : z < 1) :
    HasSum (fun n ↦ (PowerSeries.coeff (R := ℕ) n (degreeGeometricSeries d) : ℝ) * z ^ n * (n : ℝ))
      ((1 / (1 - z ^ d)) * ((d : ℝ) * z ^ d / (1 - z ^ d))) := by
  have hnorm := norm_degree_ratio_lt_one hd hz₀ hz₁
  have hs := (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).mul_left (d : ℝ)
  apply hasSum_degreeGeometric_reindex hd (fun n ↦ (n : ℝ))
  have hterm (k : ℕ) :
      (z ^ d) ^ k * ((d * k : ℕ) : ℝ) = (d : ℝ) * ((k : ℝ) * (z ^ d) ^ k) := by
    push_cast
    ring
  have hval : ((1 / (1 - z ^ d)) * ((d : ℝ) * z ^ d / (1 - z ^ d))) =
      (d : ℝ) * (z ^ d / (1 - z ^ d) ^ 2) := by
    have hden : 1 - z ^ d ≠ 0 := (sub_pos.mpr (pow_lt_one₀ hz₀ hz₁ hd.ne')).ne'
    field_simp
  simp_rw [hterm, hval]
  exact hs

/-- The second raw moment equals the mass times the geometric variance plus the
square of the mean. -/
theorem hasSum_degreeGeometric_second {d : ℕ} (hd : 0 < d) {z : ℝ} (hz₀ : 0 ≤ z) (hz₁ : z < 1) :
    HasSum (fun n ↦ (PowerSeries.coeff (R := ℕ) n (degreeGeometricSeries d) : ℝ) * z ^ n * (n : ℝ) ^ 2)
      ((1 / (1 - z ^ d)) *
        ((d : ℝ) ^ 2 * z ^ d / (1 - z ^ d) ^ 2 + ((d : ℝ) * z ^ d / (1 - z ^ d)) ^ 2)) := by
  have hr₁ := pow_lt_one₀ hz₀ hz₁ hd.ne'
  have hs := (hasSum_sq_mul_geometric (pow_nonneg hz₀ d) hr₁).mul_left ((d : ℝ) ^ 2)
  apply hasSum_degreeGeometric_reindex hd (fun n ↦ (n : ℝ) ^ 2)
  have hterm (k : ℕ) : (z ^ d) ^ k * ((d * k : ℕ) : ℝ) ^ 2 =
      (d : ℝ) ^ 2 * ((k : ℝ) ^ 2 * (z ^ d) ^ k) := by
    push_cast
    ring
  have hval : (1 / (1 - z ^ d)) *
      ((d : ℝ) ^ 2 * z ^ d / (1 - z ^ d) ^ 2 + ((d : ℝ) * z ^ d / (1 - z ^ d)) ^ 2) =
        (d : ℝ) ^ 2 * (z ^ d * (1 + z ^ d) / (1 - z ^ d) ^ 3) := by
    have hden : 1 - z ^ d ≠ 0 := (sub_pos.mpr hr₁).ne'
    field_simp
  simp_rw [hterm, hval]
  exact hs

end GRHArticle.ProgressionFree
