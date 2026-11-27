import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Logarithmic averages of convergent sequences

The harmonic weights arise from summation by parts for norm counts.
The limit argument works for arbitrary convergent real sequences.
-/

namespace GRHArticle.ProgressionFree

open Finset Filter Topology Asymptotics

private noncomputable def logWeight (n : ℕ) : ℝ := 1/((n:ℝ)+2)

private theorem logWeight_bounds {N : ℕ} (hN : 0 < N) :
    Real.log N - 1 ≤ ∑ k ∈ range N, logWeight k ∧
      (∑ k ∈ range N, logWeight k) ≤ Real.log N + 1 := by
  have hshift : (∑ k ∈ range N, logWeight k) + 1 = (harmonic (N+1) : ℝ) := by
    rw [harmonic, Rat.cast_sum, sum_range_succ']
    simp [logWeight, one_div, Nat.cast_add, add_assoc]
  rw [harmonic_succ, Rat.cast_add, Rat.cast_inv, Rat.cast_natCast] at hshift
  have hl : Real.log N ≤ (harmonic N : ℝ) :=
    (Real.log_le_log (Nat.cast_pos.mpr hN) (Nat.cast_le.mpr (Nat.le_succ N))).trans (log_add_one_le_harmonic N)
  have hu := harmonic_le_one_add_log N
  have hp : 0 ≤ (((N+1 : ℕ):ℝ))⁻¹ := by positivity
  have h₁ : (((N+1 : ℕ):ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N))
  constructor <;> linarith

private theorem log_nat_atTop : Tendsto (fun N : ℕ ↦ Real.log N) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

private theorem logWeight_sum_ratio :
    Tendsto (fun N : ℕ ↦ (∑ k ∈ range N, logWeight k) / Real.log N) atTop (𝓝 1) := by
  have hz := log_nat_atTop.const_div_atTop 1
  have hl := (tendsto_const_nhds (x := (1:ℝ))).sub hz
  have hu := (tendsto_const_nhds (x := (1:ℝ))).add hz
  rw [sub_zero] at hl
  rw [add_zero] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu
  · filter_upwards [eventually_gt_atTop 1] with N hN
    have hp : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
    rw [le_div_iff₀ hp, sub_mul, one_mul, div_mul_cancel₀ _ hp.ne']
    exact (logWeight_bounds (by omega)).1
  · filter_upwards [eventually_gt_atTop 1] with N hN
    have hp : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
    rw [div_le_iff₀ hp, add_mul, one_mul, div_mul_cancel₀ _ hp.ne']
    exact (logWeight_bounds (by omega)).2

/-- Logarithmic averaging preserves an ordinary sequence limit. -/
theorem tendsto_logarithmicAverage_of_tendsto {g : ℕ → ℝ} {d : ℝ} (hg : Tendsto g atTop (𝓝 d)) :
    Tendsto (fun N : ℕ ↦ (∑ k ∈ range N, g k / ((k : ℝ)+2)) / Real.log N) atTop (𝓝 d) := by
  let f (k : ℕ) := g k - d
  have hf : Tendsto f atTop (𝓝 0) := tendsto_sub_nhds_zero_iff.mpr hg
  have hsumdiv : Tendsto (fun N ↦ ∑ k ∈ range N, logWeight k) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ (tendsto_atTop_add_const_right atTop (-1:ℝ) log_nat_atTop)
    filter_upwards [eventually_gt_atTop 0] with N hN using (logWeight_bounds hN).1
  have ho : (fun k ↦ f k * logWeight k) =o[atTop] logWeight := by
    simpa only [one_mul] using ((isLittleO_one_iff ℝ).mpr hf).mul_isBigO (isBigO_refl logWeight atTop)
  have hs := ho.sum_range (fun k ↦ by unfold logWeight; positivity) hsumdiv
  have heq := (isEquivalent_iff_tendsto_one (log_nat_atTop.eventually_ne_atTop 0)).mpr logWeight_sum_ratio
  have hrem := (hs.trans_isBigO heq.isBigO).tendsto_div_nhds_zero
  have h := hrem.add (logWeight_sum_ratio.const_mul d)
  rw [mul_one, zero_add] at h
  refine h.congr fun N ↦ ?_
  have hsplit : (∑ k ∈ range N, f k * logWeight k) =
      (∑ k ∈ range N, g k * logWeight k) - d * ∑ k ∈ range N, logWeight k := by
    simp only [f, sub_mul, sum_sub_distrib, mul_sum]
  rw [hsplit, sub_div, mul_div_assoc, sub_add_cancel]
  simp only [logWeight, mul_one_div]

end GRHArticle.ProgressionFree
