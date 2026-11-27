import GRHArticle.ProgressionFree.NumberFieldIdeals.PrimeIdealDensity
import GRHArticle.ProgressionFree.NumberFieldIdeals.IdealSeparationBound

/-!
# Upper and natural density separate in every number field

The finite coprimality factor decays more slowly than every fixed negative
power of the norm cutoff. This follows from the sublogarithmic reciprocal
mass of prime ideals. Hence the explicit smooth obstruction eventually
outweighs the inverse-cutoff Euler tail.
-/

namespace GRHArticle.ProgressionFree.NumberFieldIdeals

open NumberField Ideal IsDedekindDomain Finset Filter Topology

variable {K : Type*} [Field K] [NumberField K]

private theorem neg_log_local_le (p : HeightOneSpectrum (𝓞 K)) :
    -Real.log (1-primeWeight p) ≤ 2 * primeWeight p := by
  obtain ⟨hw,hw'⟩ := primeWeight_pos_lt_one p
  have hn : 2 ≤ absNorm p.asIdeal := by
    have hpos := absNorm_pos_of_nonZeroDivisors (primeIdeal p)
    have hne : absNorm p.asIdeal ≠ 1 := fun h ↦ p.isMaximal.ne_top (absNorm_eq_one_iff.mp h)
    change 0 < absNorm p.asIdeal at hpos
    omega
  have hhalf : primeWeight p ≤ 1/2 := by
    rw [primeWeight, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hn)
  have hp := sub_pos.mpr hw'
  rw [← Real.log_inv]
  apply (Real.log_le_sub_one_of_pos (inv_pos.mpr hp)).trans
  apply (sub_le_iff_le_add).mpr
  rw [← one_div, div_le_iff₀ hp]
  nlinarith [mul_nonneg hw.le (by linarith : 0 ≤ 1-2*primeWeight p)]

/-- The logarithm of the inverse local coprimality factor is at most
twice the reciprocal mass of the selected prime ideals. -/
theorem neg_log_idealSmoothDensityFactor_le (S : Finset (HeightOneSpectrum (𝓞 K))) :
    -Real.log (idealSmoothDensityFactor S) ≤ 2 * ∑ p ∈ S, primeWeight p := by
  rw [idealSmoothDensityFactor, Real.log_prod (fun p _ ↦ (sub_pos.mpr (primeWeight_pos_lt_one p).2).ne'),
    ← sum_neg_distrib, mul_sum]
  exact sum_le_sum fun p _ ↦ neg_log_local_le p

/-- The product over the primes through `Y` decays more slowly than
`Y^(-a)` for every positive exponent `a`. -/
theorem tendsto_rpow_mul_idealSmoothDensityFactor {a : ℝ} (ha : 0 < a) :
    Tendsto (fun Y : ℕ ↦ (Y:ℝ)^a * idealSmoothDensityFactor (primesThroughNorm K Y)) atTop atTop := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hsmall := (tendsto_sum_primeWeight_div_log (K := K)).eventually_lt_const (show 0 < a/4 by positivity)
  have hg : Tendsto (fun Y : ℕ ↦ a * Real.log Y + Real.log (idealSmoothDensityFactor (primesThroughNorm K Y)))
      atTop atTop := by
    apply tendsto_atTop_mono' atTop _ (hlog.const_mul_atTop (half_pos ha))
    filter_upwards [hsmall,eventually_gt_atTop 1] with Y hY hY'
    have hl : 0 < Real.log Y := Real.log_pos (by exact_mod_cast hY')
    have h := (div_lt_iff₀ hl).mp hY
    change a/2 * Real.log Y ≤ a * Real.log Y + Real.log (idealSmoothDensityFactor (primesThroughNorm K Y))
    nlinarith only [h, neg_log_idealSmoothDensityFactor_le (primesThroughNorm K Y)]
  refine (Real.tendsto_exp_atTop.comp hg).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with Y hY
  simp only [Function.comp_apply, Real.exp_add, Real.exp_log (idealSmoothDensityFactor_pos _),
    Real.rpow_def_of_pos (Nat.cast_pos.mpr hY)]
  rw [mul_comm a]

/-- At every sufficiently large cutoff the explicit right-hand side
of the density gap is already strictly positive. -/
theorem eventually_idealDensitySeparationBound_pos (p : HeightOneSpectrum (𝓞 K)) :
    ∀ᶠ Y : ℕ in atTop, 0 < idealSmoothDensityFactor (primesThroughNorm K Y) /
      ((absNorm p.asIdeal : ℝ)^8 * ((absNorm p.asIdeal : ℝ)^8 + 1)) - (Module.finrank ℚ K : ℝ)/Y := by
  let m := (absNorm p.asIdeal : ℝ)^8 * ((absNorm p.asIdeal : ℝ)^8+1)
  have hn : (0:ℝ) < absNorm p.asIdeal := Nat.cast_pos.mpr (absNorm_pos_of_nonZeroDivisors (primeIdeal p))
  have hm : 0 < m := by dsimp [m]; positivity
  have ht := (tendsto_rpow_mul_idealSmoothDensityFactor (K := K) (by norm_num : (0:ℝ)<1)).eventually
    (Ioi_mem_atTop ((Module.finrank ℚ K : ℝ)*m))
  filter_upwards [ht,eventually_gt_atTop 0] with Y hY hpos
  change (Module.finrank ℚ K : ℝ)*m < (Y:ℝ)^(1:ℝ) * idealSmoothDensityFactor _ at hY
  rw [Real.rpow_one, mul_comm (Y:ℝ)] at hY
  exact sub_pos.mpr ((div_lt_div_iff₀ (Nat.cast_pos.mpr hpos) hm).mpr hY)

/-- The strict natural/upper density separation in `gpi:thm:ideal-separation`,
for every number field and either ratio convention. -/
theorem idealNaturalDensitySupremum_lt_upper (integral : Bool) :
    idealNaturalDensitySupremum K integral < idealUpperDensitySupremum K integral := by
  obtain ⟨P,hP,_,_⟩ := exists_isMaximal_dvd_of_dvd_absNorm' Nat.prime_two (⊥ : Ideal (𝓞 K)) (by simp)
  letI : P.IsMaximal := hP
  let p : HeightOneSpectrum (𝓞 K) := ⟨P,hP.isPrime,Ideal.IsMaximal.ne_bot_of_isIntegral_int P⟩
  obtain ⟨Y,hpos,hY⟩ := ((eventually_idealDensitySeparationBound_pos p).and (eventually_ge_atTop (absNorm p.asIdeal))).exists
  exact sub_pos.mp (hpos.trans_le (idealDensitySeparation_normCutoff integral p Y hY))

end GRHArticle.ProgressionFree.NumberFieldIdeals
