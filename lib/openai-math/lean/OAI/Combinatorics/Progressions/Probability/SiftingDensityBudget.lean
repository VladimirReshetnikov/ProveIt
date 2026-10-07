import OAI.Combinatorics.Progressions.Estimates.ComplexFiniteMeans

namespace OAI

section

namespace Erdos3.LocalConvolution

theorem exists_moment_separation {alpha threshold epsilon : ℝ}
    (halpha : 0 < alpha) (hthreshold : 0 ≤ threshold) (hgap : threshold < alpha)
    (hepsilon : 0 < epsilon) :
    ∃ q₀ : ℕ, ∀ q ≥ q₀, threshold ^ q ≤ epsilon / 2 * alpha ^ q := by
  have hr0 : 0 ≤ threshold / alpha := div_nonneg hthreshold halpha.le
  have hr1 : threshold / alpha < 1 := (div_lt_one halpha).mpr hgap
  obtain ⟨q₀, hq₀⟩ := exists_pow_lt_of_lt_one (show 0 < epsilon / 2 by positivity) hr1
  refine ⟨q₀, ?_⟩
  intro q hq
  have h : (threshold / alpha) ^ q ≤ epsilon / 2 :=
    (pow_le_pow_of_le_one hr0 hr1.le hq).trans hq₀.le
  rw [div_pow] at h
  exact (div_le_iff₀ (pow_pos halpha q)).mp h

theorem sifting_density_ge_exp {M alpha p : ℝ} (hM : 0 < M) (halpha : 1 ≤ alpha)
    (hp : 1 ≤ p) (hcap : M ≤ Real.exp p) (q : ℕ) :
    Real.exp (-(3 * (q : ℝ) * p + 1)) ≤ (alpha / (2 * M ^ 2)) ^ q / 2 := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by nlinarith [Real.add_one_le_exp (1 : ℝ)]
  have htwoP : (2 : ℝ) ≤ Real.exp p := htwo.trans (Real.exp_le_exp.mpr hp)
  have hden : 2 * M ^ 2 ≤ Real.exp (3 * p) := by
    calc
      _ ≤ Real.exp p * (Real.exp p) ^ 2 :=
        mul_le_mul htwoP (pow_le_pow_left₀ hM.le hcap 2) (sq_nonneg M) (Real.exp_nonneg p)
      _ = _ := by
        rw [pow_two, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
  have hbase : Real.exp (-3 * p) ≤ alpha / (2 * M ^ 2) := by
    calc
      _ = 1 / Real.exp (3 * p) := by rw [one_div, ← Real.exp_neg]; congr 1; ring
      _ ≤ 1 / (2 * M ^ 2) := one_div_le_one_div_of_le (by positivity) hden
      _ ≤ _ := div_le_div_of_nonneg_right halpha (by positivity)
  have hhalf : Real.exp (-1 : ℝ) ≤ 1 / 2 := by
    simpa only [Real.exp_neg, one_div] using one_div_le_one_div_of_le (by norm_num) htwo
  have hpow : (Real.exp (-3 * p)) ^ q = Real.exp (-3 * (q : ℝ) * p) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  calc
    _ = (Real.exp (-3 * p)) ^ q * Real.exp (-1) := by
      rw [hpow, ← Real.exp_add]
      congr 1
      ring
    _ ≤ (alpha / (2 * M ^ 2)) ^ q * (1 / 2) :=
      mul_le_mul (pow_le_pow_left₀ (Real.exp_nonneg _) hbase q) hhalf
        (Real.exp_nonneg _) (pow_nonneg (div_nonneg (by linarith) (by positivity)) q)
    _ = _ := by ring

theorem sifting_density_ge_exp_quadratic {M alpha p C : ℝ}
    (hM : 0 < M) (halpha : 1 ≤ alpha) (hp : 1 ≤ p) (hcap : M ≤ Real.exp p)
    (q : ℕ) (hq : (q : ℝ) ≤ C * p) :
    Real.exp (-((3 * C + 1) * p ^ 2)) ≤ (alpha / (2 * M ^ 2)) ^ q / 2 := by
  have hp0 : 0 ≤ p := by linarith
  have hcost : 3 * (q : ℝ) * p + 1 ≤ (3 * C + 1) * p ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hq hp0]
  exact (Real.exp_le_exp.mpr (neg_le_neg hcost)).trans (sifting_density_ge_exp hM halpha hp hcap q)

end Erdos3.LocalConvolution

end

end OAI
