import FabiusFunction.KappaZeroInMeasure

/-!
# Tightness at the CLT scale

The cheap half of the audits' fluctuation theorem: at the natural
`√n` normalization the shell-product logarithm is **tight**,
uniformly in `n`:

`vol {t ∈ (0,1] : K·√n ≤ |log |Pₙ(t)||} ≤ π²/(4K²)`,

by Chebyshev against the exact variance
`∫ log²|Pₙ| = (π²/4)n − (π²/3)(1−2⁻ⁿ)`.  The full CLT
(`log|Pₙ|/√n ⇒ N(0, π²/4)`) needs the martingale central limit
theorem, absent from Mathlib; tightness is its unconditional shadow.

* `measureReal_log_prod_sqrt_ge_le` — **uniform tightness**.
-/

set_option autoImplicit false

open Filter Topology intervalIntegral Real MeasureTheory Set

namespace Fabius

/-- **Tightness at the `√n` scale**: uniformly in `n ≥ 1`,
`vol {t : K√n ≤ |log |Pₙ||} ≤ π²/(4K²)`. -/
theorem measureReal_log_prod_sqrt_ge_le {K : ℝ} (hK : 0 < K) {n : ℕ}
    (hn : 1 ≤ n) :
    (MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) 1)).real
      {t : ℝ | K * Real.sqrt n ≤ abs (Real.log |∏ k ∈ Finset.range n,
        (2 * Real.sin (π * (2 ^ k * t)))|)} ≤
      π ^ 2 / (4 * K ^ 2) := by
  have hn0 : (0:ℝ) < (n:ℝ) := by
    have h1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    linarith
  have hs0 : (0:ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hKs : (0:ℝ) < K * Real.sqrt n := mul_pos hK hs0
  have hεn : (0:ℝ) < (K * Real.sqrt n) ^ 2 := pow_pos hKs 2
  have hcheb := MeasureTheory.mul_meas_ge_le_integral_of_nonneg
    (μ := MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) 1))
    (f := fun t => Real.log |∏ k ∈ Finset.range n,
      (2 * Real.sin (π * (2 ^ k * t)))| ^ 2)
    (Filter.Eventually.of_forall (fun t => sq_nonneg _))
    (integrableOn_sq_log_prod n hn) ((K * Real.sqrt n) ^ 2)
  have hset : {t : ℝ | (K * Real.sqrt n) ^ 2 ≤
      Real.log |∏ k ∈ Finset.range n,
        (2 * Real.sin (π * (2 ^ k * t)))| ^ 2} =
      {t : ℝ | K * Real.sqrt n ≤ abs (Real.log |∏ k ∈
        Finset.range n, (2 * Real.sin (π * (2 ^ k * t)))|)} := by
    ext t
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h
      by_contra hc
      push Not at hc
      have hsq := pow_lt_pow_left₀ hc (abs_nonneg _) two_ne_zero
      rw [sq_abs] at hsq
      linarith
    · intro h
      have hsq := pow_le_pow_left₀ hKs.le h 2
      rw [sq_abs] at hsq
      exact hsq
  rw [hset] at hcheb
  have hval : ∫ t in Set.Ioc (0:ℝ) 1, Real.log |∏ k ∈ Finset.range n,
      (2 * Real.sin (π * (2 ^ k * t)))| ^ 2 ∂MeasureTheory.volume =
      π ^ 2 / 4 * n - π ^ 2 / 3 * (1 - (1 / 2) ^ n) := by
    have h := integral_sq_log_prod_two_sin n hn
    rwa [intervalIntegral.integral_of_le
      (by norm_num : (0:ℝ) ≤ 1)] at h
  rw [hval] at hcheb
  have hVle : π ^ 2 / 4 * (n:ℝ) - π ^ 2 / 3 * (1 - (1/2) ^ n) ≤
      π ^ 2 / 4 * n := by
    have h1 : (0:ℝ) ≤ 1 - (1/2:ℝ) ^ n := by
      have h := pow_le_one₀ (by norm_num : (0:ℝ) ≤ 1/2)
        (by norm_num : (1/2:ℝ) ≤ 1) (n := n)
      linarith
    have h2 : (0:ℝ) ≤ π ^ 2 / 3 * (1 - (1/2) ^ n) :=
      mul_nonneg (by positivity) h1
    linarith
  have hlevel : (K * Real.sqrt n) ^ 2 = K ^ 2 * n := by
    rw [mul_pow, Real.sq_sqrt hn0.le]
  rw [hlevel] at hcheb
  -- from `K²n · m ≤ (π²/4)n`, divide by `K²n`
  have hK2n : (0:ℝ) < K ^ 2 * n := by positivity
  rw [show π ^ 2 / (4 * K ^ 2) = (π ^ 2 / 4 * n) / (K ^ 2 * n) by
    field_simp]
  rw [le_div_iff₀ hK2n]
  linarith [hcheb, hVle]

end Fabius
