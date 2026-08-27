import FabiusFunction.BirkhoffProductBridge

/-!
# `κ₀ = 1` in measure

The audits' typical-point law in its weak (in-measure) form, obtained
from the exact variance by Chebyshev: for every `ε > 0`,

`vol {t ∈ (0,1] : |log |Pₙ(t)|| ≥ ε·n} ≤ (π²/4 ε²)·(1/n) → 0`,

where `Pₙ(t) = ∏_{k<n} 2 sin(π 2ᵏ t)`.  Equivalently
`|Pₙ|^{1/n} → 1` in measure — the dyadic shell products grow
subexponentially at typical points, the content of the audits'
`κ₀ = 1` claim that survives without the pointwise ergodic theorem
(absent from Mathlib).

* `intervalIntegrable_sq_birkhoff_sum`, `integrableOn_sq_log_prod` —
  the integrability inputs.
* `measureReal_log_prod_ge_le` — the quantitative Chebyshev bound.
* `tendsto_measureReal_log_prod_ge` — **`κ₀ = 1` in measure**.
-/

set_option autoImplicit false

open Filter Topology intervalIntegral Real MeasureTheory Set

namespace Fabius

/-- The Birkhoff-sum square is interval integrable. -/
theorem intervalIntegrable_sq_birkhoff_sum (n : ℕ) :
    IntervalIntegrable (fun t => (∑ k ∈ Finset.range n,
      Real.log (2 * Real.sin (π * (doublingMap^[k] t)))) ^ 2)
      MeasureTheory.volume 0 1 := by
  have hPi := IntervalIntegrable.sum (Finset.range n)
    (fun j (_ : j ∈ Finset.range n) =>
      IntervalIntegrable.sum (Finset.range n)
        (fun k (_ : k ∈ Finset.range n) =>
          intervalIntegrable_cocycle_pair j k))
  have hEq : (∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n,
      fun t => Real.log (2 * Real.sin (π * (doublingMap^[j] t))) *
        Real.log (2 * Real.sin (π * (doublingMap^[k] t)))) =
      fun t => ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n,
        Real.log (2 * Real.sin (π * (doublingMap^[j] t))) *
          Real.log (2 * Real.sin (π * (doublingMap^[k] t))) := by
    funext t
    simp [Finset.sum_apply]
  rw [hEq] at hPi
  have h : IntervalIntegrable (fun t => ∑ j ∈ Finset.range n,
      ∑ k ∈ Finset.range n,
      Real.log (2 * Real.sin (π * (doublingMap^[j] t))) *
        Real.log (2 * Real.sin (π * (doublingMap^[k] t))))
      MeasureTheory.volume 0 1 := hPi
  have hfun : (fun t => (∑ k ∈ Finset.range n,
      Real.log (2 * Real.sin (π * (doublingMap^[k] t)))) ^ 2) =
      fun t => ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n,
        Real.log (2 * Real.sin (π * (doublingMap^[j] t))) *
          Real.log (2 * Real.sin (π * (doublingMap^[k] t))) := by
    funext t
    rw [sq, Finset.sum_mul_sum]
  rw [hfun]
  exact h

/-- The squared log of the shell product is integrable on `(0,1]`. -/
theorem integrableOn_sq_log_prod (n : ℕ) (hn : 1 ≤ n) :
    MeasureTheory.IntegrableOn (fun t =>
      Real.log |∏ k ∈ Finset.range n,
        (2 * Real.sin (π * (2 ^ k * t)))| ^ 2)
      (Set.Ioc (0:ℝ) 1) MeasureTheory.volume := by
  have h := intervalIntegrable_sq_birkhoff_sum n
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
    (by norm_num : (0:ℝ) ≤ 1)] at h
  apply MeasureTheory.Integrable.congr h
  have hae : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) 1)),
      ∀ k, k < n → Real.sin (π * (doublingMap^[k] t)) ≠ 0 :=
    MeasureTheory.ae_restrict_of_ae (ae_iterate_sin_ne_zero n)
  filter_upwards [hae,
    MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t hne hmem
  have ht1 : t < 1 := by
    rcases lt_or_eq_of_le hmem.2 with h' | rfl
    · exact h'
    · exfalso
      apply hne 0 hn
      rw [Function.iterate_zero_apply]
      simp [Real.sin_pi]
  have ht : t ∈ Set.Ico (0:ℝ) 1 := ⟨hmem.1.le, ht1⟩
  rw [log_abs_prod_two_sin n ht hne]

/-- **The quantitative Chebyshev bound**: for `n ≥ 1`,
`vol {t ∈ (0,1] : ε n ≤ |log |Pₙ||} ≤ (π²/4)·n / (ε n)²`. -/
theorem measureReal_log_prod_ge_le {ε : ℝ} (hε : 0 < ε) {n : ℕ}
    (hn : 1 ≤ n) :
    (MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) 1)).real
      {t : ℝ | ε * n ≤ abs (Real.log |∏ k ∈ Finset.range n,
        (2 * Real.sin (π * (2 ^ k * t)))|)} ≤
      (π ^ 2 / 4 * n) / (ε * n) ^ 2 := by
  have hn0 : (0:ℝ) < (n:ℝ) := by
    have h1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    linarith
  have hεn : (0:ℝ) < (ε * n) ^ 2 := pow_pos (mul_pos hε hn0) 2
  have hcheb := MeasureTheory.mul_meas_ge_le_integral_of_nonneg
    (μ := MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) 1))
    (f := fun t => Real.log |∏ k ∈ Finset.range n,
      (2 * Real.sin (π * (2 ^ k * t)))| ^ 2)
    (Filter.Eventually.of_forall (fun t => sq_nonneg _))
    (integrableOn_sq_log_prod n hn) ((ε * n) ^ 2)
  have hset : {t : ℝ | (ε * n) ^ 2 ≤ Real.log |∏ k ∈ Finset.range n,
      (2 * Real.sin (π * (2 ^ k * t)))| ^ 2} =
      {t : ℝ | ε * n ≤ abs (Real.log |∏ k ∈ Finset.range n,
        (2 * Real.sin (π * (2 ^ k * t)))|)} := by
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
      have hsq := pow_le_pow_left₀ (mul_nonneg hε.le hn0.le) h 2
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
  rw [le_div_iff₀ hεn]
  linarith [hcheb, hVle]

/-- **`κ₀ = 1` in measure** (the audits' typical-point law, weak
form): for every `ε > 0` the set where the shell product deviates
exponentially, `|log |Pₙ|| ≥ ε n`, has measure tending to `0` — the
dyadic sine products are subexponential in measure. -/
theorem tendsto_measureReal_log_prod_ge {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ =>
      (MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) 1)).real
        {t : ℝ | ε * n ≤ abs (Real.log |∏ k ∈ Finset.range n,
          (2 * Real.sin (π * (2 ^ k * t)))|)})
      atTop (𝓝 0) := by
  have h0 : ∀ᶠ n : ℕ in atTop, 0 ≤
      (MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) 1)).real
        {t : ℝ | ε * n ≤ abs (Real.log |∏ k ∈ Finset.range n,
          (2 * Real.sin (π * (2 ^ k * t)))|)} :=
    Filter.Eventually.of_forall (fun n => MeasureTheory.measureReal_nonneg)
  have hbound : ∀ᶠ n : ℕ in atTop,
      (MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) 1)).real
        {t : ℝ | ε * n ≤ abs (Real.log |∏ k ∈ Finset.range n,
          (2 * Real.sin (π * (2 ^ k * t)))|)} ≤
      (π ^ 2 / (4 * ε ^ 2)) / n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0:ℝ) < (n:ℝ) := by
      have h1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
      linarith
    have h := measureReal_log_prod_ge_le hε hn
    have heq : (π ^ 2 / 4 * (n:ℝ)) / (ε * n) ^ 2 =
        (π ^ 2 / (4 * ε ^ 2)) / n := by
      field_simp
    rwa [heq] at h
  exact squeeze_zero' h0 hbound
    (tendsto_const_div_atTop_nhds_zero_nat _)

end Fabius
