import FabiusFunction.KappaZeroInMeasure
import FabiusFunction.BirkhoffMoments

/-!
# First moments of the shell-product logarithm

The audits' fluctuation-scale bookkeeping for
`Pₙ(t) = ∏_{k<n} 2 sin(π 2ᵏ t)`:

`∫₀¹ log |Pₙ| = 0`  (exact centering), and
`∫₀¹ |log |Pₙ|| ≤ (π/2)·√n`  (the `σ√n` deviation scale),

the latter by the quadratic Cauchy–Schwarz trick
`(∫|f|)² ≤ ∫ f²` on the unit interval against the exact variance.

* `intervalIntegrable_log_prod` — `log |Pₙ| ∈ L¹`.
* `integral_log_prod_two_sin` — **exact centering**.
* `sq_integral_abs_le` — the reusable Cauchy–Schwarz square trick.
* `integral_abs_log_prod_le` — **the `(π/2)√n` scale**.
-/

set_option autoImplicit false

open Filter Topology intervalIntegral Real MeasureTheory Set

namespace Fabius

/-- The Birkhoff sum is interval integrable. -/
theorem intervalIntegrable_birkhoff_sum (n : ℕ) :
    IntervalIntegrable (fun t => ∑ k ∈ Finset.range n,
      Real.log (2 * Real.sin (π * (doublingMap^[k] t))))
      MeasureTheory.volume 0 1 := by
  have hPi := IntervalIntegrable.sum (Finset.range n)
    (fun k (_ : k ∈ Finset.range n) =>
      intervalIntegrable_cocycle_iterate k)
  have hEq : (∑ k ∈ Finset.range n, fun t =>
      Real.log (2 * Real.sin (π * (doublingMap^[k] t)))) =
      fun t => ∑ k ∈ Finset.range n,
        Real.log (2 * Real.sin (π * (doublingMap^[k] t))) := by
    funext t
    simp [Finset.sum_apply]
  rw [hEq] at hPi
  exact hPi

/-- `log |Pₙ|` is interval integrable. -/
theorem intervalIntegrable_log_prod (n : ℕ) (hn : 1 ≤ n) :
    IntervalIntegrable (fun t => Real.log |∏ k ∈ Finset.range n,
      (2 * Real.sin (π * (2 ^ k * t)))|)
      MeasureTheory.volume 0 1 := by
  have h := intervalIntegrable_birkhoff_sum n
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
    (by norm_num : (0:ℝ) ≤ 1)] at h ⊢
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

/-- **Exact centering of the shell-product logarithm**:
`∫₀¹ log |Pₙ| = 0`. -/
theorem integral_log_prod_two_sin (n : ℕ) (hn : 1 ≤ n) :
    ∫ t in (0:ℝ)..1, Real.log |∏ k ∈ Finset.range n,
      (2 * Real.sin (π * (2 ^ k * t)))| = 0 := by
  have hcongr : ∫ t in (0:ℝ)..1, Real.log |∏ k ∈ Finset.range n,
      (2 * Real.sin (π * (2 ^ k * t)))| =
      ∫ t in (0:ℝ)..1, (∑ k ∈ Finset.range n,
        Real.log (2 * Real.sin (π * (doublingMap^[k] t)))) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [ae_iterate_sin_ne_zero n] with t hne hmem
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hmem
    have ht1 : t < 1 := by
      rcases lt_or_eq_of_le hmem.2 with h' | rfl
      · exact h'
      · exfalso
        apply hne 0 hn
        rw [Function.iterate_zero_apply]
        simp [Real.sin_pi]
    have ht : t ∈ Set.Ico (0:ℝ) 1 := ⟨hmem.1.le, ht1⟩
    rw [log_abs_prod_two_sin n ht hne]
  rw [hcongr]
  exact integral_birkhoff_sum n

/-- **The Cauchy–Schwarz square trick on `[0,1]`**:
`(∫₀¹ |f|)² ≤ ∫₀¹ f²`. -/
theorem sq_integral_abs_le {f : ℝ → ℝ}
    (hf : IntervalIntegrable f MeasureTheory.volume 0 1)
    (hsq : IntervalIntegrable (fun t => f t ^ 2)
      MeasureTheory.volume 0 1) :
    (∫ t in (0:ℝ)..1, |f t|) ^ 2 ≤ ∫ t in (0:ℝ)..1, f t ^ 2 := by
  set c : ℝ := ∫ t in (0:ℝ)..1, |f t| with hc
  have habs : IntervalIntegrable (fun t => |f t|)
      MeasureTheory.volume 0 1 := hf.abs
  have h0 : 0 ≤ ∫ t in (0:ℝ)..1, (|f t| - c) ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num)
      (fun u _ => sq_nonneg _)
  have hpt : ∀ t : ℝ, (|f t| - c) ^ 2 =
      f t ^ 2 - 2 * c * |f t| + c ^ 2 := by
    intro t
    rw [sub_sq, sq_abs]
    ring
  have hExp : ∫ t in (0:ℝ)..1, (|f t| - c) ^ 2 =
      (∫ t in (0:ℝ)..1, f t ^ 2) - c ^ 2 := by
    rw [intervalIntegral.integral_congr
      (g := fun t => f t ^ 2 - 2 * c * |f t| + c ^ 2)
      (fun t _ => hpt t)]
    rw [intervalIntegral.integral_add
      ((hsq.sub (habs.const_mul (2 * c))))
      (intervalIntegrable_const (c := c ^ 2)),
      intervalIntegral.integral_sub hsq (habs.const_mul (2 * c)),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const]
    rw [← hc]
    ring
  linarith [hExp ▸ h0]

/-- **The `σ√n` deviation scale**: `∫₀¹ |log |Pₙ|| ≤ (π/2)·√n`. -/
theorem integral_abs_log_prod_le (n : ℕ) (hn : 1 ≤ n) :
    ∫ t in (0:ℝ)..1, abs (Real.log |∏ k ∈ Finset.range n,
      (2 * Real.sin (π * (2 ^ k * t)))|) ≤
      π / 2 * Real.sqrt n := by
  have hCS := sq_integral_abs_le (intervalIntegrable_log_prod n hn)
    (by
      have h := intervalIntegrable_sq_birkhoff_sum n
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
        (by norm_num : (0:ℝ) ≤ 1)] at h ⊢
      apply MeasureTheory.Integrable.congr h
      have hae : ∀ᵐ t ∂(MeasureTheory.volume.restrict
          (Set.Ioc (0:ℝ) 1)),
          ∀ k, k < n → Real.sin (π * (doublingMap^[k] t)) ≠ 0 :=
        MeasureTheory.ae_restrict_of_ae (ae_iterate_sin_ne_zero n)
      filter_upwards [hae,
        MeasureTheory.ae_restrict_mem measurableSet_Ioc]
        with t hne hmem
      have ht1 : t < 1 := by
        rcases lt_or_eq_of_le hmem.2 with h' | rfl
        · exact h'
        · exfalso
          apply hne 0 hn
          rw [Function.iterate_zero_apply]
          simp [Real.sin_pi]
      have ht : t ∈ Set.Ico (0:ℝ) 1 := ⟨hmem.1.le, ht1⟩
      rw [log_abs_prod_two_sin n ht hne])
  have hVar := integral_sq_log_prod_two_sin n hn
  rw [hVar] at hCS
  have hVle : π ^ 2 / 4 * (n:ℝ) - π ^ 2 / 3 * (1 - (1/2) ^ n) ≤
      π ^ 2 / 4 * n := by
    have h1 : (0:ℝ) ≤ 1 - (1/2:ℝ) ^ n := by
      have h := pow_le_one₀ (by norm_num : (0:ℝ) ≤ 1/2)
        (by norm_num : (1/2:ℝ) ≤ 1) (n := n)
      linarith
    have h2 : (0:ℝ) ≤ π ^ 2 / 3 * (1 - (1/2) ^ n) :=
      mul_nonneg (by positivity) h1
    linarith
  have hc0 : 0 ≤ ∫ t in (0:ℝ)..1, abs (Real.log |∏ k ∈
      Finset.range n, (2 * Real.sin (π * (2 ^ k * t)))|) :=
    intervalIntegral.integral_nonneg (by norm_num)
      (fun u _ => abs_nonneg _)
  have hcB : (∫ t in (0:ℝ)..1, abs (Real.log |∏ k ∈ Finset.range n,
      (2 * Real.sin (π * (2 ^ k * t)))|)) ^ 2 ≤
      π ^ 2 / 4 * n := le_trans hCS hVle
  have h1 : Real.sqrt ((∫ t in (0:ℝ)..1, abs (Real.log |∏ k ∈
      Finset.range n, (2 * Real.sin (π * (2 ^ k * t)))|)) ^ 2) ≤
      Real.sqrt (π ^ 2 / 4 * n) := Real.sqrt_le_sqrt hcB
  rw [Real.sqrt_sq hc0] at h1
  have h2 : Real.sqrt (π ^ 2 / 4 * n) = π / 2 * Real.sqrt n := by
    rw [show π ^ 2 / 4 = (π / 2) ^ 2 by ring,
      Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq (by positivity : (0:ℝ) ≤ π / 2)]
  rwa [h2] at h1

end Fabius
