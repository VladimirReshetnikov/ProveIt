import FabiusFunction.BirkhoffVariance

/-!
# From Birkhoff sums to dyadic sine products

The bridge that lands the variance theorem on the audits' actual
object: since `2ᵏt` and `Tᵏt` differ by an integer,

`log |∏_{k<n} 2 sin (π 2ᵏ t)| = ∑_{k<n} ψ(Tᵏ t)`  (a.e.),

so the exact Birkhoff variance computes the `L²` mass of the log of
the **normalized dyadic sine product** — the shell factor of the
Rvachev Fourier transform:

`∫₀¹ log² |∏_{k<n} 2 sin (π 2ᵏ t)| dt = (π²/4)n − (π²/3)(1 − 2⁻ⁿ)`.

* `exists_int_iterate_doublingMap` — `Tᵏt = 2ᵏt − m`, `m ∈ ℤ`.
* `abs_sin_two_pow_eq` — `|sin (π 2ᵏ t)| = |sin (π Tᵏ t)|`.
* `log_abs_prod_two_sin_global` — the absolute-value logarithmic bridge at
  every real seed off the finite zero set, with no fundamental-domain
  hypothesis.
* `log_abs_prod_two_sin` — the pointwise bridge.
* `ae_iterate_sin_ne_zero` — the zero set is null.
* `integral_sq_log_prod_two_sin` — **the variance of the actual
  product**.
* `integral_sq_log_prod_two_sin_all` — the same exact variance for every
  natural product length, including the empty product.
-/

set_option autoImplicit false

open Filter Topology intervalIntegral Real MeasureTheory Set

namespace Fabius

/-- The iterated doubling map differs from plain doubling by an
integer: `Tᵏt = 2ᵏt − m` for some `m ∈ ℤ`. -/
theorem exists_int_iterate_doublingMap (k : ℕ) (t : ℝ) :
    ∃ m : ℤ, (doublingMap^[k]) t = 2 ^ k * t - m := by
  induction k generalizing t with
  | zero =>
      exact ⟨0, by simp⟩
  | succ k ih =>
      obtain ⟨m', hm'⟩ := ih (doublingMap t)
      refine ⟨2 ^ k * ⌊2 * t⌋ + m', ?_⟩
      rw [Function.iterate_succ_apply, hm']
      have hT : doublingMap t = 2 * t - ⌊2 * t⌋ := rfl
      rw [hT]
      push_cast
      ring

/-- `|sin (π 2ᵏ t)| = |sin (π Tᵏ t)|`. -/
theorem abs_sin_two_pow_eq (k : ℕ) (t : ℝ) :
    |Real.sin (π * (2 ^ k * t))| =
      |Real.sin (π * (doublingMap^[k] t))| := by
  obtain ⟨m, hm⟩ := exists_int_iterate_doublingMap k t
  have harg : π * (2 ^ k * t) = π * (doublingMap^[k] t) + m * π := by
    rw [hm]
    push_cast
    ring
  rw [harg, Real.sin_add_int_mul_pi, abs_mul]
  have hone : |((-1:ℝ)) ^ m| = 1 := by
    rw [abs_zpow, abs_neg, abs_one, one_zpow]
  rw [hone, one_mul]

/-- The iterates stay in `[0,1)` once the seed is there. -/
theorem iterate_doublingMap_mem {t : ℝ} (ht : t ∈ Set.Ico (0:ℝ) 1)
    (k : ℕ) : (doublingMap^[k]) t ∈ Set.Ico (0:ℝ) 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using ht
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    rw [Function.iterate_succ_apply']
    exact ⟨doublingMap_nonneg _, doublingMap_lt_one _⟩

/-- Global absolute-value form of the product/Birkhoff bridge.  It holds at
every real seed off the finite zero set: reducing `2ᵏt` modulo integers
changes the sine only by a sign, which disappears inside the absolute value.
-/
theorem log_abs_prod_two_sin_global (n : ℕ) {t : ℝ}
    (hne : ∀ k, k < n → Real.sin (π * (doublingMap^[k] t)) ≠ 0) :
    Real.log |∏ k ∈ Finset.range n,
      (2 * Real.sin (π * (2 ^ k * t)))| =
      ∑ k ∈ Finset.range n,
        Real.log |2 * Real.sin (π * (doublingMap^[k] t))| := by
  rw [Finset.abs_prod]
  have hprod : ∏ k ∈ Finset.range n,
      |2 * Real.sin (π * (2 ^ k * t))| =
      ∏ k ∈ Finset.range n,
        |2 * Real.sin (π * (doublingMap^[k] t))| :=
    Finset.prod_congr rfl (fun k _ => by
      rw [abs_mul, abs_mul, abs_sin_two_pow_eq k t])
  rw [hprod]
  exact Real.log_prod (fun k hk => by
    rw [abs_ne_zero]
    exact mul_ne_zero (by norm_num) (hne k (Finset.mem_range.mp hk)))

/-- **The pointwise bridge**: off the zero set,
`log |∏_{k<n} 2 sin (π 2ᵏ t)| = ∑_{k<n} ψ(Tᵏ t)`. -/
theorem log_abs_prod_two_sin (n : ℕ) {t : ℝ}
    (ht : t ∈ Set.Ico (0:ℝ) 1)
    (hne : ∀ k, k < n → Real.sin (π * (doublingMap^[k] t)) ≠ 0) :
    Real.log |∏ k ∈ Finset.range n,
      (2 * Real.sin (π * (2 ^ k * t)))| =
      ∑ k ∈ Finset.range n,
        Real.log (2 * Real.sin (π * (doublingMap^[k] t))) := by
  have hpos : ∀ k, k < n → 0 < Real.sin (π * (doublingMap^[k] t)) := by
    intro k hk
    have hmem := iterate_doublingMap_mem ht k
    have h0 : 0 ≤ Real.sin (π * (doublingMap^[k] t)) := by
      apply Real.sin_nonneg_of_nonneg_of_le_pi
      · have := hmem.1
        positivity
      · nlinarith [Real.pi_pos, hmem.2]
    exact lt_of_le_of_ne h0 (Ne.symm (hne k hk))
  rw [log_abs_prod_two_sin_global n hne]
  exact Finset.sum_congr rfl (fun k hk => by
    rw [abs_of_pos (mul_pos two_pos (hpos k (Finset.mem_range.mp hk)))])

/-- The set where some factor vanishes is null. -/
theorem ae_iterate_sin_ne_zero (n : ℕ) :
    ∀ᵐ t : ℝ, ∀ k, k < n →
      Real.sin (π * (doublingMap^[k] t)) ≠ 0 := by
  rw [MeasureTheory.ae_all_iff]
  intro k
  by_cases hk : k < n
  · have hcount : {t : ℝ | Real.sin (π * (2 ^ k * t)) = 0}.Countable := by
      apply Set.Countable.mono ?_ (Set.countable_range
        (fun m : ℤ => (m : ℝ) / 2 ^ k))
      intro t htmem
      obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.mp htmem
      refine ⟨m, ?_⟩
      have hm' : (m:ℝ) * π = (2 ^ k * t) * π := by linear_combination hm
      have hmt := mul_right_cancel₀ Real.pi_ne_zero hm'
      show (m : ℝ) / 2 ^ k = t
      rw [hmt]
      field_simp
    have hnull := hcount.measure_zero MeasureTheory.volume
    have hae : ∀ᵐ t : ℝ, Real.sin (π * (2 ^ k * t)) ≠ 0 := by
      rw [MeasureTheory.ae_iff]
      simpa using hnull
    filter_upwards [hae] with t ht
    intro _ h0
    apply ht
    have habs := abs_sin_two_pow_eq k t
    rw [h0, abs_zero] at habs
    exact abs_eq_zero.mp habs
  · exact Filter.Eventually.of_forall (fun t hkn => absurd hkn hk)

/-- **The variance of the actual dyadic sine product**:

`∫₀¹ log² |∏_{k<n} 2 sin (π 2ᵏ t)| dt = (π²/4)·n − (π²/3)·(1 − 2⁻ⁿ)` —

the audits' `thm:variance` stated on the normalized shell product of
the Rvachev Fourier transform itself. -/
theorem integral_sq_log_prod_two_sin (n : ℕ) (hn : 1 ≤ n) :
    ∫ t in (0:ℝ)..1, Real.log |∏ k ∈ Finset.range n,
      (2 * Real.sin (π * (2 ^ k * t)))| ^ 2 =
      π ^ 2 / 4 * n - π ^ 2 / 3 * (1 - (1 / 2) ^ n) := by
  have hcongr : ∫ t in (0:ℝ)..1, Real.log |∏ k ∈ Finset.range n,
      (2 * Real.sin (π * (2 ^ k * t)))| ^ 2 =
      ∫ t in (0:ℝ)..1, (∑ k ∈ Finset.range n,
        Real.log (2 * Real.sin (π * (doublingMap^[k] t)))) ^ 2 := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [ae_iterate_sin_ne_zero n] with t hne hmem
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hmem
    have ht1 : t < 1 := by
      rcases lt_or_eq_of_le hmem.2 with h | rfl
      · exact h
      · exfalso
        apply hne 0 hn
        rw [Function.iterate_zero_apply]
        simp [Real.sin_pi]
    have ht : t ∈ Set.Ico (0:ℝ) 1 := ⟨hmem.1.le, ht1⟩
    rw [log_abs_prod_two_sin n ht hne]
  rw [hcongr]
  exact integral_sq_birkhoff_sum n hn

/-- Exact log-product variance for every natural product length.  For
`n = 0` the normalized product is the empty product `1`, so its logarithmic
square and the closed form both vanish. -/
theorem integral_sq_log_prod_two_sin_all (n : ℕ) :
    ∫ t in (0:ℝ)..1, Real.log |∏ k ∈ Finset.range n,
      (2 * Real.sin (π * (2 ^ k * t)))| ^ 2 =
      π ^ 2 / 4 * n - π ^ 2 / 3 * (1 - (1 / 2) ^ n) := by
  cases n with
  | zero => norm_num
  | succ n => exact integral_sq_log_prod_two_sin (n + 1) (by omega)

end Fabius
