import FabiusFunction.LaplaceMomentBounds

/-!
# Sharper effective constants for the endpoint/Laplace comparison

`LaplaceMomentBounds` derives its third and fourth normalized moment bounds
`R₃(s) ≤ 384/s²`, `R₄(s) ≤ 6144/s³` from the square bound
`R_k(s)² ≤ s·((4/s)^k k!)²`, discarding a factor `√s` each time.  Keeping
it gives

`R₃(s) ≤ 384/(s²√s)`,  `R₄(s) ≤ 6144/(s³√s)`,

so the higher-moment transfer term is `O(n^{-3/2})`, not `O(1/n)`, and the
radius-`1/2` logarithm-chart hypothesis `|S| + H ≤ 1/2` closes from
`√n ≥ 73` instead of `n ≥ 224043`:

`|dyadicEndpointLaplaceLogError n + dyadicEndpointSecondOrder F n|
   ≤ 512/n + 208896/(n√n) ≤ 3374/n`   for `n ≥ 5329 = 73²`,

against `209408/n` for `n ≥ 224043` before.  The cumulant-form estimate
improves in the same way: `40537/(12n)` for `n ≥ 5329` instead of
`2512945/(12n)` for `n ≥ 224043`.  The statements of `LaplaceMomentBounds`
are unchanged; everything here is additive.

* `normalizedLaplaceMoment_three_le_sharp`, `normalizedLaplaceMoment_four_le_sharp`
  — the moment bounds with the `√s`.
* `dyadicHigherLaplaceMoments_le_sharp` — the transfer term is
  `≤ 104448/(n√n)`.
* `abs_negativeLaplaceTailError_nat_le_four_div` — the `4/n` tail bound
  (previously inlined at two places).
* `abs_dyadicEndpointLaplaceLogError_add_secondOrder_le_sharp` (+ `'`) —
  the comparison from `n ≥ 5329`.
* `abs_log_fabius_dyadic_sub_cumulantMain_le_sharp` — the cumulant form.
-/

set_option autoImplicit false

open Filter Asymptotics

namespace Fabius

/-- `√s · (c/s³) = c/(s²√s)` for `s > 0`. -/
private lemma sqrt_mul_div_pow_three {s : ℝ} (hs : 0 < s) (c : ℝ) :
    Real.sqrt s * (c / s ^ 3) = c / (s ^ 2 * Real.sqrt s) := by
  have hr : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hsq : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs.le
  rw [mul_div_assoc', div_eq_div_iff (by positivity) (by positivity)]
  have h : Real.sqrt s * c * (s ^ 2 * Real.sqrt s) =
      c * s ^ 2 * (Real.sqrt s * Real.sqrt s) := by ring
  rw [h, hsq]
  ring

/-- `√s · (c/s⁴) = c/(s³√s)` for `s > 0`. -/
private lemma sqrt_mul_div_pow_four {s : ℝ} (hs : 0 < s) (c : ℝ) :
    Real.sqrt s * (c / s ^ 4) = c / (s ^ 3 * Real.sqrt s) := by
  have hr : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hsq : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs.le
  rw [mul_div_assoc', div_eq_div_iff (by positivity) (by positivity)]
  have h : Real.sqrt s * c * (s ^ 3 * Real.sqrt s) =
      c * s ^ 3 * (Real.sqrt s * Real.sqrt s) := by ring
  rw [h, hsq]
  ring

/-- Third normalized moment on the ray `2 ≤ s`, keeping the `√s`:
`R₃(s) ≤ 384/(s²√s)`. -/
theorem normalizedLaplaceMoment_three_le_sharp
    (F : BoundedFabius) (hF : IsFabius F) {s : ℝ} (hs : 2 ≤ s) :
    normalizedLaplaceMoment F 3 s ≤ 384 / (s ^ 2 * Real.sqrt s) := by
  have hs0 : 0 < s := by linarith
  have h := normalizedLaplaceMoment_le_sqrt F hF 3 hs
  have h3 : (4 / s) ^ 3 * (Nat.factorial 3 : ℝ) = 384 / s ^ 3 := by
    rw [div_pow]
    norm_num [Nat.factorial]
    try ring
  rw [h3, sqrt_mul_div_pow_three hs0] at h
  exact h

/-- Fourth normalized moment on the ray `2 ≤ s`, keeping the `√s`:
`R₄(s) ≤ 6144/(s³√s)`. -/
theorem normalizedLaplaceMoment_four_le_sharp
    (F : BoundedFabius) (hF : IsFabius F) {s : ℝ} (hs : 2 ≤ s) :
    normalizedLaplaceMoment F 4 s ≤ 6144 / (s ^ 3 * Real.sqrt s) := by
  have hs0 : 0 < s := by linarith
  have h := normalizedLaplaceMoment_le_sqrt F hF 4 hs
  have h4 : (4 / s) ^ 4 * (Nat.factorial 4 : ℝ) = 6144 / s ^ 4 := by
    rw [div_pow]
    norm_num [Nat.factorial]
    try ring
  rw [h4, sqrt_mul_div_pow_four hs0] at h
  exact h

/-- The combined third- and fourth-moment transfer term is
`≤ 104448/(n√n)` on `2 ≤ n` — one half-power of `n` better than
`dyadicHigherLaplaceMoments_le`. -/
theorem dyadicHigherLaplaceMoments_le_sharp
    (F : BoundedFabius) (hF : IsFabius F) {n : ℕ} (hn : 2 ≤ n) :
    16 * ((n : ℝ) * normalizedLaplaceMoment F 3 n +
      (n : ℝ) ^ 2 * normalizedLaplaceMoment F 4 n) ≤
        104448 / ((n : ℝ) * Real.sqrt n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hr : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have h3 := normalizedLaplaceMoment_three_le_sharp F hF
    (by exact_mod_cast hn : (2 : ℝ) ≤ n)
  have h4 := normalizedLaplaceMoment_four_le_sharp F hF
    (by exact_mod_cast hn : (2 : ℝ) ≤ n)
  calc
    16 * ((n : ℝ) * normalizedLaplaceMoment F 3 n +
        (n : ℝ) ^ 2 * normalizedLaplaceMoment F 4 n) ≤
      16 * ((n : ℝ) * (384 / ((n : ℝ) ^ 2 * Real.sqrt n)) +
        (n : ℝ) ^ 2 * (6144 / ((n : ℝ) ^ 3 * Real.sqrt n))) := by gcongr
    _ = 104448 / ((n : ℝ) * Real.sqrt n) := by
      field_simp
      ring

/-- The negative-Laplace tail error is at most `4/n` for `n ≥ 1`. -/
theorem abs_negativeLaplaceTailError_nat_le_four_div {n : ℕ} (hn : 1 ≤ n) :
    |negativeLaplaceTailError n| ≤ 4 / (n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hexp : (n : ℝ) ≤ Real.exp n :=
    (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)).trans
      (Real.add_one_le_exp n)
  have hinv : Real.exp (-(n : ℝ)) ≤ (n : ℝ)⁻¹ := by
    rw [Real.exp_neg]
    exact (inv_le_inv₀ (Real.exp_pos _) hn0).2 hexp
  have hlogn : Real.log 2 ≤ (n : ℝ) := by
    have hn1r : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith [Real.log_lt_sub_one_of_pos
      (by norm_num : (0 : ℝ) < 2) (by norm_num)]
  calc
    |negativeLaplaceTailError n| ≤ 4 * Real.exp (-(n : ℝ)) :=
      abs_negativeLaplaceTailError_le_four_exp n hlogn
    _ ≤ 4 * (n : ℝ)⁻¹ := mul_le_mul_of_nonneg_left hinv (by norm_num)
    _ = 4 / (n : ℝ) := by rw [div_eq_mul_inv]

/-- The chart margin: `16/r + 104448/r³ ≤ 1/2` once `r ≥ 73`
(`r³ - 32r² - 208896 = (r - 73)(r² + 41r + 2993) + 9593`). -/
private lemma margin_le_half {r : ℝ} (hr : 73 ≤ r) :
    16 / r + 104448 / (r * r * r) ≤ 1 / 2 := by
  have hr0 : 0 < r := by linarith
  rw [div_add_div _ _ hr0.ne' (by positivity), div_le_iff₀ (by positivity)]
  nlinarith [mul_nonneg hr0.le (mul_nonneg (sub_nonneg.mpr hr)
    (by positivity : (0 : ℝ) ≤ r ^ 2 + 41 * r + 2993)), hr0, hr]

/-- **Effective endpoint/Laplace comparison with the sharp moment
bounds**: for `n ≥ 5329 = 73²`,
`|dyadicEndpointLaplaceLogError n + dyadicEndpointSecondOrder F n|
  ≤ 512/n + 208896/(n√n)`.  The threshold makes the two pointwise moment
bounds imply the radius-`1/2` logarithm-chart hypothesis. -/
theorem abs_dyadicEndpointLaplaceLogError_add_secondOrder_le_sharp
    (F : BoundedFabius) (hF : IsFabius F) {n : ℕ} (hn : 5329 ≤ n) :
    |dyadicEndpointLaplaceLogError n + dyadicEndpointSecondOrder F n| ≤
      512 / (n : ℝ) + 208896 / ((n : ℝ) * Real.sqrt n) := by
  have hn2 : 2 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnr : (5329 : ℝ) ≤ n := by exact_mod_cast hn
  have hr0 : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hrr : Real.sqrt (n : ℝ) * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
  have hr73 : (73 : ℝ) ≤ Real.sqrt n :=
    (Real.le_sqrt (by norm_num)).mpr (by linarith)
  have hsecond := dyadicEndpointSecondOrder_sq_le F hF hn2
  have hhigher := dyadicHigherLaplaceMoments_le_sharp F hF hn2
  have hsecond_nonneg : 0 ≤ dyadicEndpointSecondOrder F n := by
    unfold dyadicEndpointSecondOrder
    rw [← normalizedLaplaceMoment_two_eq_logSecond_add_first_sq]
    exact mul_nonneg (by positivity)
      (normalizedLaplaceMoment_nonneg F hF 2 hn0)
  have hS : dyadicEndpointSecondOrder F n ≤ 16 / Real.sqrt n := by
    rw [le_div_iff₀ hr0]
    have hsq : (dyadicEndpointSecondOrder F n * Real.sqrt n) ^ 2 ≤ 16 ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hn0.le]
      calc
        dyadicEndpointSecondOrder F n ^ 2 * (n : ℝ) ≤ 256 / (n : ℝ) * n := by
          gcongr
        _ = 16 ^ 2 := by
          field_simp
          norm_num
    exact (sq_le_sq₀ (mul_nonneg hsecond_nonneg hr0.le) (by norm_num)).mp hsq
  have hmargin : 16 / Real.sqrt n + 104448 / ((n : ℝ) * Real.sqrt n) ≤ 1 / 2 := by
    have h := margin_le_half hr73
    rwa [show Real.sqrt (n : ℝ) * Real.sqrt n * Real.sqrt n =
      (n : ℝ) * Real.sqrt n by rw [hrr]] at h
  have hsmall :
      |dyadicEndpointSecondOrder F n| +
        16 * ((n : ℝ) * normalizedLaplaceMoment F 3 n +
          (n : ℝ) ^ 2 * normalizedLaplaceMoment F 4 n) ≤ 1 / 2 := by
    rw [abs_of_nonneg hsecond_nonneg]
    linarith
  have hlog := abs_dyadicEndpointLaplaceLogError_add_secondOrder_le
    F hF n (by omega) (by
      simpa [dyadicEndpointSecondOrder] using hsmall)
  calc
    |dyadicEndpointLaplaceLogError n + dyadicEndpointSecondOrder F n| ≤
        2 * dyadicEndpointSecondOrder F n ^ 2 +
          2 * (16 * ((n : ℝ) * normalizedLaplaceMoment F 3 n +
            (n : ℝ) ^ 2 * normalizedLaplaceMoment F 4 n)) := by
      simpa [dyadicEndpointSecondOrder] using hlog
    _ ≤ 2 * (256 / (n : ℝ)) + 2 * (104448 / ((n : ℝ) * Real.sqrt n)) := by
      gcongr
    _ = 512 / (n : ℝ) + 208896 / ((n : ℝ) * Real.sqrt n) := by ring

/-- The comparison with a single `C/n`: `≤ 3374/n` for `n ≥ 5329`
(against `209408/n` for `n ≥ 224043` in `LaplaceMomentBounds`). -/
theorem abs_dyadicEndpointLaplaceLogError_add_secondOrder_le_sharp'
    (F : BoundedFabius) (hF : IsFabius F) {n : ℕ} (hn : 5329 ≤ n) :
    |dyadicEndpointLaplaceLogError n + dyadicEndpointSecondOrder F n| ≤
      3374 / (n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnr : (5329 : ℝ) ≤ n := by exact_mod_cast hn
  have hr0 : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hr73 : (73 : ℝ) ≤ Real.sqrt n :=
    (Real.le_sqrt (by norm_num)).mpr (by linarith)
  have htail : 208896 / ((n : ℝ) * Real.sqrt n) ≤ 2862 / (n : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) hn0]
    nlinarith [mul_le_mul_of_nonneg_left hr73 hn0.le]
  calc
    |dyadicEndpointLaplaceLogError n + dyadicEndpointSecondOrder F n| ≤
        512 / (n : ℝ) + 208896 / ((n : ℝ) * Real.sqrt n) :=
      abs_dyadicEndpointLaplaceLogError_add_secondOrder_le_sharp F hF hn
    _ ≤ 512 / (n : ℝ) + 2862 / (n : ℝ) := by linarith
    _ = 3374 / (n : ℝ) := by ring

/-- **Effective cumulant-form dyadic logarithmic estimate with the sharp
constants**: for `n ≥ 5329`,
`|log F(2⁻ⁿ) - dyadicSharpCumulantMain F n| ≤ 40537/(12n)`
(against `2512945/(12n)` for `n ≥ 224043`). -/
theorem abs_log_fabius_dyadic_sub_cumulantMain_le_sharp
    (F : BoundedFabius) (hF : IsFabius F) {n : ℕ} (hn : 5329 ≤ n) :
    |Real.log (fabiusReal F (((2 : ℝ) ^ n)⁻¹)) -
        dyadicSharpCumulantMain F n| ≤ 40537 / (12 * (n : ℝ)) := by
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hendpoint :=
    abs_dyadicEndpointLaplaceLogError_add_secondOrder_le_sharp' F hF hn
  have htail := abs_negativeLaplaceTailError_nat_le_four_div hn1
  have hstirling : |dyadicStirlingLogError n| ≤ 1 / (12 * (n : ℝ)) := by
    obtain ⟨hzero, hupper⟩ := dyadicStirlingLogError_bounds n hn1
    rw [abs_of_nonneg hzero]
    exact hupper
  have hidentity :
      Real.log (fabiusReal F (((2 : ℝ) ^ n)⁻¹)) -
          dyadicSharpCumulantMain F n =
        negativeLaplaceTailError n +
          (dyadicEndpointLaplaceLogError n + dyadicEndpointSecondOrder F n) -
            dyadicStirlingLogError n := by
    rw [log_fabius_dyadic_exact_sharp_decomposition_centered F hF n hn1]
    unfold dyadicSharpCumulantMain
    ring
  rw [hidentity]
  have htri : |negativeLaplaceTailError n +
        (dyadicEndpointLaplaceLogError n + dyadicEndpointSecondOrder F n) -
          dyadicStirlingLogError n| ≤
      |negativeLaplaceTailError n| +
        |dyadicEndpointLaplaceLogError n + dyadicEndpointSecondOrder F n| +
          |dyadicStirlingLogError n| := by
    have h1 := abs_sub_le_iff.mp (le_refl
      (|negativeLaplaceTailError n +
        (dyadicEndpointLaplaceLogError n + dyadicEndpointSecondOrder F n) -
          dyadicStirlingLogError n|))
    have h2 := abs_sub (negativeLaplaceTailError n +
      (dyadicEndpointLaplaceLogError n + dyadicEndpointSecondOrder F n))
      (dyadicStirlingLogError n)
    have h3 := abs_add_le (negativeLaplaceTailError n)
      (dyadicEndpointLaplaceLogError n + dyadicEndpointSecondOrder F n)
    linarith
  calc
    _ ≤ |negativeLaplaceTailError n| +
        |dyadicEndpointLaplaceLogError n + dyadicEndpointSecondOrder F n| +
          |dyadicStirlingLogError n| := htri
    _ ≤ 4 / (n : ℝ) + 3374 / (n : ℝ) + 1 / (12 * (n : ℝ)) := by
      gcongr
    _ = 40537 / (12 * (n : ℝ)) := by
      field_simp
      ring

end Fabius
