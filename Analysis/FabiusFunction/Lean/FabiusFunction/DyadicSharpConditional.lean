import FabiusFunction.EndpointLaplaceComparison

/-!
# Conditional sharp dyadic Fabius asymptotic

This module assembles every already-quantified contribution in the exact
dyadic decomposition.  It defines the second endpoint/Laplace correction and
the corresponding cumulant main term.  The product-tail and sharp-Stirling
errors are proved to be `O(1/n)` directly.

The headline theorem therefore reduces the complete dyadic formula to exactly
the two moment estimates isolated by `EndpointLaplaceComparison`.  A later
module discharges those estimates from bounds on the first four logarithmic
derivatives.
-/

set_option autoImplicit false

open Filter Asymptotics

namespace Fabius

/-- The second-order endpoint correction to the negative Laplace transform. -/
noncomputable def dyadicEndpointSecondOrder
    (F : BoundedFabius) (n : ℕ) : ℝ :=
  (n : ℝ) / 2 *
    (negativeLaplaceLogSecond F n + negativeLaplaceLogFirst F n ^ 2)

/-- The endpoint correction vanishes at the scale-zero boundary. -/
@[simp] theorem dyadicEndpointSecondOrder_zero (F : BoundedFabius) :
    dyadicEndpointSecondOrder F 0 = 0 := by
  simp [dyadicEndpointSecondOrder]

/-- The exact elementary, constant, periodic, and second-order terms in the
sharp dyadic logarithmic asymptotic. -/
noncomputable def dyadicSharpCumulantMain
    (F : BoundedFabius) (n : ℕ) : ℝ :=
  dyadicSharpElementaryMain n +
    (negativeLaplacePeriodicMean - Real.log (2 * Real.pi) / 2) +
    negativeLaplacePsi (Real.logb 2 n) - dyadicEndpointSecondOrder F n

/-- The exact product-tail correction is `O(1/n)` along natural scales. -/
theorem negativeLaplaceTailError_nat_isBigO_inv :
    (fun n : ℕ => negativeLaplaceTailError n) =O[atTop]
      (fun n : ℕ => (n : ℝ)⁻¹) := by
  rw [isBigO_iff]
  refine ⟨4, ?_⟩
  filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hexp : (n : ℝ) ≤ Real.exp n := by
    exact (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)).trans
      (Real.add_one_le_exp n)
  have hinv : Real.exp (-(n : ℝ)) ≤ (n : ℝ)⁻¹ := by
    rw [Real.exp_neg]
    exact (inv_le_inv₀ (Real.exp_pos _) hnpos).2 hexp
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnpos)]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogn : Real.log 2 ≤ (n : ℝ) := by
    linarith [Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)]
  exact (abs_negativeLaplaceTailError_le_four_exp n hlogn).trans
    (mul_le_mul_of_nonneg_left hinv (by norm_num))

/-- The sharp Stirling remainder is `O(1/n)` along natural scales. -/
theorem dyadicStirlingLogError_isBigO_inv :
    dyadicStirlingLogError =O[atTop] (fun n : ℕ => (n : ℝ)⁻¹) := by
  rw [isBigO_iff]
  refine ⟨1 / 12, ?_⟩
  filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  obtain ⟨hzero, hupper⟩ := dyadicStirlingLogError_bounds n hn
  rw [Real.norm_eq_abs, abs_of_nonneg hzero, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hnpos)]
  calc
    dyadicStirlingLogError n ≤ 1 / (12 * (n : ℝ)) := hupper
    _ = (1 / 12) * (n : ℝ)⁻¹ := by ring

/-- Conditional sharp dyadic asymptotic.  The hypotheses are exactly the two
quantitative estimates produced by the endpoint/Laplace comparison. -/
theorem log_fabius_dyadic_sub_cumulantMain_isBigO
    (F : BoundedFabius) (hF : IsFabius F)
    (hsecond :
      (fun n : ℕ => (dyadicEndpointSecondOrder F n) ^ 2) =O[atTop]
        (fun n : ℕ => (n : ℝ)⁻¹))
    (hhigher :
      (fun n : ℕ => 16 *
        ((n : ℝ) * normalizedLaplaceMoment F 3 n +
          (n : ℝ) ^ 2 * normalizedLaplaceMoment F 4 n)) =O[atTop]
        (fun n : ℕ => (n : ℝ)⁻¹)) :
    (fun n : ℕ =>
      Real.log (fabiusReal F (((2 : ℝ) ^ n)⁻¹)) -
        dyadicSharpCumulantMain F n) =O[atTop]
      (fun n : ℕ => (n : ℝ)⁻¹) := by
  have hendpoint := dyadicEndpointLaplaceLogError_add_secondOrder_isBigO
    F hF (by simpa [dyadicEndpointSecondOrder] using hsecond) hhigher
  have hsum := negativeLaplaceTailError_nat_isBigO_inv.add hendpoint |>.sub
    dyadicStirlingLogError_isBigO_inv
  apply hsum.congr'
  · filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
    rw [log_fabius_dyadic_exact_sharp_decomposition_centered F hF n hn]
    unfold dyadicSharpCumulantMain dyadicEndpointSecondOrder
    ring
  · exact Filter.EventuallyEq.rfl

end Fabius
