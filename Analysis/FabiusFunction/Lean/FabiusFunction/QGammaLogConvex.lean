import FabiusFunction.QGammaLogDerivative
import Mathlib.Analysis.Convex.Deriv

/-!
# The second logarithmic derivative of `Γ_q` and strict log-convexity

For `0 < q < 1` and `x > 0`, `QGammaLogDerivative` gives

`(log Γ_q)'(x) = -log(1-q) + log q · ∑_{n ≥ 0} q^{n+x}/(1 - q^{n+x})`.

Differentiating the series once more termwise (dominated on every half-line `x > ε` by the
geometric series `C q^n`) gives

`(log Γ_q)''(x) = (log q)^2 · ∑_{n ≥ 0} q^{n+x}/(1 - q^{n+x})^2 > 0`,

so `log Γ_q` is strictly convex on `(0, ∞)`: `Γ_q` is strictly log-convex.

## Main declarations

* `summable_rpow_div_one_sub_rpow`, `hasDerivAt_tsum_rpow_div_one_sub_rpow`.
* `hasDerivAt_deriv_log_qGamma`: the second logarithmic derivative.
* `deriv2_log_qGamma_pos`, `strictConvexOn_log_qGamma`.
-/

set_option autoImplicit false

open Filter Topology Set

namespace Fabius

variable {q : ℝ}

/-- The series `∑ q^{n+x}/(1 - q^{n+x})` is summable for `0 < q < 1`, `x > 0`. -/
theorem summable_rpow_div_one_sub_rpow (hq0 : 0 < q) (hq1 : q < 1) {x : ℝ} (hx : 0 < x) :
    Summable fun n : ℕ => q ^ ((n : ℝ) + x) / (1 - q ^ ((n : ℝ) + x)) := by
  have hx1 : q ^ x < 1 := Real.rpow_lt_one hq0.le hq1 hx
  have hx0 : 0 < q ^ x := Real.rpow_pos_of_pos hq0 x
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    ((summable_geometric_of_lt_one hq0.le hq1).mul_right (q ^ x / (1 - q ^ x)))
  · have h1 : q ^ ((n : ℝ) + x) < 1 := Real.rpow_lt_one hq0.le hq1 (by positivity)
    exact div_nonneg (Real.rpow_nonneg hq0.le _) (by linarith)
  · rw [Real.rpow_add hq0, Real.rpow_natCast]
    have hqn : 0 < q ^ n := pow_pos hq0 n
    have hle : q ^ n * q ^ x ≤ q ^ x := by
      calc q ^ n * q ^ x ≤ 1 * q ^ x := by gcongr; exact pow_le_one₀ hq0.le hq1.le
        _ = q ^ x := one_mul _
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left hx0.le (by linarith) (by linarith)) hqn.le

/-- The series `∑ q^{n+x}/(1 - q^{n+x})^2` is summable for `0 < q < 1`, `x > 0`. -/
theorem summable_rpow_div_one_sub_rpow_sq (hq0 : 0 < q) (hq1 : q < 1) {x : ℝ} (hx : 0 < x) :
    Summable fun n : ℕ => q ^ ((n : ℝ) + x) / (1 - q ^ ((n : ℝ) + x)) ^ 2 := by
  have hx1 : q ^ x < 1 := Real.rpow_lt_one hq0.le hq1 hx
  have hx0 : 0 < q ^ x := Real.rpow_pos_of_pos hq0 x
  have h1x : 0 < 1 - q ^ x := by linarith
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    ((summable_geometric_of_lt_one hq0.le hq1).mul_right (q ^ x / (1 - q ^ x) ^ 2))
  · exact div_nonneg (Real.rpow_nonneg hq0.le _) (sq_nonneg _)
  · rw [Real.rpow_add hq0, Real.rpow_natCast]
    have hqn : 0 < q ^ n := pow_pos hq0 n
    have hle : q ^ n * q ^ x ≤ q ^ x := by
      calc q ^ n * q ^ x ≤ 1 * q ^ x := by gcongr; exact pow_le_one₀ hq0.le hq1.le
        _ = q ^ x := one_mul _
    rw [mul_div_assoc]
    refine mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left hx0.le (pow_pos h1x 2) ?_) hqn.le
    exact pow_le_pow_left₀ h1x.le (by linarith) 2

/-- **Termwise differentiation** of `∑ q^{n+x}/(1 - q^{n+x})` for `x > 0`. -/
theorem hasDerivAt_tsum_rpow_div_one_sub_rpow (hq0 : 0 < q) (hq1 : q < 1) {x : ℝ}
    (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => ∑' n : ℕ, q ^ ((n : ℝ) + y) / (1 - q ^ ((n : ℝ) + y)))
      (∑' n : ℕ, Real.log q * (q ^ ((n : ℝ) + x) / (1 - q ^ ((n : ℝ) + x)) ^ 2)) x := by
  set ε := x / 2 with hε
  have hε0 : 0 < ε := by positivity
  have hε1 : q ^ ε < 1 := Real.rpow_lt_one hq0.le hq1 hε0
  have hεpos : 0 < q ^ ε := Real.rpow_pos_of_pos hq0 ε
  have h1ε : 0 < 1 - q ^ ε := by linarith
  -- the derivative of each term
  have hterm : ∀ (n : ℕ) (y : ℝ), 0 < y →
      HasDerivAt (fun y : ℝ => q ^ ((n : ℝ) + y) / (1 - q ^ ((n : ℝ) + y)))
        (Real.log q * (q ^ ((n : ℝ) + y) / (1 - q ^ ((n : ℝ) + y)) ^ 2)) y := by
    intro n y hy
    have hp : HasDerivAt (fun y : ℝ => q ^ ((n : ℝ) + y))
        (q ^ ((n : ℝ) + y) * Real.log q) y := by
      have := (Real.hasStrictDerivAt_const_rpow hq0 ((n : ℝ) + y)).hasDerivAt.comp y
        ((hasDerivAt_id y).const_add (n : ℝ))
      simpa [Function.comp_def] using this
    have hlt : q ^ ((n : ℝ) + y) < 1 := Real.rpow_lt_one hq0.le hq1 (by positivity)
    have hne : 1 - q ^ ((n : ℝ) + y) ≠ 0 := (sub_pos.mpr hlt).ne'
    refine (hp.div (hp.const_sub 1) hne).congr_deriv ?_
    field_simp
    ring
  -- the uniform bound on the half-line `y > ε`
  have hbound : ∀ (n : ℕ) (y : ℝ), y ∈ Ioi ε →
      ‖Real.log q * (q ^ ((n : ℝ) + y) / (1 - q ^ ((n : ℝ) + y)) ^ 2)‖ ≤
        (|Real.log q| * q ^ ε / (1 - q ^ ε) ^ 2) * q ^ n := by
    intro n y hy
    have hy : ε < y := hy
    have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
    have hp0 : 0 < q ^ ((n : ℝ) + y) := Real.rpow_pos_of_pos hq0 _
    have hp1 : q ^ ((n : ℝ) + y) ≤ q ^ ε :=
      Real.rpow_le_rpow_of_exponent_ge hq0 hq1.le (by linarith)
    have hp1' : q ^ ((n : ℝ) + y) < 1 := hp1.trans_lt hε1
    have hsplit : q ^ ((n : ℝ) + y) ≤ q ^ n * q ^ ε := by
      rw [Real.rpow_add hq0, Real.rpow_natCast]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge hq0 hq1.le hy.le) (pow_pos hq0 n).le
    have hnn : 0 ≤ q ^ ((n : ℝ) + y) / (1 - q ^ ((n : ℝ) + y)) ^ 2 :=
      div_nonneg hp0.le (sq_nonneg _)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn,
      show |Real.log q| * q ^ ε / (1 - q ^ ε) ^ 2 * q ^ n =
        |Real.log q| * (q ^ n * q ^ ε / (1 - q ^ ε) ^ 2) by ring]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine div_le_div₀ (by positivity) hsplit (pow_pos h1ε 2) ?_
    exact pow_le_pow_left₀ h1ε.le (by linarith) 2
  have hxε : x ∈ Ioi ε := by
    show ε < x
    rw [hε]
    linarith
  exact hasDerivAt_tsum_of_isPreconnected
    (g := fun n y => q ^ ((n : ℝ) + y) / (1 - q ^ ((n : ℝ) + y)))
    (g' := fun n y => Real.log q * (q ^ ((n : ℝ) + y) / (1 - q ^ ((n : ℝ) + y)) ^ 2))
    (u := fun n : ℕ => (|Real.log q| * q ^ ε / (1 - q ^ ε) ^ 2) * q ^ n) (t := Ioi ε)
    ((summable_geometric_of_lt_one hq0.le hq1).mul_left _) isOpen_Ioi isPreconnected_Ioi
    (fun n y hy => hterm n y (hε0.trans hy)) hbound hxε
    (summable_rpow_div_one_sub_rpow hq0 hq1 hx) hxε

/-- **The second logarithmic derivative of `Γ_q`**: for `0 < q < 1` and `x > 0`, the first
logarithmic derivative `-log(1-q) + log q ∑ q^{n+x}/(1-q^{n+x})` has derivative
`(log q)^2 ∑ q^{n+x}/(1-q^{n+x})^2`. -/
theorem hasDerivAt_deriv_log_qGamma (hq0 : 0 < q) (hq1 : q < 1) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => -Real.log (1 - q) + Real.log q *
        ∑' n : ℕ, q ^ ((n : ℝ) + y) / (1 - q ^ ((n : ℝ) + y)))
      (Real.log q ^ 2 * ∑' n : ℕ, q ^ ((n : ℝ) + x) / (1 - q ^ ((n : ℝ) + x)) ^ 2) x := by
  have h := ((hasDerivAt_tsum_rpow_div_one_sub_rpow hq0 hq1 hx).const_mul (Real.log q)).const_add
    (-Real.log (1 - q))
  refine h.congr_deriv ?_
  rw [tsum_mul_left]
  ring

/-- The second logarithmic derivative of `Γ_q` is positive. -/
theorem deriv2_log_qGamma_pos (hq0 : 0 < q) (hq1 : q < 1) {x : ℝ} (hx : 0 < x) :
    0 < Real.log q ^ 2 * ∑' n : ℕ, q ^ ((n : ℝ) + x) / (1 - q ^ ((n : ℝ) + x)) ^ 2 := by
  have hlog : Real.log q ≠ 0 := by
    intro h
    rcases Real.log_eq_zero.mp h with h | h | h <;> linarith
  refine mul_pos (by positivity) ?_
  refine (summable_rpow_div_one_sub_rpow_sq hq0 hq1 hx).tsum_pos (fun n => ?_) 0 ?_
  · exact div_nonneg (Real.rpow_nonneg hq0.le _) (sq_nonneg _)
  · have hlt : q ^ ((0 : ℕ) + x : ℝ) < 1 := Real.rpow_lt_one hq0.le hq1 (by simp [hx])
    exact div_pos (Real.rpow_pos_of_pos hq0 _) (pow_pos (sub_pos.mpr hlt) 2)

/-- **`Γ_q` is strictly log-convex** on `(0, ∞)` for `0 < q < 1`. -/
theorem strictConvexOn_log_qGamma (hq0 : 0 < q) (hq1 : q < 1) :
    StrictConvexOn ℝ (Ioi 0) (fun x : ℝ => Real.log (qGamma q x)) := by
  set f : ℝ → ℝ := fun x => Real.log (qGamma q x) with hf
  set g : ℝ → ℝ := fun y => -Real.log (1 - q) + Real.log q *
    ∑' n : ℕ, q ^ ((n : ℝ) + y) / (1 - q ^ ((n : ℝ) + y)) with hg
  have hfg : ∀ y, 0 < y → HasDerivAt f (g y) y := fun y hy => hasDerivAt_log_qGamma hq0 hq1 hy
  refine strictConvexOn_of_deriv2_pos (convex_Ioi 0) ?_ ?_
  · exact fun y hy => (hfg y hy).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    have hx : 0 < x := hx
    have hderiv : deriv f =ᶠ[𝓝 x] g :=
      Filter.eventuallyEq_of_mem (Ioi_mem_nhds hx) fun y hy => (hfg y hy).deriv
    have h2 : HasDerivAt (deriv f) (Real.log q ^ 2 *
        ∑' n : ℕ, q ^ ((n : ℝ) + x) / (1 - q ^ ((n : ℝ) + x)) ^ 2) x :=
      (hasDerivAt_deriv_log_qGamma hq0 hq1 hx).congr_of_eventuallyEq hderiv
    show 0 < deriv (deriv f) x
    rw [h2.deriv]
    exact deriv2_log_qGamma_pos hq0 hq1 hx

end Fabius
