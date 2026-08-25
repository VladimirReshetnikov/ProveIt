import FabiusFunction.NegativeLaplaceVerticalLog
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Taylor

/-!
# All-order smoothness of the vertical negative-Laplace logarithm

The branch-safe logarithm on a positive vertical line was originally used
only through four derivatives.  An all-orders saddle expansion needs every
derivative.  The underlying transform curve is smooth to every order and
never vanishes, so its logarithmic derivative has the same regularity; the
fundamental theorem of calculus then promotes the normalized logarithm too.
-/

set_option autoImplicit false

namespace Fabius

/-- For `r > 0` the vertical logarithmic derivative
`negativeLaplaceVerticalLogDerivative F r` is `C^∞` in the vertical
parameter, on all of `ℝ`.  The exponent `↑(⊤ : ℕ∞)` is the `C^∞` exponent
of `WithTop ℕ∞`, not the analytic exponent.  Assumes `IsFabius F`, which
supplies both the regularity of the vertical curve and its non-vanishing. -/
theorem contDiff_negativeLaplaceVerticalLogDerivative_infty
    (F : BoundedFabius) (hF : IsFabius F) {r : ℝ} (hr : 0 < r) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (negativeLaplaceVerticalLogDerivative F r) := by
  unfold negativeLaplaceVerticalLogDerivative
  have hcurve := contDiff_negativeLaplaceVerticalCurve F hF r
  have hcurveSmooth : ContDiff ℝ (↑(⊤ : ℕ∞))
      (negativeLaplaceVerticalCurve F r) := hcurve.of_le (by simp)
  have hcurveDeriv : ContDiff ℝ (↑(⊤ : ℕ∞))
      (deriv (negativeLaplaceVerticalCurve F r)) :=
    (contDiff_infty_iff_deriv.mp hcurveSmooth).2
  exact hcurveDeriv.mul
    (hcurveSmooth.inv (negativeLaplaceVerticalCurve_ne_zero F hF hr))

/-- For `r > 0` the branch-safe vertical logarithm
`negativeLaplaceVerticalLog F r` is `C^∞` in the vertical parameter, on all
of `ℝ`.  The exponent `↑(⊤ : ℕ∞)` is the `C^∞` exponent of `WithTop ℕ∞`,
not the analytic exponent.  Assumes `IsFabius F`.  Used by
`FabiusFunction.FabiusSaddleCentralAllOrders`. -/
theorem contDiff_negativeLaplaceVerticalLog_infty
    (F : BoundedFabius) (hF : IsFabius F) {r : ℝ} (hr : 0 < r) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (negativeLaplaceVerticalLog F r) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun theta =>
    (negativeLaplaceVerticalLog_hasDerivAt F hF hr theta).differentiableAt, ?_⟩
  have hderiv : deriv (negativeLaplaceVerticalLog F r) =
      negativeLaplaceVerticalLogDerivative F r := by
    funext theta
    exact (negativeLaplaceVerticalLog_hasDerivAt F hF hr theta).deriv
  rw [hderiv]
  exact contDiff_negativeLaplaceVerticalLogDerivative_infty F hF hr

/-- For `r > 0` and every order `k`, the `k`-th iterated vertical derivative of
the branch-safe vertical logarithm is again `C^∞`.  The exponent
`↑(⊤ : ℕ∞)` is the `C^∞` exponent of `WithTop ℕ∞`, not the analytic
exponent.  Assumes `IsFabius F`.  Used at order one by
`FabiusFunction.NegativeLaplaceVerticalAllOrderBound`. -/
theorem contDiff_iteratedDeriv_negativeLaplaceVerticalLog_infty
    (F : BoundedFabius) (hF : IsFabius F) {r : ℝ} (hr : 0 < r) (k : ℕ) :
    ContDiff ℝ (↑(⊤ : ℕ∞))
      (iteratedDeriv k (negativeLaplaceVerticalLog F r)) := by
  rw [iteratedDeriv_eq_iterate]
  exact ContDiff.iterate_deriv k
    (contDiff_negativeLaplaceVerticalLog_infty F hF hr)

/-- For `r > 0` and every order `k`, the `k`-th iterated vertical derivative of
the branch-safe vertical logarithm is continuous on all of `ℝ`.  Assumes
`IsFabius F`.  Used by `FabiusFunction.FabiusSaddleMassAllOrders`. -/
theorem continuous_iteratedDeriv_negativeLaplaceVerticalLog
    (F : BoundedFabius) (hF : IsFabius F) {r : ℝ} (hr : 0 < r) (k : ℕ) :
    Continuous (iteratedDeriv k (negativeLaplaceVerticalLog F r)) :=
  (contDiff_iteratedDeriv_negativeLaplaceVerticalLog_infty F hF hr k).continuous

/-- Taylor's integral remainder for the branch-safe vertical logarithm at an
arbitrary order, expressed with the global iterated derivative. -/
theorem negativeLaplaceVerticalLog_sub_taylorWithinEval_eq_integralRemainder
    (F : BoundedFabius) (hF : IsFabius F) {r : ℝ} (hr : 0 < r)
    (n : ℕ) (theta : ℝ) :
    negativeLaplaceVerticalLog F r theta -
        taylorWithinEval (negativeLaplaceVerticalLog F r) n
          (Set.uIcc 0 theta) 0 theta =
      ∫ t in (0 : ℝ)..theta,
        ((theta - t) ^ n / (n.factorial : ℝ)) •
          iteratedDeriv (n + 1) (negativeLaplaceVerticalLog F r) t := by
  by_cases htheta : theta = 0
  · subst theta
    simp
  have hcont := contDiff_negativeLaplaceVerticalLog_infty F hF hr
  have htaylor := taylor_integral_remainder
    (f := negativeLaplaceVerticalLog F r) (x₀ := (0 : ℝ)) (x := theta) (n := n)
    ((hcont.of_le (by
      exact_mod_cast (show (n + 1 : ℕ∞) ≤ (⊤ : ℕ∞) from le_top))).contDiffOn)
  rw [htaylor]
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [iteratedDerivWithin_eq_iteratedDeriv
    (uniqueDiffOn_uIcc (fun h => htheta h.symm))
    ((hcont.of_le (by
      exact_mod_cast (show (n + 1 : ℕ∞) ≤ (⊤ : ℕ∞) from le_top))).contDiffAt) ht]

/-- A uniform bound on the next vertical derivative gives an arbitrary-order
Taylor remainder estimate.  The constant is deliberately simple; the exact
integral improves `n!` to `(n+1)!` when desired. -/
theorem norm_negativeLaplaceVerticalLog_sub_taylorWithinEval_le
    (F : BoundedFabius) (hF : IsFabius F) {r : ℝ} (hr : 0 < r)
    (n : ℕ) (theta M : ℝ)
    (hM : ∀ t ∈ Set.uIcc (0 : ℝ) theta,
      ‖iteratedDeriv (n + 1) (negativeLaplaceVerticalLog F r) t‖ ≤ M) :
    ‖negativeLaplaceVerticalLog F r theta -
        taylorWithinEval (negativeLaplaceVerticalLog F r) n
          (Set.uIcc 0 theta) 0 theta‖ ≤
      M * |theta| ^ (n + 1) / (n.factorial : ℝ) := by
  by_cases htheta : theta = 0
  · subst theta
    simp
  have hdist (t : ℝ) (ht : t ∈ Set.uIcc (0 : ℝ) theta) :
      |theta - t| ≤ |theta| := by
    rcases le_total 0 theta with hpos | hneg
    · rw [Set.uIcc_of_le hpos] at ht
      rw [abs_of_nonneg (sub_nonneg.mpr ht.2), abs_of_nonneg hpos]
      exact sub_le_self theta ht.1
    · rw [Set.uIcc_of_ge hneg] at ht
      rw [abs_of_nonpos (sub_nonpos.mpr ht.1), abs_of_nonpos hneg]
      linarith [ht.2]
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := theta)
    (C := M * |theta| ^ n / (n.factorial : ℝ))
    (f := fun t => ((theta - t) ^ n / (n.factorial : ℝ)) •
      iteratedDeriv (n + 1) (negativeLaplaceVerticalLog F r) t) (by
      intro t ht
      have ht' : t ∈ Set.uIcc (0 : ℝ) theta := Set.uIoc_subset_uIcc ht
      have hfac : |(n.factorial : ℝ)| = (n.factorial : ℝ) :=
        abs_of_nonneg (Nat.cast_nonneg n.factorial)
      rw [norm_smul, Real.norm_eq_abs, abs_div, abs_pow]
      rw [hfac]
      calc
        |theta - t| ^ n / (n.factorial : ℝ) *
              ‖iteratedDeriv (n + 1) (negativeLaplaceVerticalLog F r) t‖
            ≤ |theta| ^ n / (n.factorial : ℝ) * M := by
              apply mul_le_mul
              · exact div_le_div_of_nonneg_right
                  (pow_le_pow_left₀ (abs_nonneg _) (hdist t ht') n)
                  (Nat.cast_nonneg n.factorial)
              · exact hM t ht'
              · exact norm_nonneg _
              · positivity
        _ = M * |theta| ^ n / (n.factorial : ℝ) := by ring)
  rw [negativeLaplaceVerticalLog_sub_taylorWithinEval_eq_integralRemainder
    F hF hr n theta]
  calc
    ‖∫ t in (0 : ℝ)..theta, ((theta - t) ^ n / (n.factorial : ℝ)) •
        iteratedDeriv (n + 1) (negativeLaplaceVerticalLog F r) t‖
        ≤ (M * |theta| ^ n / (n.factorial : ℝ)) * |theta - 0| := hint
    _ = M * |theta| ^ (n + 1) / (n.factorial : ℝ) := by
      rw [sub_zero, pow_succ]
      ring

end Fabius
