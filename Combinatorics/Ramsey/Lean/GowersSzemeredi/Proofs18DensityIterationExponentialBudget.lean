import GowersSzemeredi.Proofs18DensityIterationPowerBound
import GowersSzemeredi.Proofs13FejerThresholdPolynomial

/-! Double-exponential density iteration when the inverse length exponent
and logarithmic threshold budget are single exponential. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The exponentially small cubic length exponent still permits a
fixed-power double-exponential bound on the full finite iteration. -/
theorem densityIterationClosedThreshold_le_double_exp_of_exp_budget
    (T c rho gain X : Real) (g r p : Nat) (hgain : 0 < gain) (hX : 2 ≤ X)
    (hA : 1 + Real.log (max 1 T) + |Real.log c| ≤ Real.exp (X ^ p))
    (hg : gain⁻¹ ≤ X ^ g) (hb : 2 * max 1 rho⁻¹ ≤ Real.exp (X ^ r))
    (hp : g + 1 + r ≤ p) :
    densityIterationClosedThreshold T c rho ⌈gain⁻¹⌉₊ ≤
      Real.exp (Real.exp (X ^ (p + 1))) := by
  refine (densityIterationClosedThreshold_le_double_exp_of_exp_power_bounds
    T c rho gain (X ^ p) X g r p hgain hX hA hg hb hp).trans ?_
  apply Real.exp_le_exp.mpr (Real.exp_le_exp.mpr _)
  simpa only [two_mul, pow_succ'] using
    mul_le_mul_of_nonneg_right hX (pow_nonneg (by linarith only [hX] : (0 : Real) ≤ X) p)

end LeanProofs.GowersSzemeredi
