import FabiusFunction.ActivationSeriesAsymptotics
import FabiusFunction.GeometricActivationDimension

/-!
# Sharp asymptotics for geometric activation dimensions

The generic square-summable activation-series theorem specializes to the
normalized geometric weights

`w n = q ^ n * (1 - q)`.

Their squared sum is `(1 - q) / (1 + q)` whenever `|q| < 1`.  Consequently,
the quadratic coefficient in the global estimate for
`geometricActivationDimension` is exact, not merely an upper bound.  The
dyadic coefficient is `1 / 9`.  The analytic theorem uses `|q| < 1`; its
frontier-report interpretation as a positive-weight active count uses the
narrower range `0 < q < 1`.  No Bernoulli family or expectation identity is
constructed here.
-/

set_option autoImplicit false

open Filter
open scoped Topology

namespace Fabius

noncomputable section

/-- The normalized geometric activation dimension has sharp quadratic
coefficient `(1 - q) / (3 * (1 + q))` throughout the convergent range:

`geometricActivationDimension q t / t ^ 2
    -> (1 - q) / (3 * (1 + q))`

as `t -> 0` through nonzero values. -/
theorem tendsto_geometricActivationDimension_div_sq
    {q : ℝ} (hq : |q| < 1) :
    Tendsto
      (fun t : ℝ ↦ geometricActivationDimension q t / t ^ 2)
      (𝓝[≠] 0) (𝓝 ((1 - q) / (3 * (1 + q)))) := by
  have hweights := hasSum_normalizedGeometricWeight_sq hq
  have hlimit :=
    tendsto_tsum_activationProbability_mul_div_sq hweights.summable
  have hplus : 1 + q ≠ 0 := by
    have hq_lower := (abs_lt.mp hq).1
    linarith
  have hcoefficient :
      ((1 - q) / (1 + q)) / 3 = (1 - q) / (3 * (1 + q)) := by
    field_simp [hplus]
  rw [hweights.tsum_eq, hcoefficient] at hlimit
  simpa only [geometricActivationDimension, mul_assoc] using hlimit

/-- The dyadic effective activation dimension has sharp quadratic
coefficient `1 / 9`:

`dyadicEffectiveDimension t / t ^ 2 -> 1 / 9`

as `t -> 0` through nonzero values. -/
theorem tendsto_dyadicEffectiveDimension_div_sq :
    Tendsto (fun t : ℝ ↦ dyadicEffectiveDimension t / t ^ 2)
      (𝓝[≠] 0) (𝓝 (1 / 9 : ℝ)) := by
  convert
    (tendsto_geometricActivationDimension_div_sq
      (q := (1 / 2 : ℝ)) (by norm_num)) using 1 <;>
    norm_num [dyadicEffectiveDimension]

end

end Fabius
