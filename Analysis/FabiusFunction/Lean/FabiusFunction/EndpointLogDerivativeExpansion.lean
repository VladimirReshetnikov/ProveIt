import FabiusFunction.LaplaceCumulantAsymptotics
import FabiusFunction.NegativeLaplaceDerivativeBounds

/-!
# The corrected endpoint expansion, unconditionally, from the logarithmic
derivatives

`LaplaceCumulantAsymptotics` proves the corrected endpoint expansion

`dyadicEndpointLaplaceLogError n + (n/2)(q''(n) + q'(n)²) = O(1/n)`

*conditionally* on the four bounds `q⁽ʲ⁾(n) = O(log n / nʲ)`,
`j = 1,…,4`.  Those four bounds are theorems of
`NegativeLaplaceDerivativeBounds`, but neither module imports the other, so
the conditional statement had no instance anywhere in the corpus.  This
leaf supplies it.

The result duplicates
`LaplaceMomentBounds.dyadicEndpointLaplaceLogError_add_secondOrder_isBigO_unconditional`
as a statement, but by a genuinely different route: that proof runs on
log-convexity of the tilted moments and never mentions the logarithmic
derivatives, while this one is the Bell-polynomial inversion of the
moment/derivative dictionary.  Having both makes the conditional theorem
non-vacuous and cross-checks the dictionary.
-/

set_option autoImplicit false

open Filter Asymptotics

namespace Fabius

/-- **The corrected endpoint expansion, unconditionally.**  The four
hypotheses of
`dyadicEndpointLaplaceLogError_add_secondOrder_isBigO_of_logDerivative_bounds`
are exactly the four theorems of `NegativeLaplaceDerivativeBounds`, so the
conditional expansion holds outright. -/
theorem dyadicEndpointLaplaceLogError_add_secondOrder_isBigO_logDerivative
    (F : BoundedFabius) (hF : IsFabius F) :
    (fun n : ℕ => dyadicEndpointLaplaceLogError n +
      (n : ℝ) / 2 *
        (negativeLaplaceLogSecond F n +
          negativeLaplaceLogFirst F n ^ 2)) =O[atTop]
      (fun n : ℕ => (n : ℝ)⁻¹) :=
  dyadicEndpointLaplaceLogError_add_secondOrder_isBigO_of_logDerivative_bounds
    F hF
    (negativeLaplaceLogFirst_isBigO_log_div_nat F hF)
    (negativeLaplaceLogSecond_isBigO_log_div_sq_nat F hF)
    (negativeLaplaceLogThird_isBigO_log_div_cube_nat F hF)
    (negativeLaplaceLogFourth_isBigO_log_div_fourth_nat F hF)

end Fabius
