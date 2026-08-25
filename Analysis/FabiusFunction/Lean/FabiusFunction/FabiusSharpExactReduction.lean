import FabiusFunction.FabiusSaddleReduction
import FabiusFunction.FabiusSharpLambertMain

/-!
# Exact reduction of the sharp Fabius error to the saddle mass

The leading sharp-asymptotic development only needed a one-term Big-O
transfer from the normalized Bromwich integral.  A full Poincaré expansion
needs the underlying exact identity.  On the lower-Lambert branch, the
difference between `log F` and the corrected sharp main term is exactly the
logarithm of the real normalized saddle ratio plus the exponentially small
forward tail of the dyadic Laplace product.

This module isolates that identity so arbitrary-order estimates of the
normalized kernel can be transported without repeating the saddle algebra.
It also records the exactly equivalent multiplicative factorization obtained
by exponentiating the logarithmic identity.
-/

set_option autoImplicit false

namespace Fabius

/-- Exact decomposition of the corrected logarithmic error into the
normalized saddle mass and the forward product tail. -/
theorem log_fabius_sub_sharpLambertMain_eq_log_ratio_add_tail
    (F : BoundedFabius) (hF : IsFabius F) {x : ℝ}
    (hx : 0 < x) (hsmall : Real.log 2 * x < Real.exp (-1)) :
    Real.log (fabiusReal F x) - fabiusSharpLambertMain x =
      Real.log (fabiusSaddleRatio F x (fabiusLambertRadius x)
        (fabiusLambertPhase x)) +
          negativeLaplaceTailError (fabiusLambertRadius x) := by
  have hFx : 0 < fabiusReal F x := fabius_pos_of_pos F hF hx
  have hphase : 0 < fabiusLambertPhase x :=
    fabiusLambertPhase_pos hx hsmall
  rw [log_fabiusSaddleRatio F hFx hphase]
  rw [fabiusLambertSaddleAction_eq hx hsmall]
  ring

/-- Multiplicative form of the exact sharp reduction.  The ratio of `F(x)`
to the exponential sharp main term is exactly the normalized saddle ratio
times the exponential forward-tail correction. -/
theorem fabius_div_exp_sharpLambertMain_eq_saddleRatio_mul_exp_tail
    (F : BoundedFabius) (hF : IsFabius F) {x : ℝ}
    (hx : 0 < x) (hsmall : Real.log 2 * x < Real.exp (-1)) :
    fabiusReal F x / Real.exp (fabiusSharpLambertMain x) =
      fabiusSaddleRatio F x (fabiusLambertRadius x)
          (fabiusLambertPhase x) *
        Real.exp (negativeLaplaceTailError (fabiusLambertRadius x)) := by
  have hFx : 0 < fabiusReal F x := fabius_pos_of_pos F hF hx
  have hphase : 0 < fabiusLambertPhase x :=
    fabiusLambertPhase_pos hx hsmall
  have hratio :
      0 < fabiusSaddleRatio F x (fabiusLambertRadius x)
        (fabiusLambertPhase x) :=
    fabiusSaddleRatio_pos F hFx hphase
  have hlog := congrArg Real.exp
    (log_fabius_sub_sharpLambertMain_eq_log_ratio_add_tail
      F hF hx hsmall)
  simpa only [Real.exp_sub, Real.exp_add, Real.exp_log hFx,
    Real.exp_log hratio] using hlog

end Fabius
