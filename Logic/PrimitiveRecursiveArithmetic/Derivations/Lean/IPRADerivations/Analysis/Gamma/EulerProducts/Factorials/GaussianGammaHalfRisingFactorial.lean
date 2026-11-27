import IPRADerivations.Analysis.Gamma.HalfInteger.GaussianGammaHalfIntegerDomain
import IPRADerivations.Probability.NormalMoments

/-!
# The original half-integer rising product has its exact factorial value

The actual original risingProduct at 1/2 is the existing odd double
factorial divided by 2^N, for every internal N. Its original finite
recursion is bound directly to NormalMoments.df_succ. The checked exact
double-factorial identity then gives (2N)!/(2^N*2^N*N!). This is finite
arithmetic and does not assume a half-integer Gamma value.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaHalfRisingFactorial

open_ipra
open GaussianGammaRepeatedShift (risingProduct prefix_zero prefix_succ)
open GaussianGammaEulerHeadShift (linear)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (positive_product)
open GaussianRationalSyntheticDivision (qmul_congr qone)
open GaussianCoefficientNameBounds (unit unit_positive)
open LeanProofs.IPRA.Probability.NormalMoments (df df_zero df_succ df_fact)
open ComplexLogarithmRemainder (oneCode scale)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def value (N : PTm n) : PTm n := fraction (df N) (unit N)
def factorialValue (N : PTm n) : PTm n := fraction (Products.fact (two*N)) (unit N*unit N*Products.fact N)
def law (N : PTm n) : Fm PTm n := risingProduct oneCode two N ≐ value N
ipra_subst value [df]
ipra_subst factorialValue [Products.fact]
ipra_subst law

theorem linear_value (N : PTm n) : Γ ⊢[PRAAx] linear (oneCode : PTm n) two N ≐ fraction (succ (two*N)) two := by
  apply GaussianGammaFiniteValueProperness.fraction_equal _ _ two (zero_lt_succ one)
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [GaussianGammaEulerHeadLower.translated,GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,
      GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one]
  all_goals (ipra_simps; ring)

theorem base : Γ ⊢[PRAAx] law (zero : PTm n) := by
  have simplify : Γ ⊢[PRAAx] value (zero : PTm n) ≐ qone :=
    (GaussianCompactRiemannName.fraction_congr _ _ _ _ df_zero (pw_zero two)).eqTrans GaussianGammaFactorialValues.natural_one
  exact (prefix_zero oneCode two).eqTrans simplify.eqSymm

theorem step (N : PTm n) (ih : Γ ⊢[PRAAx] law N) : Γ ⊢[PRAAx] law (succ N) :=
  (prefix_succ oneCode two N).eqTrans ((qmul_congr ih (linear_value N)).eqTrans
    ((GaussianEulerDampedTimeRate.fraction_product (df N) (unit N) (succ (two*N)) two (unit_positive N) (zero_lt_succ one)).eqTrans
      (GaussianCompactRiemannName.fraction_congr _ _ _ _ (df_succ N).eqSymm (pw_succ two N).eqSymm)))

theorem original_half_rising (N : PTm n) : Γ ⊢[PRAAx] law N := by
  have all : Γ ⊢[PRAAx] .all (law (var 0)) := by
    ipra_qfind [subst_law]
    · exact base
    · exact step _ Prf.hyp0
  simpa only [subst_law,Syn.subst_var,Syn.inst_zero] using all.allE N

theorem factorial_positive (N : PTm n) : Γ ⊢[PRAAx] le one (Products.fact N) :=
  Order.zero_lt_of_eq_succ (AnalyticNumberTheory.Primes.fact_pos N)

theorem factorial_formula (N : PTm n) : Γ ⊢[PRAAx] value N ≐ factorialValue N := by
  let U := unit N
  let F := Products.fact N
  have hp := positive_product (Γ := Γ) U F (unit_positive N) (factorial_positive N)
  have scale := (GaussianCompactRiemannSplit.fraction_cancel (U*F) (df N) U hp (unit_positive N)).eqSymm
  have numerator : Γ ⊢[PRAAx] (U*F)*df N ≐ Products.fact (two*N) :=
    (mul_comm _ _).eqTrans (df_fact N)
  exact scale.eqTrans (GaussianCompactRiemannName.fraction_congr _ _ _ _ numerator (by dsimp only [U,F]; ipra_ring))

theorem original_half_rising_factorial (N : PTm n) : Γ ⊢[PRAAx]
    risingProduct (oneCode : PTm n) two N ≐ factorialValue N :=
  (original_half_rising N).eqTrans (factorial_formula N)

theorem actual_original_half_integer_rising_factorial_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (risingProduct oneCode two (var 0) ≐ factorialValue (var 0)) := closeUniv 1 (original_half_rising_factorial _)

end LeanProofs.IPRA.Analysis.GaussianGammaHalfRisingFactorial
