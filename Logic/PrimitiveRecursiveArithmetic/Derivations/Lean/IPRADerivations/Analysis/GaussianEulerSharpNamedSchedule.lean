import IPRADerivations.Analysis.GaussianEulerSharpNamedRate
import IPRADerivations.Analysis.GaussianEulerSharpScheduledApproximation

/-!
# Evaluated sharp Euler degree on an original named complex input

The literal degree uses the original computed input disk U(f,x).
Actual observations of the original finite Euler and Gamma programs at
p+2 are within 2^-p. Only original named regularity and a positive real
margin are assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerSharpNamedSchedule

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNamedRightHalfPlane (source radius)
open GaussianEulerSharpNamedRate (finitePoint gammaPoint)
open GaussianEulerSharpDegreeSchedule (degree degree_positive)
open GaussianEulerSharpScheduleBudget (decayClock mainNumerator mainDenominator main_budget)
open GaussianEulerSharpScheduledApproximation (numerator denominator denominator_positive numerical_rate evaluated_precision_budget)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem degree_guard (f : PR 2) (p x : PTm n) : Γ ⊢[PRAAx] le two (degree p (radius f x)) :=
  le_trans (le_congr (one_mul two) (mul_comm _ _) (mul_le_mul_right two (GaussianNameBounds.U_positive f x)))
    (GaussianEulerSharpScheduleBudget.degree_covers_radius p (radius f x))

theorem original_observations (f : PR 2) (p q v x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) : Γ ⊢[PRAAx]
    distanceBounded (finitePoint f q x A (degree p (radius f x))) (gammaPoint f v x A) (numerator p q v) (denominator p q v) :=
  numerical_rate p q v (mainNumerator p (radius f x)) (mainDenominator p (radius f x)) _ _
    (positive_product _ _ (degree_positive _ _) (GaussianBetaContiguousUpperTailBudget.fixed_denominator_positive _ _))
    (main_budget p (radius f x))
    (GaussianEulerSharpNamedRate.original_sharp_bound f q v (decayClock p (radius f x)) x A (degree p (radius f x))
      (.andI h (degree_guard f p x)))

theorem original_evaluated (f : PR 2) (p x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) : Γ ⊢[PRAAx]
    distanceBounded (finitePoint f (p+num 2) x A (degree p (radius f x))) (gammaPoint f (p+num 2) x A) one (unit p) :=
  GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ _ _
    (denominator_positive p (p+num 2) (p+num 2)) (unit_positive p) (evaluated_precision_budget p)
    (original_observations f p (p+num 2) (p+num 2) x A h)

theorem original_literal_sharp_degree_named_Euler_Gamma_approximation_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source f (var 1) (var 2) ⟶
      distanceBounded (finitePoint f ((var 0)+num 2) (var 1) (var 2) (degree (var 0) (radius f (var 1))))
        (gammaPoint f ((var 0)+num 2) (var 1) (var 2)) one (unit (var 0))) :=
  closeUniv 3 (.impI (original_evaluated f _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerSharpNamedSchedule
