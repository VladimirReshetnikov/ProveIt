import IPRADerivations.Analysis.Beta.Endpoints.AllDegrees.GaussianBetaAllDegreeFiniteBinding
import IPRADerivations.Analysis.Euler.PositiveAxis.SharpRates.FiniteEstimates.GaussianEulerSharpFiniteRate

/-!
# The sharp Euler integral comparison at every degree at least two

The same finite reciprocal evaluator uses an inverse height certified
from its finite beta endpoint. This height works even below twice the
disk radius. The original and endpoint-certified heights give equivalent
names on the domain where the original height was certified.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerSharpAllDegrees

open_ipra
open GaussianBetaSharpNaturalDegreeSchedule (source)
open GaussianEulerSharpFiniteRate (improperPoint numerator denominator cofinal_observations_of_finite_binding sharp_bound_of_cofinal)
open GaussianCoefficientNameBounds (unit)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def finitePoint (q z B N : PTm n) : PTm n :=
  ap2 GaussianBetaAllDegreeEulerInverse.nameF q (GaussianBetaAllDegreeEulerInverse.data z B N)

theorem cofinal_observations (t q v q0 z R B A N : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A N) : Γ ⊢[PRAAx]
    distanceBounded (finitePoint q z B N) (improperPoint v z R B A)
      (numerator q v q0 R N*unit t+num 12*denominator q v q0 N) (denominator q v q0 N*unit t) :=
  cofinal_observations_of_finite_binding t q v q0 z R B A N (finitePoint q z B N) h
    (fun p k K => GaussianBetaAllDegreeFiniteBinding.original_finite_euler t p q k z R B A N K
      (.andI h.andE₁ (GaussianBetaSharpNaturalDegreeSchedule.degree_positive z R B A N h)))

theorem original_sharp_bound (q v q0 z R B A N : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A N) : Γ ⊢[PRAAx]
    distanceBounded (finitePoint q z B N) (improperPoint v z R B A)
      (numerator q v q0 R N) (denominator q v q0 N) :=
  sharp_bound_of_cofinal q v q0 R N (finitePoint q z B N) (improperPoint v z R B A)
    (GaussianBetaSharpNaturalDegreeSchedule.degree_positive z R B A N h)
    (fun t => cofinal_observations t q v q0 z R B A N h)

theorem original_sharp_Euler_integral_rate_every_degree_two_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (source (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
        distanceBounded (finitePoint (var 0) (var 3) (var 5) (var 7))
          (improperPoint (var 1) (var 3) (var 4) (var 5) (var 6))
          (numerator (var 0) (var 1) (var 2) (var 4) (var 7))
          (denominator (var 0) (var 1) (var 2) (var 7))) :=
  closeUniv 8 (.impI (original_sharp_bound _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerSharpAllDegrees
