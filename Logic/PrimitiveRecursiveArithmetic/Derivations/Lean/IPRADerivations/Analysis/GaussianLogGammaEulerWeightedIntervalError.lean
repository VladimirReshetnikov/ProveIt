import IPRADerivations.Analysis.GaussianLogGammaEulerLinearIntervalError
import IPRADerivations.Analysis.GaussianLogGammaEulerNormalizedDifference
import IPRADerivations.Analysis.GaussianNamedSmallPerturbationTransport
import IPRADerivations.Analysis.GaussianApproximateInverseDistance

/-!
# The actual weighted logarithm interval of the normalized Euler head

The named product computes the original signed Gaussian input times the
difference of the two actual positive-rational logarithms. Its deviation
from the exact sum of the interval's linear rows is at most R/N plus an
explicit observation allowance, uniformly over the interval length.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerWeightedIntervalError

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerLinearInterval (harmonicInterval linearSum exact_sum)
open GaussianLogGammaEulerNormalizedDifference (weightedLogF weightedLogData)
open GaussianLogGammaEulerResidualDomain (native source)
open GaussianNamedSmallPerturbationTransport (productClock product_at)
open GaussianPositiveRationalLogarithm (logF data name_regular)
open GaussianPositiveRationalLogarithmIncrement (increment)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (qmul positive_product ofGaussian_represents)
open GaussianRationalMetric (bounded bounded_of_cleared distanceBounded)
open GaussianRationalSyntheticDivision (qmul_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private def logarithmDifferenceF : PR 2 := GaussianNamedDifference.nameF logF logF

private def logarithmDifferenceData (N r : PTm n) : PTm n :=
  GaussianNamedDifference.data (data (N+r) one) (data N one)

def errorNumerator (p R N : PTm n) : PTm n := R*(unit p+num 8*N)
def errorDenominator (p N : PTm n) : PTm n := N*unit p

theorem argument_bound (A B D neg R : PTm n) (h : Γ ⊢[PRAAx] source A B D neg R) :
    Γ ⊢[PRAAx] bounded (argument A B D neg) R one := by
  have hD := h.andE₁.andE₂
  exact bounded_of_cleared _ (native A B neg) D R one hD (le_refl one)
    (ofGaussian_represents (native A B neg) D hD)
    (le_congr (by ipra_ring) (by ipra_ring) h.andE₂)

private theorem logarithm_difference_at (p N r : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 logarithmDifferenceF p (logarithmDifferenceData N r)) (harmonicInterval N r)
      (unit p+num 8*N) (N*unit p) := by
  let P := unit p
  let E := N*P
  let z := increment p p N one r
  have hp : Γ ⊢[PRAAx] le one P := unit_positive p
  have hE : Γ ⊢[PRAAx] le one E := positive_product _ _ hN hp
  have hPP : Γ ⊢[PRAAx] le one (P*P) := positive_product _ _ hp hp
  have raw := GaussianNamedDifference.sample_error logF logF (data (N+r) one) (data N one) p
    (name_regular (N+r) one (.andI (le_trans hN (le_add_right N r)) (le_refl one)))
    (name_regular N one (.andI hN (le_refl one)))
  have named : Γ ⊢[PRAAx] distanceBounded (ap2 logarithmDifferenceF p (logarithmDifferenceData N r)) z
      (num 6*N) E :=
    distance_radius_mono _ _ _ _ _ _ hp hE
      (le_of_eq_add (d := zero) (by dsimp only [E]; ipra_ring)) raw
  have exact : Γ ⊢[PRAAx] distanceBounded z (harmonicInterval N r) (P+two*N) E :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hN hPP) hE
      (le_of_eq_add (d := zero) (by
        dsimp only [E,P,GaussianLogGammaEulerLinearIntervalError.errorNumerator,
          GaussianLogGammaEulerLinearIntervalError.errorDenominator]
        ipra_ring)) (GaussianLogGammaEulerLinearIntervalError.logarithms_at p p N r hN)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [P]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hE named exact)

/-- The actual product at its internal query reduces to the fixed signed
argument multiplied by the actual normalized logarithm difference. -/
theorem sample_at (p A B D neg N r : PTm n) :
    Γ ⊢[PRAAx] ap2 weightedLogF p (weightedLogData A B D neg N r) ≐
      qmul (argument A B D neg)
        (ap2 logarithmDifferenceF
          (productClock constantF logarithmDifferenceF (argument A B D neg) (logarithmDifferenceData N r) p)
          (logarithmDifferenceData N r)) := by
  let z := argument A B D neg
  let d := logarithmDifferenceData N r
  exact (product_at constantF logarithmDifferenceF z d p).eqTrans
    (qmul_congr (constant_at (productClock constantF logarithmDifferenceF z d p) z) (.eqRefl _))

/-- The weighted logarithm interval is within R/N+8R/2^p of the exact
Gaussian-rational sum of its linear rows. -/
theorem sample_error (p A B D neg R N r : PTm n) (h : Γ ⊢[PRAAx] source A B D neg R)
    (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 weightedLogF p (weightedLogData A B D neg N r))
      (linearSum A B D neg N r) (errorNumerator p R N) (errorDenominator p N) := by
  let z := argument A B D neg
  let d := logarithmDifferenceData N r
  let k := productClock constantF logarithmDifferenceF z d p
  have hK : Γ ⊢[PRAAx] le one (N*unit k) := positive_product _ _ hN (unit_positive k)
  have raw := GaussianApproximateInverseDistance.multiply_distance z _ _ _ _ _ hK
    (argument_bound A B D neg R h) (logarithm_difference_at k N r hN)
  have lifted := distance_congr (sample_at p A B D neg N r).eqSymm (exact_sum A B D neg N r).eqSymm
    (.eqRefl _) (.eqRefl _) raw
  have later : Γ ⊢[PRAAx] le (unit p) (unit k) :=
    GaussianFactorBudget.power_monotone_length two p k (le_succ_self one) (le_add_right _ _)
  have extra := mul_le_mul_right (num 8*R*N*N) later
  have budget : Γ ⊢[PRAAx] le (R*(unit k+num 8*N)*(N*unit p)) (R*(unit p+num 8*N)*(N*unit k)) :=
    le_congr (by ipra_ring) (by ipra_ring) (add_le_add₂ (le_refl (R*N*unit p*unit k)) extra)
  exact distance_radius_mono _ _ _ _ _ _ hK (positive_product _ _ hN (unit_positive p)) budget lifted

theorem actual_weighted_Euler_logarithm_interval_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (source (var 1) (var 2) (var 3) (var 4) (var 5) ⟶ le one (var 6) ⟶
        distanceBounded (ap2 weightedLogF (var 0) (weightedLogData (var 1) (var 2) (var 3) (var 4) (var 6) (var 7)))
          (linearSum (var 1) (var 2) (var 3) (var 4) (var 6) (var 7))
          (errorNumerator (var 0) (var 5) (var 6)) (errorDenominator (var 0) (var 6))) :=
  closeUniv 8 (.impI (.impI (sample_error _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerWeightedIntervalError
