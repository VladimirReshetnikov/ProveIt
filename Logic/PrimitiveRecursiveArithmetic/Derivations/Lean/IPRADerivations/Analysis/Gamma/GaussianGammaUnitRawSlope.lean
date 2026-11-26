import IPRADerivations.Analysis.Gamma.FunctionalEquations.GaussianGammaUnitShiftedTaylorBound
import IPRADerivations.Analysis.Gamma.GaussianGammaUnitInverseSamples
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalInverseQuadraticAlgebra

/-!
# The original rational Gamma slope at one

The reciprocal Taylor bound and the original Gamma product residual
give a quadratic inverse bound. Division by the actual positive
rational step gives a linear remainder for the original shifted
Gamma sample against the original Euler–Mascheroni observation.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaUnitRawSlope

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaUnitEulerDifference (minimumDenominator denominator_positive)
open GaussianGammaUnitReciprocalShift (step large neighbor)
open GaussianGammaUnitShiftedTaylorBound (cubic cubic_positive original_times_neighbor_cubic)
open GaussianGammaUnitInverseSamples (shiftedSample normBudget residualBudget actual_step_separated)
open GaussianGammaFiniteQuadraticExpansion (gammaPoint)
open GaussianGammaUnitCoefficientMass (budget)
open GaussianRationalUnitInverseExpansion (productResidual directError inverseError boundCoefficient)
open GaussianRationalInverseQuadraticAlgebra
  (cancel_nested_product inverse_quadratic_power inverse_affine_difference subtract_one_sum subtract_zero_difference)
open GaussianRationalHorner (qadd qmul qzero)
open GaussianRationalSyntheticDivision (qone)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalReciprocal (bounded_product bound_congr)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianNamedDifferenceQuotient (inverse actual_inverse inverse_bound scale_distance)
open ComplexLogarithmRemainder (oneCode)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def coefficientNorm : PTm n := GaussianNameBounds.U GaussianGammaCanonicalExponent.gammaF zero
def directBudget : PTm n := budget one+num 12
def slopeBudget : PTm n := boundCoefficient one directBudget coefficientNorm normBudget
def rawSlope (t D : PTm n) : PTm n := qmul (inverse oneCode D) (qsub (shiftedSample t D) qone)
def rawNegative (t : PTm n) : PTm n := qsub qzero (gammaPoint t)

theorem reciprocal_quadratic (t D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hc : Γ ⊢[PRAAx] le (cubic D) (unit t)) : Γ ⊢[PRAAx]
    bounded (directError (large t D) (qmul (step D) (gammaPoint t))) directBudget (D*D) := by
  let inv := inverse oneCode D
  let w := step D
  let c := gammaPoint t
  have sep := actual_step_separated D hD
  have hi : Γ ⊢[PRAAx] qmul inv w ≐ qone := actual_inverse oneCode D sep
  have scale := scale_distance inv _ _ D directBudget (cubic D) (cubic_positive D hD)
    (inverse_bound oneCode D sep) (original_times_neighbor_cubic t D hD hc)
  have converted : Γ ⊢[PRAAx] distanceBounded (large t D) (qadd qone (qmul w c)) (D*directBudget) (cubic D) :=
    distance_congr (cancel_nested_product inv w (large t D) (GaussianGammaC7Name.sample_canonical _ _ _ _) hi)
      (inverse_quadratic_power inv w c hi) (.eqRefl _) (.eqRefl _) scale
  exact bounded_radius_mono _ _ _ _ _ (cubic_positive D hD) (GaussianRationalHorner.positive_product _ _ hD hD)
    (le_of_eq_add (d := zero) (by unfold cubic; ipra_ring))
    (bound_congr (subtract_one_sum (large t D) (qmul w c)).eqSymm (.eqRefl _) (.eqRefl _) converted)

theorem original_raw_slope (s t D : PTm n) (h : Γ ⊢[PRAAx] le (minimumDenominator s) D)
    (hc : Γ ⊢[PRAAx] le (cubic D) (unit t))
    (hr : Γ ⊢[PRAAx] le (residualBudget D*(D*D)) (unit t)) : Γ ⊢[PRAAx]
    distanceBounded (rawSlope t D) (rawNegative t) slopeBudget D := by
  let inv := inverse oneCode D
  let w := step D
  let c := gammaPoint t
  let b := qmul w c
  let g := shiftedSample t D
  have hD := denominator_positive s D h
  have d2 := GaussianRationalHorner.positive_product _ _ hD hD
  have sep := actual_step_separated D hD
  have residual : Γ ⊢[PRAAx] bounded (productResidual g (large t D)) one (D*D) :=
    bounded_radius_mono _ _ _ _ _ (unit_positive t) d2 (le_congr (.eqRefl _) (by ipra_ring) hr)
      (GaussianGammaUnitInverseSamples.original_residual s t D h)
  have coeff : Γ ⊢[PRAAx] bounded c coefficientNorm one :=
    GaussianNameBounds.sample_bound _ _ t (GaussianGammaCanonicalExponent.gamma_regular (Γ := Γ))
  have stepNorm := GaussianGammaUnitEulerDifference.increment_bound D D hD (le_refl _)
  have linear : Γ ⊢[PRAAx] bounded b coefficientNorm D :=
    bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring) (bounded_product _ _ _ _ _ _ hD (le_refl one) stepNorm coeff)
  have approx := GaussianRationalUnitInverseExpansion.original_quadratic_bound g (large t D) b D one directBudget
    coefficientNorm normBudget hD residual (reciprocal_quadratic t D hD hc) linear
    (GaussianGammaUnitInverseSamples.original_shifted_norm s t D h)
  have scaled := bounded_product inv _ D one slopeBudget (D*D) (le_refl one) d2 (inverse_bound oneCode D sep) approx
  have invLaw : Γ ⊢[PRAAx] qmul inv w ≐ qone := actual_inverse oneCode D sep
  have cCan : Γ ⊢[PRAAx] GaussianRationalHorner.canonical c :=
    RationalGaussianNameEmbedding.sample_canonical _ t _
  have equal : Γ ⊢[PRAAx] qmul inv (inverseError g b) ≐ qsub (rawSlope t D) (rawNegative t) :=
    (inverse_affine_difference inv w g c cCan invLaw).eqTrans (subtract_zero_difference (rawSlope t D) c).eqSymm
  exact bounded_radius_mono _ _ _ _ _ (GaussianRationalHorner.positive_product _ _ (le_refl one) d2) hD
    (le_of_eq_add (d := zero) (by ipra_ring))
    (bound_congr equal (.eqRefl _) (.eqRefl _) scaled)

end LeanProofs.IPRA.Analysis.GaussianGammaUnitRawSlope
