import IPRADerivations.Analysis.Stirling.Binet.Bose.CompactIntegrand.GaussianBinetBoseDenominator
import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.ImageGrids.Lattice.GaussianEulerPositivePowerChartCorrectedImage

/-!
# Contractive ratio of each original positive exponential sample

For every actual positive Pi-scaled exponential sample, the first two
Taylor terms give the lower margin `1+4t`. The exact rational inverse
therefore has norm at most `1/(1+4t)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 550000

namespace LeanProofs.IPRA.Analysis.GaussianBinetBoseGeometricRatio

open_ipra
open GaussianBinetBoseExponential (scaleF scaleData scale_positive scale_lower_order expF expData expRadius)
open GaussianDominantPairAlgebra (radiusPoint radius_one)
open GaussianEulerDecayFactorBounds (fraction_is_radius_point)
open GaussianExponentialAffineLower (affine_prefix lower_of_real_order)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRadiusExponentialName (index inputPrecision sample_at)
open GaussianRationalExponentialTail (scalarPrefix)
open GaussianRationalHorner (qadd qmul canonical positive_product)
open GaussianRationalLowerBounds (lower)
open GaussianRationalMetric (bounded)
open GaussianRationalPolynomialExponential (scalarSum scalarBody)
open GaussianRationalReciprocal (reciprocal)
open GaussianRationalSyntheticDivision (qone qadd_congr)
open RationalArgmin (rationalLE_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem one_plus_fraction (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] qadd qone (radiusPoint A B) ≐ radiusPoint (B+A) B := by
  have oneEq := (fraction_is_radius_point (Γ := Γ) one one (le_refl one)).eqTrans radius_one
  exact (qadd_congr oneEq.eqSymm (fraction_is_radius_point A B hB).eqSymm).eqTrans
    ((GaussianEulerPositivePowerChartCorrectedImage.fraction_sum one one A B (le_refl one) hB).eqTrans
      ((GaussianCompactRiemannName.fraction_congr _ _ _ _ (by ipra_ring) (one_mul B)).eqTrans
        (fraction_is_radius_point (B+A) B hB)))

theorem positive_lower (p A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] lower (ap2 expF p (expData false A B)) (B+num 4*A) B := by
  let R := expRadius A
  let j := inputPrecision R p
  let u := radiusPoint (num 4*A) B
  let q := ap2 scaleF j (scaleData false A B)
  let K := index R p
  let x := ap2 expF p (expData false A B)
  have s := scale_positive j A B hB
  have hu := GaussianPositiveExponentialTermBound.actual_positive_fraction (num 4*A) B hB
  have hc : Γ ⊢[PRAAx] canonical u := GaussianRationalHorner.ofGaussian_canonical _ _ hB
  have hK : Γ ⊢[PRAAx] le one K := GaussianPositiveExponentialSeparation.original_cutoff_positive R p
  have read : Γ ⊢[PRAAx] x ≐ scalarSum q K := sample_at scaleF R p (scaleData false A B)
  have affine : Γ ⊢[PRAAx] scalarSum u one ≐ radiusPoint (B+num 4*A) B :=
    (affine_prefix u hc).eqTrans (one_plus_fraction (num 4*A) B hB)
  have order := GaussianPositiveExponentialOrder.argument_and_cutoff_monotone u q one K hu s.andE₁
    (scale_lower_order j A B hB) hK
  exact lower_of_real_order x (B+num 4*A) B
    (GaussianPositiveRealArithmetic.positive_congr read.eqSymm
      (GaussianPositiveExponentialProduct.positive_scalar_sum q K s.andE₁))
    (GaussianRadiusExponentialName.sample_canonical scaleF R p (scaleData false A B)) hB
    (rationalLE_congr (congrFst affine) (congrFst read).eqSymm order)

theorem inverse_pair (p A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] qmul (ap2 expF p (expData false A B)) (reciprocal (ap2 expF p (expData false A B))) ≐ qone := by
  let x := ap2 expF p (expData false A B)
  have positive : Γ ⊢[PRAAx] le one (B+num 4*A) := le_trans hB (le_add_right B _)
  exact GaussianRationalLowerBounds.reciprocal_identity_of_lower x (B+num 4*A) B positive hB (positive_lower p A B hB)

theorem inverse_bound (p A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] bounded (reciprocal (ap2 expF p (expData false A B))) B (B+num 4*A) :=
  GaussianRationalLowerBounds.inverse_bound _ _ _ (le_trans hB (le_add_right B _)) hB (positive_lower p A B hB)

end LeanProofs.IPRA.Analysis.GaussianBinetBoseGeometricRatio
