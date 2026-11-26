import IPRADerivations.Analysis.Stirling.Raabe.GaussianRaabeRightSide
import IPRADerivations.Analysis.Stirling.Raabe.GaussianRaabeLogPrimitiveRescale
import IPRADerivations.Analysis.Stirling.Raabe.GaussianRaabeStirlingRemainder

/-!
# The Raabe right side at the encoded unit argument
-/

set_option autoImplicit false
set_option maxHeartbeats 760000

namespace LeanProofs.IPRA.Analysis.GaussianRaabeAtOne

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameArithmetic (sum_distance)
open GaussianPositiveRationalLogarithm (fraction sample)
open GaussianRaabeLogPrimitiveCell (primitive)
open GaussianRaabeStirlingRemainder (constantSample)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (qadd qzero positive_product)
open GaussianRationalMetric (distanceBounded qnegative qsub qnegative_canonical)
open GaussianRationalPowerDifference (distance_refl_zero)
open GaussianRationalSyntheticDivision (qmul_congr qsub_congr qone qzero_add)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem primitive_at_unit (p E : PTm n) (he : Γ ⊢[PRAAx] le one E) :
    Γ ⊢[PRAAx] distanceBounded (primitive p E E) (qnegative qone) (num 10) (unit p) := by
  let U := unit p
  let l := sample p one one
  let t : PTm n := qnegative qone
  let v := primitive p one one
  have hu := unit_positive (Γ := Γ) p
  have one_at : Γ ⊢[PRAAx] fraction (one : PTm n) one ≐ qone :=
    (GaussianEulerDecayFactorBounds.fraction_is_radius_point one one (le_refl one)).eqTrans
      GaussianDominantPairAlgebra.radius_one
  have primitive_read : Γ ⊢[PRAAx] v ≐ qadd l t :=
    qsub_congr ((qmul_congr one_at (.eqRefl l)).eqTrans
      (GaussianPolynomialDeterminantTerms.one_mul_canonical l (GaussianPositiveRationalLogarithm.sample_canonical p one one))) one_at
  have log := GaussianCompactLogarithmBounds.sample_one_bound (Γ := Γ) p
  have near : Γ ⊢[PRAAx] distanceBounded v t (num 8) U :=
    distance_congr primitive_read.eqSymm (qzero_add t (qnegative_canonical qone)) (add_zero _) (.eqRefl _)
      (sum_distance l qzero t t (num 8) zero U hu log (distance_refl_zero t U hu))
  have same := GaussianRaabeLogPrimitiveRescale.equal_ratio p p E E one one
    (.andI he he) (.andI (le_refl one) (le_refl one)) (.eqRefl _)
  have rescale : Γ ⊢[PRAAx] distanceBounded (primitive p E E) v two U :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ he (positive_product _ _ hu hu)) hu
      (le_of_eq_add (d := zero) (by ipra_ring)) same
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hu rescale near)

theorem right_side_at_unit (p E w : PTm n) (he : Γ ⊢[PRAAx] le one E) :
    Γ ⊢[PRAAx] distanceBounded (ap2 GaussianRaabeRightSide.nameF p (GaussianRaabeRightSide.data E E w))
      (qsub (constantSample p w) qone) (GaussianRaabeRightSide.cost E+num 10) (unit p) := by
  let c := constantSample p w
  let t : PTm n := qnegative qone
  let x := primitive p E E
  let U := unit p
  have hu := unit_positive (Γ := Γ) p
  have base := GaussianRaabeRightSide.sample_error p E E w (.andI he he)
  have next : Γ ⊢[PRAAx] distanceBounded (qadd x c) (qsub c qone) (num 10) U :=
    distance_congr (.eqRefl _) (GaussianReciprocalHorner.qadd_commutative t c) (add_zero _) (.eqRefl _)
      (sum_distance x t c c (num 10) zero U hu (primitive_at_unit p E he) (distance_refl_zero c U hu))
  exact distance_triangle_same _ _ _ _ _ _ hu base next

end LeanProofs.IPRA.Analysis.GaussianRaabeAtOne
