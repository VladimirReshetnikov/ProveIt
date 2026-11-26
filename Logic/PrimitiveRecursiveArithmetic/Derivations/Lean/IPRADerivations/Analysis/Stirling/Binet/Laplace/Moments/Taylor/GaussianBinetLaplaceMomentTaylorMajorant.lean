import IPRADerivations.Analysis.Stirling.Binet.Laplace.Moments.Taylor.GaussianBinetLaplaceMomentTaylorRows
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianCompactScalarMajorant

/-!
# Scalar majorant for the actual Binet Taylor rows

The scalar bound consists of the positive higher moment row times
the squared increment, plus the original dyadic allowance. Its
Gaussian embedding is close to the correspondingly scaled actual
higher-order row, with a uniform error on the compact strip.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentTaylorMajorant

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianBinetLaplaceIntegrand (input)
open GaussianBinetLaplaceMomentFloor (observation)
open GaussianBinetLaplaceMomentFrozenRows (frozen frozen_positive frozen_error frozen_higher_representation)
open GaussianBinetLaplaceMomentTaylorRows (linearObservation leadingNumerator leadingDenominator allowance observation_taylor)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianDominantPairAlgebra (radiusPoint radius_bounded)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open GaussianRationalHorner (qadd qmul qzero qmul_canonical positive_product scalar_congr)
open GaussianRationalMetric (qsub bounded distanceBounded)
open GaussianRationalSumMajorant (majorized from_representation)
open GaussianRationalSyntheticDivision (qmul_congr qadd_congr)
open RationalGaussianEmbedding (embed embed_add embed_multiply canonical_axis_roundtrip)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def coefficient (H Q : PTm n) : PTm n := radiusPoint (num 3*(H*H)) (Q*Q)
def scalar (p j X D T H Q A B : PTm n) : PTm n :=
  RationalArithmetic.add
    (RationalArithmetic.multiply (fraction (num 3*(H*H)) (Q*Q)) (fstT (frozen p (succ (succ j)) X D A B)))
    (fraction (allowance j T) (unit p))
def errorCost (j T : PTm n) : PTm n := allowance j T+num 36*pw T (succ (succ j))

ipra_subst coefficient
ipra_subst scalar
ipra_subst errorCost

theorem leading_denominator_positive (p j X D Q A B : PTm n)
    (hQ : Γ ⊢[PRAAx] le one Q) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] le one (leadingDenominator p j X D Q A B) := by
  have hq := positive_product _ _ hQ hB
  exact positive_product _ _ (RationalArgmin.denominator_positive (fstT (frozen p j X D A B))) (positive_product _ _ hq hq)

theorem scalar_represents (p j X D T H Q A B : PTm n)
    (hQ : Γ ⊢[PRAAx] le one Q) (hB : Γ ⊢[PRAAx] le one B) (hT : Γ ⊢[PRAAx] le A (T*B)) :
    let L := leadingNumerator p j X D H A B
    let E := leadingDenominator p j X D Q A B
    Γ ⊢[PRAAx] RationalArithmetic.represents (scalar p j X D T H Q A B)
      (ZT.ofNat (L*unit p+allowance j T*E)) (E*unit p) := by
  let z := frozen p j X D A B
  let u := fstT (frozen p (succ (succ j)) X D A B)
  let c := fraction (num 3*(H*H)) (Q*Q)
  let v := fraction (allowance j T) (unit p)
  let E := leadingDenominator p j X D Q A B
  let F := GaussianBinetLaplaceDomination.realDenominator z*(B*B)
  have hqq := positive_product _ _ hQ hQ
  have cRep := fraction_represents (num 3*(H*H)) (Q*Q) hqq
  have uRep := frozen_higher_representation p j X D A B T hB hT
  have product := RationalRepresentations.represents_multiply c u _ _ (Q*Q) F cRep uRep
  have raw := RationalRepresentations.represents_add (RationalArithmetic.multiply c u) v _ _ (Q*Q*F) (unit p)
    product (fraction_represents (allowance j T) (unit p) (unit_positive p))
  apply scalar_congr (.eqRefl _) _ _ raw
  · apply ZT.derive
    simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat,LeanProofs.IPRA.Q.mk_mul,LeanProofs.IPRA.Q.mk_add,map_mul,map_add]
    dsimp only [F,E,leadingDenominator,leadingNumerator,z]
    ipra_simps
    ring
  · dsimp only [F,E,leadingDenominator,z]
    ipra_ring

theorem observation_majorant (p j X D R S T H Q A B : PTm n)
    (h : Γ ⊢[PRAAx] input X zero D zero R T A B)
    (h' : Γ ⊢[PRAAx] input (X*Q+H*D) zero (D*Q) zero S T A B)
    (hQ : Γ ⊢[PRAAx] le one Q) (hH : Γ ⊢[PRAAx] le H Q) :
    Γ ⊢[PRAAx] majorized (qsub (observation p j (X*Q+H*D) (D*Q) S T A B) (linearObservation p j X D R T H Q A B))
      (scalar p j X D T H Q A B) := by
  have hB := h.andE₂.andE₁
  have hT := h.andE₂.andE₂
  have hE := leading_denominator_positive p j X D Q A B hQ hB
  have den := positive_product _ _ hE (unit_positive p)
  have rep := scalar_represents p j X D T H Q A B hQ hB hT
  exact from_representation _ _ _ _ den
    (GaussianRationalL1.nonnegative_of_representation _ _ _ den rep) rep
    (observation_taylor p j X D R S T H Q A B h h' hQ hH)

private theorem fraction_radius (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] embed (fraction A B) ≐ radiusPoint A B :=
  (GaussianEulerDecayOrder.fraction_embedding A B hB).eqTrans
    (GaussianEulerDecayFactorBounds.fraction_is_radius_point A B hB)

theorem scalar_embedding (p j X D T H Q A B : PTm n)
    (hQ : Γ ⊢[PRAAx] le one Q) (hB : Γ ⊢[PRAAx] le one B) (hT : Γ ⊢[PRAAx] le A (T*B)) :
    Γ ⊢[PRAAx] embed (scalar p j X D T H Q A B) ≐
      qadd (qmul (coefficient H Q) (frozen p (succ (succ j)) X D A B)) (radiusPoint (allowance j T) (unit p)) := by
  let z := frozen p (succ (succ j)) X D A B
  let c := fraction (num 3*(H*H)) (Q*Q)
  let v := fraction (allowance j T) (unit p)
  have hqq := positive_product _ _ hQ hQ
  have axis := canonical_axis_roundtrip z (qmul_canonical _ _)
    (frozen_positive p (succ (succ j)) X D A B T hB hT).andE₁
  exact (embed_add (RationalArithmetic.multiply c (fstT z)) v).eqTrans
    (qadd_congr ((embed_multiply c (fstT z)).eqTrans (qmul_congr (fraction_radius _ _ hqq) axis))
      (fraction_radius _ _ (unit_positive p)))

theorem coefficient_bound (H Q : PTm n) (hQ : Γ ⊢[PRAAx] le one Q) (hH : Γ ⊢[PRAAx] le H Q) :
    Γ ⊢[PRAAx] bounded (coefficient H Q) (num 3) one := by
  have den := positive_product _ _ hQ hQ
  exact bounded_radius_mono _ _ _ _ _ den (le_refl one) (le_congr (by ipra_ring) (.eqRefl _)
    (le_mul_mono (le_refl (num 3)) (sq_le_sq hH))) (radius_bounded _ _ den)

theorem scalar_observation_distance (p j X D R T H Q A B : PTm n)
    (h : Γ ⊢[PRAAx] input X zero D zero R T A B) (hQ : Γ ⊢[PRAAx] le one Q) (hH : Γ ⊢[PRAAx] le H Q) :
    Γ ⊢[PRAAx] distanceBounded (embed (scalar p j X D T H Q A B))
      (qmul (coefficient H Q) (observation p (succ (succ j)) X D R T A B)) (errorCost j T) (unit p) := by
  let z := frozen p (succ (succ j)) X D A B
  let v := observation p (succ (succ j)) X D R T A B
  let e := radiusPoint (allowance j T) (unit p)
  let c := coefficient H Q
  have hp := unit_positive (Γ := Γ) p
  have δ := distance_symmetric _ _ _ _ hp (frozen_error p (succ (succ j)) X D R T A B h)
  have d := GaussianApproximateInverseDistance.multiply_distance c z v (num 3) (num 12*pw T (succ (succ j)))
    (unit p) hp (coefficient_bound H Q hQ hH) δ
  have add := GaussianNameArithmetic.sum_distance (qmul c z) (qmul c v) e qzero _ _ _ hp d
    ((GaussianReconstructionRoots.distance_zero_iff _ _ _ hp).iffMpr (radius_bounded _ _ hp))
  exact distance_congr (scalar_embedding p j X D T H Q A B hQ h.andE₂.andE₁ h.andE₂.andE₂).eqSymm
    (GaussianRationalLinearProduct.qadd_zero_right _ (qmul_canonical _ _))
    (by unfold errorCost; ipra_ring) (.eqRefl _) add

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentTaylorMajorant
