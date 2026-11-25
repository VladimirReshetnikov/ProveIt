import IPRADerivations.Analysis.GaussianNamedDifferenceQuotient
import IPRADerivations.Analysis.GaussianInverseBinomialRows

/-!
# Inverse coefficients for the negative Gamma shift product

These identities accept verified inverses of the endpoint products. They
apply to the original pole multipliers and give the finite difference
needed to differentiate the normalized product with the terminal Gamma.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeProductDerivativeInverse

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalDistanceOrder (distance_congr distance_triangle_same)
open GaussianRationalHorner (canonical canonical_unique positive_product qmul represents_congr)
open GaussianRationalL1 (rawGaussian rawDen raw_den_positive raw_represents)
open GaussianRationalMetric (bounded distanceBounded qnegative qnegative_canonical qnegative_represents qsub qsub_canonical qsub_represents)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (bound_congr bounded_negative bounded_product)
open GaussianRationalSyntheticDivision (qmul_congr qsub_congr qone rescale_to)
open GaussianReciprocalHorner (qmul_associative qmul_one_right)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def inverseCoefficient (c1 c0 pDelta : PTm n) : PTm n := qmul (qmul c1 c0) (qnegative pDelta)

@[simp] theorem subst_inverseCoefficient {m : ℕ} (σ : Fin n → PTm m) (c1 c0 pDelta : PTm n) :
    Syn.subst σ (inverseCoefficient c1 c0 pDelta) =
      inverseCoefficient (Syn.subst σ c1) (Syn.subst σ c0) (Syn.subst σ pDelta) := by
  simp [inverseCoefficient]

private theorem reverse_difference (a b : PTm n) : Γ ⊢[PRAAx] qsub b a ≐ qnegative (qsub a b) := by
  let A := rawGaussian a
  let B := rawGaussian b
  let D := rawDen a*rawDen b
  have hp : Γ ⊢[PRAAx] le one D := positive_product _ _ (raw_den_positive a) (raw_den_positive b)
  have ha := rescale_to a A (rawDen a) (rawDen b) D (raw_represents (Γ := Γ) a) (.eqRefl D)
  have hb := rescale_to b B (rawDen b) (rawDen a) D (raw_represents (Γ := Γ) b) (mul_comm _ _)
  have right := qnegative_represents _ _ _ (qsub_represents _ _ _ _ D hp ha hb)
  have left := qsub_represents _ _ _ _ D hp hb ha
  apply canonical_unique _ _ _ D (qsub_canonical _ _) (qnegative_canonical _) hp left
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := right)
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [GaussianRootAlgebra.re_neg, GaussianRootAlgebra.im_neg,
      GaussianRootAlgebra.re_sub, GaussianRootAlgebra.im_sub] <;> ring

theorem inverse_gap (p1 p0 c1 c0 : PTm n)
    (hc1 : Γ ⊢[PRAAx] canonical c1) (hc0 : Γ ⊢[PRAAx] canonical c0)
    (hi1 : Γ ⊢[PRAAx] qmul p1 c1 ≐ qone) (hi0 : Γ ⊢[PRAAx] qmul p0 c0 ≐ qone) :
    Γ ⊢[PRAAx] qsub c1 c0 ≐ inverseCoefficient c1 c0 (qsub p1 p0) := by
  let k := qmul c1 c0
  have e1 : Γ ⊢[PRAAx] qmul k p0 ≐ c1 :=
    (qmul_associative c1 c0 p0).eqTrans
      ((qmul_congr (.eqRefl _) ((qmul_commutative c0 p0).eqTrans hi0)).eqTrans (qmul_one_right c1 hc1))
  have e0 : Γ ⊢[PRAAx] qmul k p1 ≐ c0 :=
    (qmul_congr (qmul_commutative c1 c0) (.eqRefl _)).eqTrans
      ((qmul_associative c0 c1 p1).eqTrans
        ((qmul_congr (.eqRefl _) ((qmul_commutative c1 p1).eqTrans hi1)).eqTrans (qmul_one_right c0 hc0)))
  exact (qsub_congr e1.eqSymm e0.eqSymm).eqTrans
    ((GaussianRationalRoundedPower.multiplication_difference k p0 p1).eqTrans
      (qmul_congr (.eqRefl _) (reverse_difference p1 p0)))

theorem inverse_coefficient_difference (p1 p0 c1 c0 delta pDelta : PTm n)
    (hc1 : Γ ⊢[PRAAx] canonical c1) (hc0 : Γ ⊢[PRAAx] canonical c0)
    (hi1 : Γ ⊢[PRAAx] qmul p1 c1 ≐ qone) (hi0 : Γ ⊢[PRAAx] qmul p0 c0 ≐ qone)
    (hGap : Γ ⊢[PRAAx] qsub p1 p0 ≐ qmul delta pDelta) :
    Γ ⊢[PRAAx] qsub c1 c0 ≐ qmul delta (inverseCoefficient c1 c0 pDelta) := by
  let k := qmul c1 c0
  have flip : Γ ⊢[PRAAx] qnegative (qsub p1 p0) ≐ qmul (qnegative pDelta) delta :=
    (GaussianInverseBinomialRows.negative_congr (hGap.eqTrans (qmul_commutative delta pDelta))).eqTrans
      (GaussianInverseBinomialRows.negative_product pDelta delta)
  exact (inverse_gap p1 p0 c1 c0 hc1 hc0 hi1 hi0).eqTrans
    ((qmul_congr (.eqRefl k) flip).eqTrans
      ((qmul_associative k (qnegative pDelta) delta).eqSymm.eqTrans (qmul_commutative _ _)))

theorem inverse_gap_bound (p1 p0 c1 c0 H A D : PTm n)
    (hc1 : Γ ⊢[PRAAx] canonical c1) (hc0 : Γ ⊢[PRAAx] canonical c0)
    (hi1 : Γ ⊢[PRAAx] qmul p1 c1 ≐ qone) (hi0 : Γ ⊢[PRAAx] qmul p0 c0 ≐ qone)
    (hb1 : Γ ⊢[PRAAx] bounded c1 H one) (hb0 : Γ ⊢[PRAAx] bounded c0 H one)
    (hD : Γ ⊢[PRAAx] le one D) (hd : Γ ⊢[PRAAx] distanceBounded p1 p0 A D) :
    Γ ⊢[PRAAx] distanceBounded c1 c0 (H*H*A) D := by
  have hProduct : Γ ⊢[PRAAx] bounded (qmul c1 c0) (H*H) one :=
    bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring)
      (bounded_product c1 c0 H one H one (le_refl _) (le_refl _) hb1 hb0)
  exact bound_congr (inverse_gap p1 p0 c1 c0 hc1 hc0 hi1 hi0).eqSymm (.eqRefl _) (by ipra_ring)
    (bounded_product (qmul c1 c0) (qnegative (qsub p1 p0)) (H*H) one A D
      (le_refl _) hD hProduct (bounded_negative _ _ _ hD hd))

/-- The same denominator can measure both the product derivative error
and the displacement of the original endpoint coefficient. -/
theorem inverse_coefficient_rate (c1 c0 pDelta pPrime H V A B D : PTm n)
    (hb1 : Γ ⊢[PRAAx] bounded c1 H one) (hb0 : Γ ⊢[PRAAx] bounded c0 H one)
    (hp : Γ ⊢[PRAAx] bounded pPrime V one) (hD : Γ ⊢[PRAAx] le one D)
    (hd : Γ ⊢[PRAAx] distanceBounded pDelta pPrime A D)
    (hc : Γ ⊢[PRAAx] distanceBounded c1 c0 B D) :
    Γ ⊢[PRAAx] distanceBounded (inverseCoefficient c1 c0 pDelta) (inverseCoefficient c0 c0 pPrime)
      (H*H*A+V*(H*B)) D := by
  let k := qmul c1 c0
  let k0 := qmul c0 c0
  let v := qnegative pPrime
  have hk : Γ ⊢[PRAAx] bounded k (H*H) one :=
    bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring)
      (bounded_product c1 c0 H one H one (le_refl _) (le_refl _) hb1 hb0)
  have hv := bounded_negative pPrime V one (le_refl _) hp
  have scale := GaussianNamedDifferenceQuotient.scale_distance k _ _ (H*H) A D hD hk
    (GaussianNamedDifference.negative_distance _ _ _ _ hD hd)
  have gap : Γ ⊢[PRAAx] distanceBounded k k0 (H*B) D :=
    distance_congr (qmul_commutative c0 c1) (.eqRefl _) (.eqRefl _) (.eqRefl _)
      (GaussianNamedDifferenceQuotient.scale_distance c0 _ _ H B D hD hb0 hc)
  have shift := distance_congr (qmul_commutative v k) (qmul_commutative v k0) (.eqRefl _) (.eqRefl _)
    (GaussianNamedDifferenceQuotient.scale_distance v _ _ V (H*B) D hD hv gap)
  exact distance_triangle_same _ _ _ _ _ _ hD scale shift

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeProductDerivativeInverse
