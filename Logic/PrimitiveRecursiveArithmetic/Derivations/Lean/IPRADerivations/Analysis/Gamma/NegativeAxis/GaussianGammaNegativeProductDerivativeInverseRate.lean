import IPRADerivations.Analysis.Gamma.NegativeAxis.GaussianGammaNegativeProductDerivativeInverse
import IPRADerivations.Analysis.Gamma.NegativeAxis.GaussianGammaNegativeProductDerivativeQuotient
import IPRADerivations.Analysis.LinearAlgebra.GaussianDeterminantSignTransport

/-!
# Uniform rate for the inverse negative Gamma shift coefficient

The actual first coefficient of the shift product identifies the diagonal
inverse coefficient as the inverse multiplier times the signed reciprocal
correction. The bound is uniform in the two fractional coordinates,
given a common bound for their verified inverse multipliers.
-/

set_option autoImplicit false
set_option maxHeartbeats 1700000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeProductDerivativeInverseRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaDigammaTwoShiftFiniteRate (fraction_bound)
open GaussianGammaNegativeCriticalCorrection (correction guard)
open GaussianGammaNegativeProductDerivative (dividedDifference firstCoefficient original_product_gap prefixDifference)
open GaussianGammaNegativeProductDerivativeCorrection (original_first_coefficient)
open GaussianGammaNegativeProductDerivativeInverse (inverseCoefficient inverse_gap_bound inverse_coefficient_rate)
open GaussianGammaNegativeProductDerivativeQuotient (shiftProduct step)
open GaussianGammaNegativeProductDerivativeRate (coefficientCap productCap derivativeCost prefix_bounds derivative_error)
open GaussianInverseBinomialRows (negative_congr negative_product)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same)
open GaussianRationalHorner (canonical qmul)
open GaussianRationalMetric (bounded distanceBounded qnegative qsub_canonical)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalPowerDifference (bounded_sum_same distance_refl_zero)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalSyntheticDivision (qmul_congr qone)
open GaussianReciprocalHorner (qmul_associative qmul_one_right)
open GaussianReconstructionRoots (distance_zero_iff norm_from_distance)
open GaussianStirlingGammaLogarithm (arg)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def firstCap (j : PTm n) : PTm n := coefficientCap j j+productCap j j

def dividedCap (j : PTm n) : PTm n := two*derivativeCost j+firstCap j

def inverseGapCost (j H : PTm n) : PTm n := H*H*dividedCap j

def inverseRateCost (j H : PTm n) : PTm n :=
  H*H*derivativeCost j+firstCap j*(H*inverseGapCost j H)

@[simp] theorem subst_firstCap {m : ℕ} (σ : Fin n → PTm m) (j : PTm n) :
    Syn.subst σ (firstCap j) = firstCap (Syn.subst σ j) := by simp [firstCap]

@[simp] theorem subst_dividedCap {m : ℕ} (σ : Fin n → PTm m) (j : PTm n) :
    Syn.subst σ (dividedCap j) = dividedCap (Syn.subst σ j) := by simp [dividedCap,two]

@[simp] theorem subst_inverseGapCost {m : ℕ} (σ : Fin n → PTm m) (j H : PTm n) :
    Syn.subst σ (inverseGapCost j H) = inverseGapCost (Syn.subst σ j) (Syn.subst σ H) := by
  simp [inverseGapCost]

@[simp] theorem subst_inverseRateCost {m : ℕ} (σ : Fin n → PTm m) (j H : PTm n) :
    Syn.subst σ (inverseRateCost j H) = inverseRateCost (Syn.subst σ j) (Syn.subst σ H) := by
  simp [inverseRateCost]

private theorem endpoint_bound (a b : PTm n) (ha : Γ ⊢[PRAAx] guard a b) : Γ ⊢[PRAAx]
    bounded (fraction a b) one one :=
  fraction_bound a b one (le_trans ha.andE₁ (le_of_lt ha.andE₂))
    (le_congr (.eqRefl _) (one_mul b).eqSymm (le_of_lt ha.andE₂))

theorem first_bounded (a b j : PTm n) (ha : Γ ⊢[PRAAx] guard a b) : Γ ⊢[PRAAx]
    bounded (firstCoefficient (arg a) b j) (firstCap j) one := by
  have h := prefix_bounds a a b j ConciseIPRA.PTm.zero one j ha ha (le_refl one)
    (distance_refl_zero (fraction a b) one (le_refl one)) (le_refl j)
  have factor : Γ ⊢[PRAAx] bounded
      (qmul (prefixDifference (arg a) (arg a) b j) (fraction a b)) (coefficientCap j j) one :=
    bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring)
      (bounded_product _ _ (coefficientCap j j) one one one
      (le_refl _) (le_refl _) h.andE₂.andE₁ (endpoint_bound a b ha))
  exact bounded_sum_same _ _ _ _ _ (le_refl one) factor h.andE₁

theorem divided_bounded (a c b j : PTm n) (ha : Γ ⊢[PRAAx] guard a b) (hc : Γ ⊢[PRAAx] guard c b) : Γ ⊢[PRAAx]
    bounded (dividedDifference (arg a) (arg c) b j) (dividedCap j) one := by
  have left := (distance_zero_iff (fraction c b) one one (le_refl one)).iffMpr (endpoint_bound c b hc)
  have right := (distance_zero_iff (fraction a b) one one (le_refl one)).iffMpr (endpoint_bound a b ha)
  have hs : Γ ⊢[PRAAx] distanceBounded (fraction c b) (fraction a b) two one :=
    distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
      (distance_triangle_same _ _ _ _ _ _ (le_refl one) left (distance_symmetric _ _ _ _ (le_refl one) right))
  have e := derivative_error a c b j two one ha hc (le_refl one) hs
  exact bound_congr (.eqRefl _) (by unfold dividedCap; ipra_ring) (by ipra_ring)
    (norm_from_distance _ _ _ _ _ _ (le_refl one) (le_refl one) e (first_bounded a b j ha))

theorem shift_product_gap_bound (a c b N A D : PTm n)
    (ha : Γ ⊢[PRAAx] guard a b) (hc : Γ ⊢[PRAAx] guard c b) (hD : Γ ⊢[PRAAx] le one D)
    (hStep : Γ ⊢[PRAAx] distanceBounded (fraction c b) (fraction a b) A D) : Γ ⊢[PRAAx]
    distanceBounded (shiftProduct c b N) (shiftProduct a b N) (dividedCap (succ N)*A) D := by
  have eq := original_product_gap (arg a) (arg c) b (succ N) (le_trans ha.andE₁ (le_of_lt ha.andE₂))
  exact bound_congr eq.eqSymm (by ipra_ring) (by ipra_ring)
    (bounded_product (step a c b) _ A D (dividedCap (succ N)) one hD (le_refl one)
      hStep (divided_bounded a c b (succ N) ha hc))

theorem original_inverse_diagonal (a b N c : PTm n) (ha : Γ ⊢[PRAAx] guard a b)
    (hc : Γ ⊢[PRAAx] canonical c) (hi : Γ ⊢[PRAAx] qmul (shiftProduct a b N) c ≐ qone) :
    Γ ⊢[PRAAx] inverseCoefficient c c (firstCoefficient (arg a) b (succ N)) ≐
      qmul c (correction a b N) := by
  let P := shiftProduct a b N
  let R := correction a b N
  let F := firstCoefficient (arg a) b (succ N)
  have p : Γ ⊢[PRAAx] qnegative F ≐ qmul P R :=
    (negative_congr ((original_first_coefficient a b N ha).eqTrans (qmul_commutative P (qnegative R)))).eqTrans
      ((negative_product (qnegative R) P).eqTrans
        ((qmul_congr (GaussianDeterminantSignTransport.negative_involution R (qsub_canonical _ _)) (.eqRefl _)).eqTrans
          (qmul_commutative R P)))
  have cP : Γ ⊢[PRAAx] qmul (qmul c c) P ≐ c :=
    (qmul_associative c c P).eqTrans
      ((qmul_congr (.eqRefl _) ((qmul_commutative c P).eqTrans hi)).eqTrans (qmul_one_right c hc))
  exact (qmul_congr (.eqRefl _) p).eqTrans
    ((qmul_associative (qmul c c) P R).eqSymm.eqTrans (qmul_congr cP (.eqRefl _)))

theorem original_inverse_gap_bound (a c b N c1 c0 H A D : PTm n)
    (ha : Γ ⊢[PRAAx] guard a b) (hc : Γ ⊢[PRAAx] guard c b)
    (hc1 : Γ ⊢[PRAAx] canonical c1) (hc0 : Γ ⊢[PRAAx] canonical c0)
    (hi1 : Γ ⊢[PRAAx] qmul (shiftProduct c b N) c1 ≐ qone)
    (hi0 : Γ ⊢[PRAAx] qmul (shiftProduct a b N) c0 ≐ qone)
    (hb1 : Γ ⊢[PRAAx] bounded c1 H one) (hb0 : Γ ⊢[PRAAx] bounded c0 H one)
    (hD : Γ ⊢[PRAAx] le one D)
    (hStep : Γ ⊢[PRAAx] distanceBounded (fraction c b) (fraction a b) A D) : Γ ⊢[PRAAx]
    distanceBounded c1 c0 (inverseGapCost (succ N) H*A) D := by
  have hProduct := shift_product_gap_bound a c b N A D ha hc hD hStep
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold inverseGapCost; ipra_ring) (.eqRefl _)
    (inverse_gap_bound _ _ c1 c0 H (dividedCap (succ N)*A) D hc1 hc0 hi1 hi0 hb1 hb0 hD hProduct)

theorem original_inverse_coefficient_rate (a c b N c1 c0 H A D : PTm n)
    (ha : Γ ⊢[PRAAx] guard a b) (hc : Γ ⊢[PRAAx] guard c b)
    (hc1 : Γ ⊢[PRAAx] canonical c1) (hc0 : Γ ⊢[PRAAx] canonical c0)
    (hi1 : Γ ⊢[PRAAx] qmul (shiftProduct c b N) c1 ≐ qone)
    (hi0 : Γ ⊢[PRAAx] qmul (shiftProduct a b N) c0 ≐ qone)
    (hb1 : Γ ⊢[PRAAx] bounded c1 H one) (hb0 : Γ ⊢[PRAAx] bounded c0 H one)
    (hD : Γ ⊢[PRAAx] le one D)
    (hStep : Γ ⊢[PRAAx] distanceBounded (fraction c b) (fraction a b) A D) : Γ ⊢[PRAAx]
    distanceBounded (inverseCoefficient c1 c0 (dividedDifference (arg a) (arg c) b (succ N)))
      (qmul c0 (correction a b N)) (inverseRateCost (succ N) H*A) D := by
  let j := succ N
  have hInverse := original_inverse_gap_bound a c b N c1 c0 H A D ha hc hc1 hc0 hi1 hi0 hb1 hb0 hD hStep
  have rate := inverse_coefficient_rate c1 c0 (dividedDifference (arg a) (arg c) b j) (firstCoefficient (arg a) b j)
    H (firstCap j) (derivativeCost j*A) (inverseGapCost j H*A) D hb1 hb0 (first_bounded a b j ha) hD
    (derivative_error a c b j A D ha hc hD hStep) hInverse
  exact distance_congr (.eqRefl _) (original_inverse_diagonal a b N c0 ha hc0 hi0)
    (by unfold inverseRateCost; ipra_ring) (.eqRefl _) rate

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeProductDerivativeInverseRate
