import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.FiniteFactors.GaussianBarnesCanonicalHeadPolynomialDerivative
import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.DerivativeRates.GaussianNativeDerivativeQuotientQuadratic

/-!
# Named quotient for the original finite Barnes base powers

The literal constant-name difference and quotient use the actual base
product. The original Gaussian displacement is removed only from the
difference quotient. A vanishing value of the product is allowed.
-/

set_option autoImplicit false
set_option maxHeartbeats 1250000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHeadPolynomialQuotient

open_ipra
open ComplexLogarithmRemainder (add)
open GaussianBarnesCanonicalBaseProductShift (powerProduct)
open GaussianBarnesCanonicalHeadPolynomialDerivative (input valueCap slopeCap errorGain powerSlope increment linear step_bound)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianL1 (norm1)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedMultiplyRate (sampleBound)
open GaussianRationalHorner (ofGaussian positive_product qadd_canonical qmul_canonical qzero qmul)
open GaussianRationalMetric (bounded distanceBounded qsub qsub_canonical)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalSyntheticDivision (qadd_congr qsub_congr qzero_add)
open GaussianRationalDistanceOrder (distance_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Diff" => GaussianNamedDifference.nameF
local notation "dd" => GaussianNamedDifference.data
local notation "QF" => GaussianNamedDifferenceQuotient.nameF
local notation "qd" => GaussianNamedDifferenceQuotient.data

def continuityGain (R N : PTm n) : PTm n := errorGain R N + slopeCap R N

@[simp] theorem subst_continuityGain {m : ℕ} (σ : Fin n → PTm m) (R N : PTm n) :
    Syn.subst σ (continuityGain R N) = continuityGain (Syn.subst σ R) (Syn.subst σ N) := by
  simp [continuityGain]

private theorem increment_norm (x y J P H B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (he : Γ ⊢[PRAAx] distanceBounded x y (J*H) B)
    (hy : Γ ⊢[PRAAx] bounded y (P*H) B) : Γ ⊢[PRAAx] bounded x ((J+P)*H) B :=
  bound_congr (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (GaussianRationalDistanceOrder.norm_from_distance_same hB he hy)

private theorem constant_difference_at (x y p : PTm n) : Γ ⊢[PRAAx]
    ap2 (Diff constantF constantF) p (dd x y) ≐ qsub x y := by
  let g := GaussianNameRingLaws.negativeF constantF
  let v := GaussianNameRingLaws.negativeData y
  let k := GaussianFastValueCut.exponent two p
  have neg : Γ ⊢[PRAAx] ap2 g k v ≐ qsub qzero y := by
    let j := GaussianFastValueCut.exponent (one+one) k
    have changeInput := qsub_congr (Γ := Γ) (.eqRefl qzero) (constant_at j y)
    exact (GaussianNameRingLaws.negative_at constantF y k).eqTrans
      ((GaussianNameArithmetic.recode_congr changeInput).eqTrans
        (GaussianExponentialReference.recode_fixed _ (qsub_canonical _ _)))
  have add := GaussianNameArithmetic.add_at (Γ := Γ) constantF g x v p
  have e := qadd_congr (constant_at k x) neg
  exact add.eqTrans ((GaussianNameArithmetic.recode_congr e).eqTrans
    ((GaussianExponentialReference.recode_fixed _ (qadd_canonical _ _)).eqTrans
       (qadd_congr (.eqRefl x) (qzero_add _ (GaussianRationalMetric.qnegative_canonical y)))))

private theorem constant_increment_rate (x y d a A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hr : Γ ⊢[PRAAx] distanceBounded (qsub x y) (qmul d a) A B) :
    Γ ⊢[PRAAx] independentRate (Diff constantF constantF) (multiplyF constantF constantF)
      (dd x y) (multiplyData constantF constantF d a) A B := by
  let sh (v : PTm n) := Syn.shift (Syn.shift v)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have hc : Γ ⊢[PRAAx] independentRate constantF constantF (qsub x y) (qmul d a) A B :=
    GaussianNamedAddRate.constant_rate _ _ _ _ hB hr
  have hs : Δ ⊢[PRAAx] independentRate constantF constantF (qsub (sh x) (sh y)) (qmul (sh d) (sh a)) (sh A) (sh B) := by
    simpa [Fm.shift,Syn.shift,sh,Δ] using hc.shift.shift
  refine .allI (.allI ?_)
  let p : PTm (n+2) := var 1
  let q : PTm (n+2) := var 0
  have raw := GaussianNamedInverseRate.rate_at constantF constantF _ _ _ _ p q hs
  have ex := (constant_difference_at (Γ := Δ) (sh x) (sh y) p).eqTrans
    (constant_at p (qsub (sh x) (sh y))).eqSymm
  have ey := ((GaussianGammaReciprocalInverse.constant_product_sample (Γ := Δ) q (sh d) (sh a)).eqTrans
     (GaussianExponentialReference.recode_fixed _ (qmul_canonical _ _))).eqTrans
       (constant_at q (qmul (sh d) (sh a))).eqSymm
  simpa only [Syn.shift,GaussianNamedDifference.subst_data,GaussianNameArithmetic.subst_multiplyData,sh,Δ,p,q] using
    distance_congr ex.eqSymm ey.eqSymm (.eqRefl _) (.eqRefl _) raw

theorem named_rate (z h R B H N : PTm n) (hs : Γ ⊢[PRAAx] input z h R B H) : Γ ⊢[PRAAx]
    independentRate (Diff constantF constantF) (multiplyF constantF constantF)
      (dd (powerProduct (add z h) B N) (powerProduct z B N))
      (multiplyData constantF constantF (ofGaussian h B) (powerSlope z B N))
      (errorGain R N*H*H) (B*B) :=
  constant_increment_rate (powerProduct (add z h) B N) (powerProduct z B N) (ofGaussian h B)
    (powerSlope z B N) (errorGain R N*H*H) (B*B) (positive_product _ _ hs.andE₁ hs.andE₁)
    (GaussianBarnesCanonicalHeadPolynomialDerivative.quadratic_bound z h R B H N hs)

theorem quotient_rate (z h R B N : PTm n) (hs : Γ ⊢[PRAAx] input z h R B (norm1 h))
    (hh : Γ ⊢[PRAAx] le one (ComplexLogarithmRemainder.normSq h)) : Γ ⊢[PRAAx]
    independentRate (QF constantF constantF) constantF
      (qd constantF constantF (powerProduct (add z h) B N) (powerProduct z B N) h B)
      (powerSlope z B N) (two*errorGain R N*norm1 h) B :=
  GaussianNativeDerivativeQuotientQuadratic.rate constantF constantF constantF (powerProduct (add z h) B N)
    (powerProduct z B N) (powerSlope z B N) h B (errorGain R N) (constant_regular _) (constant_regular _)
    (constant_regular _) hs.andE₁ hh (named_rate z h R B (norm1 h) N hs)

theorem rational_continuity (z h R B H N : PTm n) (hs : Γ ⊢[PRAAx] input z h R B H)
    (hHB : Γ ⊢[PRAAx] le H B) : Γ ⊢[PRAAx]
    distanceBounded (powerProduct (add z h) B N) (powerProduct z B N) (continuityGain R N*H) B := by
  let x := increment z h B N
  let y := linear z h B N
  let J := errorGain R N
  let P := slopeCap R N
  have hB := hs.andE₁
  have hB2 := positive_product _ _ hB hB
  have err := GaussianBarnesCanonicalHeadPolynomialDerivative.quadratic_bound z h R B H N hs
  have narrow : Γ ⊢[PRAAx] bounded (qsub x y) (J*H) B := by
    refine GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ hB2 hB ?_ err
    have r := mul_le_mul_right (J*H*B) hHB
    exact le_congr (by dsimp only [J]; ipra_ring) (by ipra_ring) r
  have hy : Γ ⊢[PRAAx] bounded y (P*H) B :=
    bound_congr (.eqRefl _) (mul_comm H P) (show Γ ⊢[PRAAx] B*one ≐ B by ipra_ring) (bounded_product _ _ _ _ _ _ hB (le_refl one)
      (step_bound h B H hB hs.andE₂.andE₂.andE₂)
      (GaussianBarnesCanonicalHeadPolynomialDerivative.slope_bound z R B N hB hs.andE₂.andE₁))
  exact increment_norm x y J P H B hB narrow hy

theorem continuity (z h R B H N : PTm n) (hs : Γ ⊢[PRAAx] input z h R B H)
    (hHB : Γ ⊢[PRAAx] le H B) : Γ ⊢[PRAAx] independentRate constantF constantF
    (powerProduct (add z h) B N) (powerProduct z B N) (continuityGain R N*H) B :=
  GaussianNamedAddRate.constant_rate _ _ _ _ hs.andE₁ (rational_continuity z h R B H N hs hHB)

private theorem constant_sample_bound (x M : PTm n) (hx : Γ ⊢[PRAAx] bounded x M one) :
    Γ ⊢[PRAAx] sampleBound constantF x M := by
  refine .allI ?_
  have hx' : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift x) (Syn.shift M) one := by
    simpa [Fm.shift,Syn.shift,one] using hx.shift
  exact bound_congr (constant_at _ _).eqSymm (.eqRefl _) (.eqRefl _) hx'

theorem value_sample_bound (z R B N : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) : Γ ⊢[PRAAx]
    sampleBound constantF (powerProduct z B N) (valueCap R N) :=
  constant_sample_bound _ _ (GaussianBarnesCanonicalHeadPolynomialDerivative.value_bound z R B N hB hz)

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHeadPolynomialQuotient
