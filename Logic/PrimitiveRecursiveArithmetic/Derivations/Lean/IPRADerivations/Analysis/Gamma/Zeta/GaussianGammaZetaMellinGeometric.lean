import IPRADerivations.Analysis.Gamma.Zeta.GaussianGammaZetaMellinIntegrand
import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerPositivePowerChartCorrectedImage
import IPRADerivations.Analysis.Geometry.GaussianRationalGeometricPowerTail
import IPRADerivations.Analysis.Geometry.GaussianRationalInverseGeometric

/-!
# Finite geometric prefixes of the original Gamma–zeta integrand

The geometric ratio is the exact rational inverse of the unscaled
positive exponential at the clock used by the original reciprocal.
The error can be bounded uniformly on a strip of positive times.
-/

set_option autoImplicit false
set_option maxHeartbeats 750000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinGeometric

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianApproximateInverseDistance (multiply_distance)
open GaussianDominantPairAlgebra (radiusPoint radius_one)
open GaussianEulerDecayFactorBounds (fraction_is_radius_point)
open GaussianEulerIntegrandName (powerF powerData source)
open GaussianExponentialAffineLower (affine_prefix lower_of_real_order)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianGammaZetaMellinIntegrand
  (exponentialF exponentialData denominatorF denominatorData denominatorClock reciprocalF reciprocalData
    reciprocalClock denominator_lower denominator_at reciprocal_at reciprocal_bound factorClock)
open GaussianPositiveExponentialTermBound (actual_positive_fraction)
open GaussianPositiveRealArithmetic (positive_congr)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (qadd qmul canonical positive_product ofGaussian_canonical)
open GaussianRationalLowerBounds (lower name_lower inverse_bound)
open GaussianRationalMetric (qsub qnegative qnegative_canonical bounded distanceBounded)
open GaussianRationalPolynomialExponential (scalarSum scalarBody)
open GaussianRationalReciprocal (power reciprocal reciprocal_identity bound_congr bounded_negative bounded_product)
open GaussianRationalSyntheticDivision (qone qmul_congr qadd_congr qadd_sub_cancel)
open GaussianReciprocalHorner (qmul_associative qmul_one_right)
open GaussianRationalPowerAlgebra (qmul_commutative)
open RationalArgmin (rationalLE_congr)
open ConciseIPRA.PTm (succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

def positiveSample (p a b : PTm n) : PTm n :=
  ap2 exponentialF (denominatorClock (reciprocalClock p b)) (exponentialData a b)

def ratio (p a b : PTm n) : PTm n := reciprocal (positiveSample p a b)
def prefixValue (p a b N : PTm n) : PTm n := GaussianRationalInverseGeometric.value N (ratio p a b)

def weightedValue (p z D a b N : PTm n) : PTm n :=
  let k := factorClock p z D a b
  qmul (ap2 powerF k (powerData z D a b)) (prefixValue k a b N)

@[simp] theorem subst_positiveSample {m : ℕ} (σ : Fin n → PTm m) (p a b : PTm n) :
    Syn.subst σ (positiveSample p a b) = positiveSample (Syn.subst σ p) (Syn.subst σ a) (Syn.subst σ b) := by
  simp [positiveSample,denominatorClock,reciprocalClock,two,one]

@[simp] theorem subst_ratio {m : ℕ} (σ : Fin n → PTm m) (p a b : PTm n) :
    Syn.subst σ (ratio p a b) = ratio (Syn.subst σ p) (Syn.subst σ a) (Syn.subst σ b) := by simp [ratio]

@[simp] theorem subst_prefixValue {m : ℕ} (σ : Fin n → PTm m) (p a b N : PTm n) :
    Syn.subst σ (prefixValue p a b N) =
      prefixValue (Syn.subst σ p) (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ N) := by simp [prefixValue]

@[simp] theorem subst_weightedValue {m : ℕ} (σ : Fin n → PTm m) (p z D a b N : PTm n) :
    Syn.subst σ (weightedValue p z D a b N) =
      weightedValue (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ D) (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ N) := by
  simp [weightedValue,factorClock]

private theorem affine_radius (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] qadd qone (radiusPoint a b) ≐ radiusPoint (b+a) b := by
  have e := (fraction_is_radius_point (Γ := Γ) one one (le_refl one)).eqTrans radius_one
  exact (qadd_congr e.eqSymm (fraction_is_radius_point a b hb).eqSymm).eqTrans
    ((GaussianEulerPositivePowerChartCorrectedImage.fraction_sum one one a b (le_refl one) hb).eqTrans
      ((GaussianCompactRiemannName.fraction_congr _ _ _ _ (by ipra_ring) (one_mul b)).eqTrans
        (fraction_is_radius_point (b+a) b hb)))

theorem positive_sample_lower (p a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] lower (positiveSample p a b) (b+a) b := by
  let t := radiusPoint a b
  let R := GaussianNameBounds.U constantF t
  let r := denominatorClock (reciprocalClock p b)
  let k := GaussianRadiusExponentialName.index R r
  let u := GaussianRadiusExponentialName.inputPrecision R r
  let x := positiveSample p a b
  have ht := actual_positive_fraction a b hb
  have hc : Γ ⊢[PRAAx] canonical t := ofGaussian_canonical _ _ hb
  have hk := GaussianPositiveExponentialSeparation.original_cutoff_positive (Γ := Γ) R r
  have read : Γ ⊢[PRAAx] x ≐ scalarSum t k :=
    (GaussianRadiusExponentialName.sample_at constantF R r t).eqTrans
      (GaussianRationalFiniteSum.sum_index_congr scalarBody (.eqRefl _) (constant_at u t))
  have line : Γ ⊢[PRAAx] scalarSum t one ≐ radiusPoint (b+a) b :=
    (affine_prefix t hc).eqTrans (affine_radius a b hb)
  have order := GaussianPositiveExponentialOrder.argument_and_cutoff_monotone t t one k ht ht
    (RationalArgmin.reflexive (fstT t)) hk
  exact lower_of_real_order x (b+a) b
    (positive_congr read.eqSymm (GaussianPositiveExponentialProduct.positive_scalar_sum t k ht))
    (GaussianRadiusExponentialName.sample_canonical constantF R r t) hb
    (rationalLE_congr (congrFst line) (congrFst read).eqSymm order)

theorem ratio_bound (p a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] bounded (ratio p a b) b (b+a) :=
  inverse_bound _ _ _ (le_trans hb (le_add_right b a)) hb (positive_sample_lower p a b hb)

theorem inverse_pair (p a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] qmul (positiveSample p a b) (ratio p a b) ≐ qone :=
  reciprocal_identity _ (GaussianNameReciprocal.lower_norm_positive _ b hb
    (name_lower _ (b+a) b (le_trans hb (le_add_right b a)) hb (positive_sample_lower p a b hb)))

theorem prefix_term (j p a b : PTm n) :
    inst2 GaussianRationalInverseGeometric.body j (ratio p a b) = power (ratio p a b) (succ j) := by
  simp only [GaussianRationalInverseGeometric.body,inst2,GaussianRationalReciprocal.subst_power,Syn.subst_var,
    ConciseIPRA.PTm.subst_succ,Matrix.cons_val_zero,Matrix.cons_val_one]

theorem partial_cleared (p a b N : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] qmul (ap2 denominatorF (reciprocalClock p b) (denominatorData a b)) (prefixValue p a b N) ≐
      qsub qone (power (ratio p a b) N) :=
  (qmul_congr (denominator_at (reciprocalClock p b) a b) (.eqRefl (prefixValue p a b N))).eqTrans
    (GaussianRationalInverseGeometric.finite (positiveSample p a b) (ratio p a b) N (inverse_pair p a b hb))

theorem partial_value (p a b N : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] prefixValue p a b N ≐
      qmul (ap2 reciprocalF p (reciprocalData a b)) (qsub qone (power (ratio p a b) N)) := by
  let r := reciprocalClock p b
  let d := ap2 denominatorF r (denominatorData a b)
  let w := ap2 reciprocalF p (reciprocalData a b)
  let v := prefixValue p a b N
  have read : Γ ⊢[PRAAx] w ≐ reciprocal d :=
    (reciprocal_at p a b).eqTrans (GaussianNameReciprocal.reciprocal_congr (denominator_at r a b).eqSymm)
  have inverse : Γ ⊢[PRAAx] qmul w d ≐ qone :=
    (qmul_congr read (.eqRefl d)).eqTrans ((qmul_commutative (reciprocal d) d).eqTrans
      (reciprocal_identity d (GaussianNameReciprocal.lower_norm_positive d b hb
        (name_lower d a b ha hb (denominator_lower r a b hb)))))
  have cancel : Γ ⊢[PRAAx] qmul w (qmul d v) ≐ v :=
    (qmul_associative w d v).eqSymm.eqTrans
      ((qmul_congr inverse (.eqRefl v)).eqTrans (GaussianPolynomialDeterminantTerms.one_mul_canonical v
        (GaussianRationalFiniteSum.sum_canonical GaussianRationalInverseGeometric.body N (ratio p a b))))
  exact cancel.eqSymm.eqTrans (qmul_congr (.eqRefl w) (partial_cleared p a b N hb))

theorem partial_error (p a b N : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] distanceBounded (prefixValue p a b N) (ap2 reciprocalF p (reciprocalData a b))
      (b*b) (a*(b+N*a)) := by
  let w := ap2 reciprocalF p (reciprocalData a b)
  let v := power (ratio p a b) N
  let H := b+N*a
  have hH : Γ ⊢[PRAAx] le one H := le_trans hb (le_add_right b (N*a))
  have tail := GaussianRationalGeometricPowerTail.power_tail (ratio p a b) b a N hb (ratio_bound p a b hb)
  have back : Γ ⊢[PRAAx] qsub (qsub qone v) qone ≐ qnegative v :=
    qadd_sub_cancel qone (qnegative v) (qnegative_canonical v)
  have diff := bound_congr back.eqSymm (.eqRefl b) (.eqRefl H) (bounded_negative v _ _ hH tail)
  have prod := bounded_product w _ b a b H ha hH (reciprocal_bound p a b ha hb) diff
  have dist := bound_congr (GaussianRationalRoundedPower.multiplication_difference w (qsub qone v) qone).eqSymm
    (.eqRefl _) (.eqRefl _) prod
  exact distance_congr (partial_value p a b N ha hb).eqSymm
    (qmul_one_right w (GaussianNameReciprocal.name_canonical denominatorF b (denominatorData a b) p))
    (.eqRefl _) (.eqRefl _) dist

theorem partial_error_on_strip (p a b N H : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (hH : Γ ⊢[PRAAx] le one H) (ht : Γ ⊢[PRAAx] le b (H*a)) :
    Γ ⊢[PRAAx] distanceBounded (prefixValue p a b N) (ap2 reciprocalF p (reciprocalData a b))
      (H*H) (H+N) := by
  have den := positive_product _ _ ha (le_trans hb (le_add_right b (N*a)))
  have pad : Γ ⊢[PRAAx] le ((b*b)*(H+N)) ((H*H)*(a*(b+N*a))) := by
    ipra_le 𝔞(H*b)*sl ht+𝔞(N)*sl (sq_le_sq ht)
  exact distance_radius_mono _ _ _ _ _ _ den (le_trans hH (le_add_right H N)) pad (partial_error p a b N ha hb)

theorem integrand_error_on_strip (p z D a b N H P : PTm n)
    (h : Γ ⊢[PRAAx] source z D a b) (hH : Γ ⊢[PRAAx] le one H)
    (ht : Γ ⊢[PRAAx] le b (H*a))
    (hP : Γ ⊢[PRAAx] bounded (ap2 powerF (factorClock p z D a b) (powerData z D a b)) P one) :
    Γ ⊢[PRAAx] distanceBounded (weightedValue p z D a b N)
      (ap2 GaussianGammaZetaMellinIntegrand.nameF p (GaussianGammaZetaMellinIntegrand.data z D a b))
      (P*(H*H)) (H+N) := by
  let k := factorClock p z D a b
  have raw := partial_error_on_strip k a b N H h.andE₂.andE₁ h.andE₂.andE₂ hH ht
  have prod := multiply_distance _ _ _ P (H*H) (H+N) (le_trans hH (le_add_right H N)) hP raw
  exact distance_congr (.eqRefl _) (GaussianGammaZetaMellinIntegrand.sample_at p z D a b).eqSymm
    (.eqRefl _) (.eqRefl _) prod

theorem actual_gamma_zeta_mellin_geometric_prefix_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (((le one (var 1) ⋏ le one (var 2)) ⋏ (le one (var 4) ⋏ le (var 2) (var 4*var 1))) ⟶
      distanceBounded (prefixValue (var 0) (var 1) (var 2) (var 3))
        (ap2 reciprocalF (var 0) (reciprocalData (var 1) (var 2))) (var 4*var 4) (var 4+var 3)) :=
  closeUniv 5 (.impI (partial_error_on_strip _ _ _ _ _ Prf.hyp0.andE₁.andE₁ Prf.hyp0.andE₁.andE₂
    Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinGeometric
