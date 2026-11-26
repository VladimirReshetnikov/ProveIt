import IPRADerivations.Analysis.Euler.Integration.Decay.GaussianEulerDampedNamedIntegrand
import IPRADerivations.Analysis.Euler.ExponentialSubstitution.GaussianEulerExponentialNamedKernelRate
import IPRADerivations.Analysis.Euler.Integration.Decay.GaussianEulerDampedTimeRate
import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedRateRadius

/-!
# Compact variation of the actual power-damped Euler integrand

The rational power chart provides a uniform disk and a Lipschitz rate.
Its actual negation and exponential preserve a computed compact rate.
Combining this with the original Euler power gives a uniform sample
majorant and independent-query rate for the damped integrand.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPowerScalingCompactRate

open_ipra
open GaussianEulerDampedNamedIntegrand (decayF decayData)
open GaussianNameRingLaws (negativeF negativeData negative_fast)
open GaussianRationalMetric (bounded distanceBounded qnegative)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialReference (unit_monotone)
open GaussianNamedInverseRate (independentRate)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalHorner (positive_product qmul)

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev chartF : PR 2 := GaussianEulerPositivePowerChart.nameF
abbrev nameF : PR 2 := GaussianEulerDampedNamedIntegrand.nameF chartF
def data (z B e f d h S a b : PTm n) : PTm n :=
  GaussianEulerDampedNamedIntegrand.data chartF z B a b (GaussianEulerPositivePowerChart.data e f d h S a b)
def decayBound (Q S E T : PTm n) : PTm n :=
  GaussianEulerExponentialNamedKernelRate.innerBound (GaussianEulerPositivePowerChart.majorant Q S E T)
def majorant (R Q S E T : PTm n) : PTm n :=
  GaussianEulerCompactPowerMajorant.majorant R E T*decayBound Q S E T
def lipschitz (R Q S E T : PTm n) : PTm n :=
  decayBound Q S E T*GaussianEulerCompactPowerVariation.lipschitz R E T+
    GaussianEulerCompactPowerMajorant.majorant R E T*decayBound Q S E T*GaussianEulerPositivePowerChart.lipschitz Q S E T
def source (z R B e f d h Q S E T a b c v A D : PTm n) : Fm PTm n :=
  GaussianEulerExponentCompactBounds.source z R B E ⋏ GaussianEulerPositivePowerChart.input e f d h Q S E T a b c v A D

ipra_subst data

ipra_subst lipschitz [decayBound, GaussianEulerCompactPowerVariation.lipschitz, GaussianEulerCompactPowerMajorant.majorant, GaussianEulerCompactPowerMajorant.exponentRadius]

private theorem negative_at (F : PR 2) (p x : PTm n) : Γ ⊢[PRAAx]
    ap2 (negativeF F) p (negativeData x) ≐ qnegative (ap2 F (GaussianFastValueCut.exponent (one+one) p) x) :=
  (GaussianNameRingLaws.negative_at F x p).eqTrans
    ((GaussianNameArithmetic.recode_congr
      (GaussianRationalSyntheticDivision.qzero_add _ (GaussianRationalMetric.qnegative_canonical _))).eqTrans
      (GaussianExponentialReference.recode_fixed _ (GaussianRationalMetric.qnegative_canonical _)))

private theorem negative_diagonal (F G : PR 2) (p x y A D : PTm n)
    (hd : Γ ⊢[PRAAx] le one D) (hr : Γ ⊢[PRAAx] independentRate F G x y A D) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (negativeF F) p (negativeData x)) (ap2 (negativeF G) p (negativeData y))
      (A*unit p+two*D) (D*unit p) := by
  let k := GaussianFastValueCut.exponent (one+one) p
  have kd : Γ ⊢[PRAAx] le p k := le_add_right _ _
  have rd := positive_product _ _ hd (unit_positive k)
  have raw := GaussianNamedInverseRate.diagonal_rate F G x y A D k hd hr
  have neg := GaussianNamedDifference.negative_distance _ _ _ _ rd raw
  have shrink := mul_le_mul_right (two*D*D) (unit_monotone kd)
  have aligned := add_le_add_right (A*D*unit p*unit k) shrink
  have near := distance_radius_mono _ _ _ _ (A*unit p+two*D) (D*unit p) rd (positive_product _ _ hd (unit_positive p))
    (le_congr (by ipra_ring) (by ipra_ring) aligned) neg
  exact distance_congr (negative_at F p x).eqSymm (negative_at G p y).eqSymm (.eqRefl _) (.eqRefl _) near

theorem negative_rate (F G : PR 2) (x y A D : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN F x) (hg : Γ ⊢[PRAAx] pointCN G y)
    (hd : Γ ⊢[PRAAx] le one D) (hr : Γ ⊢[PRAAx] independentRate F G x y A D) :
    Γ ⊢[PRAAx] independentRate (negativeF F) (negativeF G) (negativeData x) (negativeData y) A D := by
  apply GaussianNamedLipschitzRate.independent_rate _ _ _ _ _ _ two hd (negative_fast F x hf) (negative_fast G y hg)
  refine .allI ?_
  have ds : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift D) := by simpa [Fm.shift,Syn.shift] using hd.shift
  have rs : Γ.map Fm.shift ⊢[PRAAx] independentRate F G (Syn.shift x) (Syn.shift y) (Syn.shift A) (Syn.shift D) := by
    simpa [Fm.shift,Syn.shift] using hr.shift
  simpa only [GaussianNamedLipschitzRate.diagonalEnvelope,GaussianNamedLipschitzRate.diagonalNumerator,
    GaussianNamedLipschitzRate.diagonalDenominator,Syn.shift,GaussianNameRingLaws.subst_negativeData,
    PTm.subst_add,PTm.subst_mul,GaussianCoefficientNameBounds.subst_unit,two,ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero] using negative_diagonal F G (var 0) (Syn.shift x) (Syn.shift y) (Syn.shift A) (Syn.shift D) ds rs

theorem chart_disk (e f d h Q S E T a b : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianEulerPositivePowerChart.source e f d h Q S E T a b) : Γ ⊢[PRAAx]
    GaussianRadiusExponentialName.input chartF (GaussianEulerPositivePowerChart.majorant Q S E T)
      (GaussianEulerPositivePowerChart.data e f d h S a b) := by
  refine .andI (GaussianEulerPositivePowerChart.name_regular e f d h Q S E T a b hs) (.allI ?_)
  have ss : Γ.map Fm.shift ⊢[PRAAx] GaussianEulerPositivePowerChart.source (Syn.shift e) (Syn.shift f)
      (Syn.shift d) (Syn.shift h) (Syn.shift Q) (Syn.shift S) (Syn.shift E) (Syn.shift T) (Syn.shift a) (Syn.shift b) := by
    simpa only [Fm.shift,Syn.shift,GaussianEulerPositivePowerChart.subst_source] using hs.shift
  simpa only [GaussianRadiusExponentialName.boundedSamples,GaussianEulerPositivePowerChart.subst_majorant,
    GaussianEulerPositivePowerChart.subst_data,Syn.shift] using
    GaussianEulerPositivePowerChart.original_bound (var 0) (Syn.shift e) (Syn.shift f) (Syn.shift d) (Syn.shift h)
      (Syn.shift Q) (Syn.shift S) (Syn.shift E) (Syn.shift T) (Syn.shift a) (Syn.shift b) ss

theorem original_decay_bound (e f d h Q S E T a b : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianEulerPositivePowerChart.source e f d h Q S E T a b) : Γ ⊢[PRAAx]
    GaussianNamedMultiplyRate.sampleBound (decayF chartF)
      (decayData chartF (GaussianEulerPositivePowerChart.data e f d h S a b)) (decayBound Q S E T) := by
  refine .allI ?_
  have ss : Γ.map Fm.shift ⊢[PRAAx] GaussianEulerPositivePowerChart.source (Syn.shift e) (Syn.shift f)
      (Syn.shift d) (Syn.shift h) (Syn.shift Q) (Syn.shift S) (Syn.shift E) (Syn.shift T) (Syn.shift a) (Syn.shift b) := by
    simpa only [Fm.shift,Syn.shift,GaussianEulerPositivePowerChart.subst_source] using hs.shift
  let x := GaussianEulerPositivePowerChart.data (Syn.shift e) (Syn.shift f) (Syn.shift d) (Syn.shift h)
    (Syn.shift S) (Syn.shift a) (Syn.shift b)
  let M := GaussianEulerPositivePowerChart.majorant (Syn.shift Q) (Syn.shift S) (Syn.shift E) (Syn.shift T)
  have hi := GaussianExponentialInverse.negative_input chartF M x (chart_disk _ _ _ _ _ _ _ _ _ _ ss)
  have hb : Γ.map Fm.shift ⊢[PRAAx] bounded (ap2 (decayF chartF) (var 0) (decayData chartF x)) (decayBound
      (Syn.shift Q) (Syn.shift S) (Syn.shift E) (Syn.shift T)) one :=
    GaussianEulerExponentialNamedKernelRate.inner_observation_bound (negativeF chartF) (var 0) M (negativeData x) hi
  simpa only [x,GaussianNamedMultiplyRate.sampleBound,GaussianEulerDampedNamedIntegrand.subst_decayData,
    GaussianEulerPositivePowerChart.subst_data,decayBound,GaussianEulerExponentialNamedKernelRate.subst_innerBound,
    GaussianEulerPositivePowerChart.subst_majorant,Syn.shift] using
    hb

theorem original_observation_bound (p z R B e f d h Q S E T a b : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianEulerExponentCompactBounds.source z R B E)
    (hs : Γ ⊢[PRAAx] GaussianEulerPositivePowerChart.source e f d h Q S E T a b) : Γ ⊢[PRAAx]
    bounded (ap2 nameF p (data z B e f d h S a b)) (majorant R Q S E T) one := by
  let P := GaussianEulerIntegrandName.powerF
  let x := GaussianEulerIntegrandName.powerData z B a b
  let D := decayF chartF
  let y := decayData chartF (GaussianEulerPositivePowerChart.data e f d h S a b)
  let k := GaussianFastValueCut.exponent (GaussianNameArithmetic.multiplyModulus P D x y) p
  have read := (GaussianNameArithmetic.multiply_at (Γ := Γ) P D x y p).eqTrans
    (GaussianExponentialReference.recode_fixed (qmul (ap2 P k x) (ap2 D k y)) (GaussianRationalHorner.qmul_canonical _ _))
  have left := GaussianEulerCompactPowerMajorant.original_power_observation k z R B E T a b hz hs.andE₂.andE₂
  have right := GaussianNamedMultiplyRate.sample_bound_at D y (decayBound Q S E T) k
    (original_decay_bound e f d h Q S E T a b hs)
  exact GaussianRationalReciprocal.bound_congr read.eqSymm (.eqRefl _) (by ipra_ring)
    (GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ (le_refl one) (le_refl one) left right)

theorem original_rate (z R B e f d h Q S E T a b c v A D : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B e f d h Q S E T a b c v A D) : Γ ⊢[PRAAx]
    independentRate nameF nameF (data z B e f d h S a b) (data z B e f d h S c v) (lipschitz R Q S E T*A) D := by
  let C := chartF
  let M := GaussianEulerPositivePowerChart.majorant Q S E T
  let x := GaussianEulerPositivePowerChart.data e f d h S a b
  let y := GaussianEulerPositivePowerChart.data e f d h S c v
  let P := GaussianEulerIntegrandName.powerF
  let u := GaussianEulerIntegrandName.powerData z B a b
  let w := GaussianEulerIntegrandName.powerData z B c v
  have hfirst := hs.andE₂.andE₁
  have hsecond : Γ ⊢[PRAAx] GaussianEulerPositivePowerChart.source e f d h Q S E T c v :=
    .andI hfirst.andE₁ (.andI hfirst.andE₂.andE₁ hs.andE₂.andE₂.andE₁)
  have ha := hfirst.andE₂.andE₂
  have hc := hsecond.andE₂.andE₂
  have hd := hs.andE₂.andE₂.andE₂.andE₁
  have hx := chart_disk e f d h Q S E T a b hfirst
  have hy := chart_disk e f d h Q S E T c v hsecond
  have positive := GaussianEulerPositivePowerChart.original_rate e f d h Q S E T a b c v A D hs.andE₂
  have negative := negative_rate C C x y _ D hx.andE₁ hy.andE₁ hd positive
  have decay := GaussianEulerExponentialNamedKernelRate.inner_rate (negativeF C) (negativeF C) M
    (negativeData x) (negativeData y) _ D (GaussianExponentialInverse.negative_input C M x hx)
    (GaussianExponentialInverse.negative_input C M y hy) hd negative
  have power := GaussianEulerCompactPowerVariation.original_power_rate z R B E T a b c v A D
    (.andI hs.andE₁ (.andI ha (.andI hc hs.andE₂.andE₂.andE₂)))
  have first := GaussianEulerIntegrandName.power_regular z B a b (.andI hs.andE₁.andE₁ ha.andE₁)
  have second := GaussianEulerIntegrandName.power_regular z B c v (.andI hs.andE₁.andE₁ hc.andE₁)
  have raw := GaussianNamedMultiplyRate.independent_rate P (decayF C) P (decayF C)
    u (decayData C x) w (decayData C y) _ D _ D _ _ hd hd
    first (GaussianEulerDampedNamedIntegrand.decay_regular C x hx.andE₁)
    second (GaussianEulerDampedNamedIntegrand.decay_regular C y hy.andE₁)
    (original_decay_bound e f d h Q S E T a b hfirst)
    (GaussianEulerDampedTimeRate.power_sample_bound z R B E T c v hs.andE₁ hc) power decay
  have aligned : Γ ⊢[PRAAx] independentRate nameF nameF (data z B e f d h S a b) (data z B e f d h S c v)
      ((lipschitz R Q S E T*A)*D) (D*D) :=
    GaussianEulerCompactModulus.rate_congr _ _ _ _ _ _ _
      (by unfold GaussianNamedMultiplyRate.leadingNumerator lipschitz decayBound; ipra_ring) raw
  exact GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ (positive_product _ _ hd hd) hd
    (le_congr (.eqRefl _) (by ipra_ring) (le_refl _)) aligned

theorem actual_original_power_damped_compact_rate_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 17
      (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9)
        (var 10) (var 11) (var 12) (var 13) (var 14) (var 15) (var 16) ⟶ independentRate nameF nameF
        (data (var 0) (var 2) (var 3) (var 4) (var 5) (var 6) (var 8) (var 11) (var 12))
        (data (var 0) (var 2) (var 3) (var 4) (var 5) (var 6) (var 8) (var 13) (var 14))
        (lipschitz (var 1) (var 7) (var 8) (var 9) (var 10)*var 15) (var 16)) :=
  closeUniv 17 (.impI (original_rate _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

theorem actual_original_power_damped_sample_bound_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 14
      ((GaussianEulerExponentCompactBounds.source (var 1) (var 2) (var 3) (var 10) ⋏
        GaussianEulerPositivePowerChart.source (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11)
          (var 12) (var 13)) ⟶
        bounded (ap2 nameF (var 0) (data (var 1) (var 3) (var 4) (var 5) (var 6) (var 7) (var 9) (var 12) (var 13)))
          (majorant (var 2) (var 8) (var 9) (var 10) (var 11)) one) :=
  closeUniv 14 (.impI (original_observation_bound _ _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerPowerScalingCompactRate
