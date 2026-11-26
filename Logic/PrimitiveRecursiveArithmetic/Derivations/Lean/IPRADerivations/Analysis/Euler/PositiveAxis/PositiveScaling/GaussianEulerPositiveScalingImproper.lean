import IPRADerivations.Analysis.Euler.PositiveAxis.PositiveScaling.GaussianEulerPositiveScalingCompact
import IPRADerivations.Analysis.Euler.Integration.Decay.GaussianEulerDampedCompactName
import IPRADerivations.Analysis.Euler.PositiveAxis.PositiveScaling.GaussianEulerPositiveScalingCutoffGeometry
import IPRADerivations.Analysis.Euler.PositiveAxis.PositiveScaling.GaussianEulerPositiveScalingCancellation
import IPRADerivations.Analysis.Euler.CompactExhaustion.GaussianEulerFixedCutoffApproximation
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedMultiplyRate
import IPRADerivations.Analysis.Names.Rates.GaussianNamedDifferenceRate
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateComposition
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateTransport

/-!
# Actual cofinal Euler quadrature with positive rational linear damping

The sampler uses the original damped compact program on the inverse
image of the original Euler cutoff. Its cutoff and observation clocks
pay the genuine original fixed-cutoff error multiplied by the actual
inverse scaling-name bound. The returned original PR2 program is
cross-equivalent to the normalized product of that inverse and the
original Euler improper name; regularity is then derived from the
actual independent observation comparison.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPositiveScalingImproper

open_ipra
open GaussianEulerPositiveScalingConstant (inverseF inverseData inverseBound)
open GaussianGammaIntegralCutoffs (height etaDen top)
open GaussianGammaCompactQuadratureBoundary (width)
open GaussianEulerCutoffCauchyComparison (combined oldData)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNamedInverseRate (independentRate rate_at rateNumerator rateDenominator)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "Damped" => GaussianEulerDampedCompactName.nameF
local notation "Euler" => GaussianEulerImproperName.nameF
local notation "Compact" => GaussianGammaEulerCompactQuadrature.nameF

def source (z R B A c d : PTm n) : Fm PTm n :=
  GaussianEulerImproperName.source z R B A ⋏ (le one c ⋏ le one d)
def gain (z R B A c d : PTm n) : PTm n := inverseBound z B c d*combined A R
def cutoff (p z R B A c d : PTm n) : PTm n := GaussianFastValueCut.exponent (gain z R B A c d) (succ p)
def compactData (k z R B A c d : PTm n) : PTm n :=
  GaussianEulerDampedCompactName.data z R B c d d (d*width k A R) (c*etaDen k A R) (d*top k A R)
def sample (p z R B A c d : PTm n) : PTm n :=
  ap2 Damped (succ p) (compactData (cutoff p z R B A c d) z R B A c d)
def referenceF : PR 2 := multiplyF inverseF Euler
def referenceData (z R B A c d : PTm n) : PTm n :=
  multiplyData inverseF Euler (inverseData z B c d) (GaussianEulerImproperName.data z R B A)
def data (z R B A c d : PTm n) : PTm n := pairT (pairT z R) (pairT (pairT B A) (pairT c d))
def reader (p x : PTm n) : PTm n :=
  sample p (fstT (fstT x)) (sndT (fstT x)) (fstT (fstT (sndT x))) (sndT (fstT (sndT x)))
    (fstT (sndT (sndT x))) (sndT (sndT (sndT x)))
def nameF : PR 2 := PTm.toPR (reader (var 0) (var 1))

ipra_subst source
ipra_subst gain [combined, GaussianGammaIntegralCutoffs.tailCoefficient]
ipra_subst cutoff
ipra_subst compactData [etaDen, top, height, GaussianGammaIntegralCutoffs.tailCoefficient]
ipra_subst sample
ipra_subst referenceData
ipra_subst data
ipra_subst reader

theorem constant_source (z R B A c d : PTm n) (h : Γ ⊢[PRAAx] source z R B A c d) : Γ ⊢[PRAAx]
    GaussianEulerPositiveScalingConstant.source B c d := .andI h.andE₁.andE₁.andE₁ h.andE₂

theorem cutoff_later (p z R B A c d : PTm n) : Γ ⊢[PRAAx] le (succ p) (cutoff p z R B A c d) :=
  le_add_right _ _

theorem cutoff_budget (p z R B A c d : PTm n) : Γ ⊢[PRAAx]
    le (gain z R B A c d*unit (succ p)) (unit (height (cutoff p z R B A c d) A R)) := by
  have later : Γ ⊢[PRAAx] le (cutoff p z R B A c d) (height (cutoff p z R B A c d) A R) :=
    le_of_eq_add (d := A+GaussianGammaIntegralCutoffs.tailCoefficient R+num 10) (by unfold height; ipra_ring)
  exact le_trans (GaussianFastValueCut.query_budget _ _) (GaussianExponentialReference.unit_monotone later)

theorem reference_regular (z R B A c d : PTm n) (h : Γ ⊢[PRAAx] source z R B A c d) : Γ ⊢[PRAAx]
    pointCN referenceF (referenceData z R B A c d) :=
  multiply_fast _ _ _ _ (GaussianEulerPositiveScalingConstant.inverse_regular z B c d (constant_source z R B A c d h))
    (GaussianEulerImproperName.name_regular z R B A h.andE₁)

theorem geometry_source (k z R B A c d : PTm n) (h : Γ ⊢[PRAAx] source z R B A c d) : Γ ⊢[PRAAx]
    GaussianEulerPositiveScalingCutoffGeometry.source z R B one (width k A R) (etaDen k A R) (top k A R) c d :=
  .andI (GaussianEulerPositiveScalingCutoffGeometry.cutoff_interval k A z R B h.andE₁.andE₁) h.andE₂

theorem damped_source (k z R B A c d : PTm n) (h : Γ ⊢[PRAAx] source z R B A c d) : Γ ⊢[PRAAx]
    GaussianEulerDampedCompactName.source z R B c d d (d*width k A R) (c*etaDen k A R) (d*top k A R) := by
  have original := GaussianEulerPositiveScalingCutoffGeometry.pullback_interval _ _ _ _ _ _ _ _ _
    (geometry_source k z R B A c d h)
  exact .andI (.andI original.andE₁ (.andI h.andE₂.andE₂
    (le_congr (congrAdd (by ipra_ring : Γ ⊢[PRAAx] d*one ≐ d) (.eqRefl _)) (.eqRefl _) original.andE₂.andE₂))) h.andE₂

private theorem observation_budget (L H p q : PTm n) (spend : Γ ⊢[PRAAx] le (L*unit (succ p)) H) : Γ ⊢[PRAAx]
    le (rateNumerator L H (succ p) q*(unit p*unit q)) ((unit p+unit q)*rateDenominator H (succ p) q) := by
  have du : Γ ⊢[PRAAx] unit (succ p) ≐ unit p*two := pw_succ two p
  have paid : Γ ⊢[PRAAx] le (L*(unit p*two)) H := le_congr (congrMul (.eqRefl _) du) (.eqRefl _) spend
  have scalar : Γ ⊢[PRAAx] le
      ((L*(unit p*two)*unit q+H*(unit p*two+unit q))*(unit p*unit q))
      ((unit p+unit q)*(H*(unit p*two)*unit q)) := by
    ipra_le (𝔞(unit p)*(𝔞(unit q))^2)*sl paid
  have rn : Γ ⊢[PRAAx] rateNumerator L H (succ p) q ≐ L*(unit p*two)*unit q+H*(unit p*two+unit q) :=
    congrAdd (congrMul (congrMul (.eqRefl _) du) (.eqRefl _)) (congrMul (.eqRefl _) (congrAdd du (.eqRefl _)))
  have rd : Γ ⊢[PRAAx] rateDenominator H (succ p) q ≐ H*(unit p*two)*unit q :=
    congrMul (congrMul (.eqRefl _) du) (.eqRefl _)
  exact le_congr (congrMul rn (.eqRefl _)).eqSymm (congrMul (.eqRefl _) rd).eqSymm scalar

private theorem sample_congr (p z R B A c d z' R' B' A' c' d' : PTm n)
    (hz : Γ ⊢[PRAAx] z ≐ z') (hR : Γ ⊢[PRAAx] R ≐ R') (hB : Γ ⊢[PRAAx] B ≐ B')
    (hA : Γ ⊢[PRAAx] A ≐ A') (hc : Γ ⊢[PRAAx] c ≐ c') (hd : Γ ⊢[PRAAx] d ≐ d') : Γ ⊢[PRAAx]
    sample p z R B A c d ≐ sample p z' R' B' A' c' d' := by
  have e1 : Γ ⊢[PRAAx] sample p z R B A c d ≐ sample p z' R B A c d := by
    simpa only [subst_sample,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (sample (Syn.shift p) (var 0) (Syn.shift R) (Syn.shift B) (Syn.shift A) (Syn.shift c) (Syn.shift d)) hz
  have e2 : Γ ⊢[PRAAx] sample p z' R B A c d ≐ sample p z' R' B A c d := by
    simpa only [subst_sample,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (sample (Syn.shift p) (Syn.shift z') (var 0) (Syn.shift B) (Syn.shift A) (Syn.shift c) (Syn.shift d)) hR
  have e3 : Γ ⊢[PRAAx] sample p z' R' B A c d ≐ sample p z' R' B' A c d := by
    simpa only [subst_sample,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (sample (Syn.shift p) (Syn.shift z') (Syn.shift R') (var 0) (Syn.shift A) (Syn.shift c) (Syn.shift d)) hB
  have e4 : Γ ⊢[PRAAx] sample p z' R' B' A c d ≐ sample p z' R' B' A' c d := by
    simpa only [subst_sample,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (sample (Syn.shift p) (Syn.shift z') (Syn.shift R') (Syn.shift B') (var 0) (Syn.shift c) (Syn.shift d)) hA
  have e5 : Γ ⊢[PRAAx] sample p z' R' B' A' c d ≐ sample p z' R' B' A' c' d := by
    simpa only [subst_sample,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (sample (Syn.shift p) (Syn.shift z') (Syn.shift R') (Syn.shift B') (Syn.shift A') (var 0) (Syn.shift d)) hc
  have e6 : Γ ⊢[PRAAx] sample p z' R' B' A' c' d ≐ sample p z' R' B' A' c' d' := by
    simpa only [subst_sample,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (sample (Syn.shift p) (Syn.shift z') (Syn.shift R') (Syn.shift B') (Syn.shift A') (Syn.shift c') (var 0)) hd
  exact e1.eqTrans (e2.eqTrans (e3.eqTrans (e4.eqTrans (e5.eqTrans e6))))

theorem name_at (p z R B A c d : PTm n) : Γ ⊢[PRAAx] ap2 nameF p (data z R B A c d) ≐ sample p z R B A c d := by
  have program : Γ ⊢[PRAAx] ap2 nameF p (data z R B A c d) ≐ reader p (data z R B A c d) := by
    simpa [nameF,ap2] using toPR_eq (Γ := Γ) (reader (var 0) (var 1) : PTm 2) ![p,data z R B A c d]
  have left := fst_pair (Γ := Γ) (pairT z R) (pairT (pairT B A) (pairT c d))
  have right := snd_pair (Γ := Γ) (pairT z R) (pairT (pairT B A) (pairT c d))
  have middle := (congrFst right).eqTrans (fst_pair (pairT B A) (pairT c d))
  have last := (congrSnd right).eqTrans (snd_pair (pairT B A) (pairT c d))
  exact program.eqTrans (sample_congr p _ _ _ _ _ _ _ _ _ _ _ _
    left.fstE left.sndE
    middle.fstE middle.sndE
    last.fstE last.sndE)

theorem compact_cross (k z R B A c d : PTm n) (h : Γ ⊢[PRAAx] source z R B A c d) : Γ ⊢[PRAAx]
    crossEquivalent Damped (multiplyF inverseF Compact) (compactData k z R B A c d)
      (multiplyData inverseF Compact (inverseData z B c d) (oldData z R B k A)) := by
  have original := GaussianEulerPositiveScalingCompact.original_compact_cross z R B one (width k A R) (etaDen k A R) (top k A R) c d
    (geometry_source k z R B A c d h)
  have dataEq : Γ ⊢[PRAAx]
      GaussianEulerDampedCompactName.data z R B c d (d*one) (d*width k A R) (c*etaDen k A R) (d*top k A R) ≐ compactData k z R B A c d := by
    simpa only [compactData,GaussianEulerDampedCompactName.subst_data,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (GaussianEulerDampedCompactName.data (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift c) (Syn.shift d)
        (var 0) (Syn.shift (d*width k A R)) (Syn.shift (c*etaDen k A R)) (Syn.shift (d*top k A R)))
        (by ipra_ring : Γ ⊢[PRAAx] d*one ≐ d)
  have productEq : Γ ⊢[PRAAx]
      multiplyData GaussianEulerPositiveScalingConstant.scaleF Damped (GaussianEulerPositiveScalingConstant.scaleData z B c d)
        (GaussianEulerDampedCompactName.data z R B c d (d*one) (d*width k A R) (c*etaDen k A R) (d*top k A R)) ≐
      multiplyData GaussianEulerPositiveScalingConstant.scaleF Damped (GaussianEulerPositiveScalingConstant.scaleData z B c d) (compactData k z R B A c d) := by
    simpa only [GaussianNameArithmetic.subst_multiplyData,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (multiplyData GaussianEulerPositiveScalingConstant.scaleF Damped
        (Syn.shift (GaussianEulerPositiveScalingConstant.scaleData z B c d)) (var 0)) dataEq
  have returned : Γ ⊢[PRAAx]
      crossEquivalent Compact (multiplyF GaussianEulerPositiveScalingConstant.scaleF Damped)
        (oldData z R B k A) (multiplyData GaussianEulerPositiveScalingConstant.scaleF Damped
          (GaussianEulerPositiveScalingConstant.scaleData z B c d) (compactData k z R B A c d)) :=
    GaussianGammaCompactCutoffAlignment.cross_data_congr _ _ _ _ _ _ (.eqRefl _) productEq original
  exact GaussianEulerPositiveScalingCancellation.cancel Compact Damped _ _ z B c d
    (constant_source z R B A c d h)
    (GaussianGammaEulerCompactQuadrature.fixed_interval_regular z R B k A h.andE₁.andE₁)
    (GaussianEulerDampedCompactName.name_regular _ _ _ _ _ _ _ _ _ (damped_source k z R B A c d h)) returned

theorem compact_reference_rate (k z R B A c d : PTm n) (h : Γ ⊢[PRAAx] source z R B A c d) : Γ ⊢[PRAAx]
    independentRate Damped referenceF (compactData k z R B A c d) (referenceData z R B A c d)
      (gain z R B A c d) (unit (height k A R)) := by
  have hi := GaussianEulerPositiveScalingConstant.inverse_regular z B c d (constant_source z R B A c d h)
  have hc := GaussianGammaEulerCompactQuadrature.fixed_interval_regular z R B k A h.andE₁.andE₁
  have he := GaussianEulerImproperName.name_regular z R B A h.andE₁
  have cb : Γ ⊢[PRAAx] GaussianNamedMultiplyRate.sampleBound Compact (oldData z R B k A)
      (GaussianNameBounds.U Compact (oldData z R B k A)) := by
    simpa only [GaussianNamedMultiplyRate.sampleBound,GaussianRootApproximationWitness.pointBounds] using
      GaussianNameBounds.all_samples_bounded Compact (oldData z R B k A) hc
  have ib : Γ ⊢[PRAAx] GaussianNamedMultiplyRate.sampleBound inverseF (inverseData z B c d) (inverseBound z B c d) := by
    simpa only [GaussianNamedMultiplyRate.sampleBound,GaussianRootApproximationWitness.pointBounds,inverseBound] using
      GaussianNameBounds.all_samples_bounded inverseF (inverseData z B c d) hi
  have reverse := GaussianNamedRateComposition.symmetric Euler Compact _ _ (combined A R) (unit (height k A R))
    (unit_positive _) (GaussianEulerFixedCutoffApproximation.original_fixed_cutoff_rate z R B A k h.andE₁)
  have raw := GaussianNamedMultiplyRate.independent_rate inverseF Compact inverseF Euler
    (inverseData z B c d) (oldData z R B k A) (inverseData z B c d) (GaussianEulerImproperName.data z R B A)
    zero one (combined A R) (unit (height k A R)) (GaussianNameBounds.U Compact (oldData z R B k A)) (inverseBound z B c d)
    (le_refl one) (unit_positive _) hi hc hi he cb ib
    (GaussianNamedDifferenceRate.self_rate inverseF (inverseData z B c d) hi) reverse
  have exactRate : Γ ⊢[PRAAx]
      independentRate (multiplyF inverseF Compact) referenceF
        (multiplyData inverseF Compact (inverseData z B c d) (oldData z R B k A)) (referenceData z R B A c d)
        (gain z R B A c d) (unit (height k A R)) :=
    GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ _ _ _ _
      (by unfold GaussianNamedMultiplyRate.leadingNumerator gain; ipra_ring)
      (by unfold GaussianNamedMultiplyRate.leadingDenominator; ipra_ring) raw
  exact GaussianNamedRateTransport.transport _ _ _ _ _ _ _ _ _ _ (unit_positive _) exactRate
    (compact_cross k z R B A c d h) (cross_refl referenceF (referenceData z R B A c d) (reference_regular z R B A c d h))

theorem sample_observations (p q z R B A c d : PTm n) (h : Γ ⊢[PRAAx] source z R B A c d) : Γ ⊢[PRAAx]
    distanceBounded (sample p z R B A c d) (ap2 referenceF q (referenceData z R B A c d))
      (unit p+unit q) (unit p*unit q) := by
  have exactRate := compact_reference_rate (cutoff p z R B A c d) z R B A c d h
  exact distance_radius_mono _ _ _ _ _ _
    (GaussianNamedInverseRate.denominator_positive _ _ _ (unit_positive _))
    (positive_product _ _ (unit_positive p) (unit_positive q))
    (observation_budget _ _ p q (cutoff_budget p z R B A c d))
    (rate_at _ _ _ _ _ _ (succ p) q exactRate)

theorem original_observations (p q z R B A c d : PTm n) (h : Γ ⊢[PRAAx] source z R B A c d) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (data z R B A c d)) (ap2 referenceF q (referenceData z R B A c d))
      (unit p+unit q) (unit p*unit q) :=
  distance_congr (name_at p z R B A c d).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (sample_observations p q z R B A c d h)

theorem original_cross (z R B A c d : PTm n) (h : Γ ⊢[PRAAx] source z R B A c d) : Γ ⊢[PRAAx]
    crossEquivalent nameF referenceF (data z R B A c d) (referenceData z R B A c d) := by
  have hh : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift B))
      (Syn.shift (Syn.shift A)) (Syn.shift (Syn.shift c)) (Syn.shift (Syn.shift d)) :=
    by simpa only [Fm.shift,subst_source,Syn.shift] using h.shift.shift
  refine .allI (.allI ?_)
  simpa only [crossEquivalent,subst_data,subst_referenceData,Syn.shift] using
    original_observations (var 1) (var 0) (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift B))
      (Syn.shift (Syn.shift A)) (Syn.shift (Syn.shift c)) (Syn.shift (Syn.shift d)) hh

theorem name_regular (z R B A c d : PTm n) (h : Γ ⊢[PRAAx] source z R B A c d) : Γ ⊢[PRAAx]
    pointCN nameF (data z R B A c d) :=
  cross_trans _ _ _ _ _ _ (original_cross z R B A c d h) (cross_symm _ _ _ _ (original_cross z R B A c d h))

theorem actual_original_linearly_damped_Euler_improper_name_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶ pointCN nameF
      (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))) :=
  closeUniv 6 (.impI (name_regular _ _ _ _ _ _ Prf.hyp0))

theorem actual_original_positive_scaling_improper_identification_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶ crossEquivalent nameF referenceF
      (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
      (referenceData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))) :=
  closeUniv 6 (.impI (original_cross _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerPositiveScalingImproper
