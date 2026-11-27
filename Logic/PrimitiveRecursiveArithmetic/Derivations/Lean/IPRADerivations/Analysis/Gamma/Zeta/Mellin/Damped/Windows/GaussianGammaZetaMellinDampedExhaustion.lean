import IPRADerivations.Analysis.Euler.CompactExhaustion.GaussianEulerCompactExhaustion
import IPRADerivations.Analysis.Gamma.Integrals.Substitutions.GaussianEulerPositiveScalingGamma

/-!
# A damped Mellin row on an enclosing compact window

A row of scale `c` on the original rational panel is compared to the
original positive-scaling improper name. Its image panel must enclose
the Euler cutoff at `k`. Both clocks remain independent.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinDampedExhaustion

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (mesh quadrature)
open GaussianEulerCompactExhaustion (budget denominator image_clock_equivalent)
open GaussianEulerDampedTimeRate (lipschitz)
open GaussianEulerPositiveScalingConstant (inverseF inverseData inverse_regular inverseBound scaleF scaleData)
open GaussianEulerPositiveScalingIntegrand (evaluatorF fixedData)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianNameBounds (U all_samples_bounded)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianGammaCompactCutoffAlignment (cross_data_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "Damp" => GaussianEulerDampedCompactName.nameF
local notation "Euler" => GaussianEulerCompactAdditivity.nameF
local notation "Improper" => GaussianEulerPositiveScalingImproper.nameF

def source (z R B A k c a C E T : PTm n) : Fm PTm n :=
  GaussianEulerCompactExhaustion.source z R B A k (c*a) (c*C) E E T ⋏ (le one c ⋏ le one a)

def data (z R B c a C E T : PTm n) : PTm n :=
  GaussianEulerDampedCompactName.data z R B c one a C E T

def gain (z R B A c : PTm n) : PTm n := inverseBound z B c one*budget A R

ipra_subst source [GaussianEulerCompactExhaustion.source, GaussianGammaIntegralCutoffs.etaDen, GaussianGammaIntegralCutoffs.top, GaussianGammaIntegralCutoffs.height, GaussianGammaIntegralCutoffs.tailCoefficient]

ipra_subst data

theorem image_source (z R B A k c a C E T : PTm n) (h : Γ ⊢[PRAAx] source z R B A k c a C E T) :
    Γ ⊢[PRAAx] GaussianEulerPositiveScalingCutoffGeometry.source z R B (c*a) (c*C) E T c one :=
  .andI (GaussianEulerCompactExhaustion.full_source z R B A k (c*a) (c*C) E E T h.andE₁)
    (.andI h.andE₂.andE₁ (le_refl one))

theorem damped_source (z R B A k c a C E T : PTm n) (h : Γ ⊢[PRAAx] source z R B A k c a C E T) :
    Γ ⊢[PRAAx] GaussianEulerDampedCompactName.source z R B c one a C E T := by
  have g := image_source z R B A k c a C E T h
  have w := mul_le_mul_right (a+C) h.andE₂.andE₁
  have first : Γ ⊢[PRAAx] le (a+C) (c*a+c*C) :=
    le_congr (one_mul _) (by ipra_ring) w
  exact .andI (.andI g.andE₁.andE₁
    (.andI h.andE₂.andE₂ (le_trans first g.andE₁.andE₂.andE₂))) g.andE₂

private theorem scaled_source (z R B A k c a C E T : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A k c a C E T) :
    Γ ⊢[PRAAx] GaussianEulerDampedCompactName.source z R B c one (c*a) (c*C) (c*E) T := by
  have d := damped_source z R B A k c a C E T h
  have lower := positive_product _ _ h.andE₂.andE₁ d.andE₁.andE₁.andE₂.andE₁
  have endLe := mul_le_mul_right c d.andE₁.andE₂.andE₂
  exact .andI (.andI (.andI d.andE₁.andE₁.andE₁ (.andI lower d.andE₁.andE₁.andE₂.andE₂))
    (.andI (positive_product _ _ h.andE₂.andE₁ h.andE₂.andE₂)
      (le_congr (by ipra_ring) (by ipra_ring) endLe))) d.andE₂

private theorem pulled_data_congr (z R B c a C E T : PTm n) : Γ ⊢[PRAAx]
    GaussianEulerPositiveScalingCompact.dampedDatum z R B (c*a) (c*C) E T c one ≐
      data z R B c (c*a) (c*C) (c*E) T := by
  let sh (u : PTm n) := Syn.shift u
  let fixed := GaussianEulerDampedCompactName.data (sh z) (sh R) (sh B) (sh c) (sh one)
  have ea : Γ ⊢[PRAAx] data z R B c (one*(c*a)) (one*(c*C)) (c*E) (one*T) ≐
      data z R B c (c*a) (one*(c*C)) (c*E) (one*T) := by
    simpa only [data,fixed,sh,GaussianEulerDampedCompactName.subst_data,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      using Prf.eqCongr1 (fixed (var 0) (sh (one*(c*C))) (sh (c*E)) (sh (one*T))) (one_mul (c*a))
  have eC : Γ ⊢[PRAAx] data z R B c (c*a) (one*(c*C)) (c*E) (one*T) ≐
      data z R B c (c*a) (c*C) (c*E) (one*T) := by
    simpa only [data,fixed,sh,GaussianEulerDampedCompactName.subst_data,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      using Prf.eqCongr1 (fixed (sh (c*a)) (var 0) (sh (c*E)) (sh (one*T))) (one_mul (c*C))
  have eT : Γ ⊢[PRAAx] data z R B c (c*a) (c*C) (c*E) (one*T) ≐ data z R B c (c*a) (c*C) (c*E) T := by
    simpa only [data,fixed,sh,GaussianEulerDampedCompactName.subst_data,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      using Prf.eqCongr1 (fixed (sh (c*a)) (sh (c*C)) (sh (c*E)) (var 0)) (one_mul T)
  exact ea.eqTrans (eC.eqTrans eT)

theorem unscale_cross (z R B A k c a C E T : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A k c a C E T) :
    Γ ⊢[PRAAx] crossEquivalent Damp Damp (data z R B c a C E T)
      (GaussianEulerPositiveScalingCompact.dampedDatum z R B (c*a) (c*C) E T c one) := by
  let x := fixedData z B c one
  let L := lipschitz R E T c one
  let L' := lipschitz R (c*E) T c one
  have hi := GaussianEulerDampedCompactName.compact_input _ _ _ _ _ _ _ _ _ (damped_source z R B A k c a C E T h)
  have hr : Γ ⊢[PRAAx] GaussianCompactIntervalRescaling.input evaluatorF c a C E L T x :=
    .andI h.andE₂.andE₁ hi
  have geom := GaussianCompactIntervalRescaling.name_rescaling evaluatorF c a C E L T x hr
  have agree := GaussianCompactMeshIndependence.name_independence evaluatorF (c*a) (c*C) (c*E) L T L' T x
    (.andI (GaussianCompactIntervalRescaling.scaled_input evaluatorF c a C E L T x hr)
      (GaussianEulerDampedCompactName.compact_input _ _ _ _ _ _ _ _ _ (scaled_source z R B A k c a C E T h)))
  exact cross_data_congr Damp Damp _ _ _ _ (.eqRefl _) (pulled_data_congr z R B c a C E T).eqSymm
    (cross_trans Damp Damp Damp _ _ _ geom agree)

theorem compact_cross (z R B A k c a C E T : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A k c a C E T) :
    Γ ⊢[PRAAx] crossEquivalent Damp (multiplyF inverseF Euler) (data z R B c a C E T)
      (multiplyData inverseF Euler (inverseData z B c one)
        (GaussianEulerCompactAdditivity.data z R B (c*a) (c*C) E T)) := by
  let V := GaussianEulerPositiveScalingCompact.dampedDatum z R B (c*a) (c*C) E T c one
  let X := GaussianEulerCompactAdditivity.data z R B (c*a) (c*C) E T
  let g := image_source z R B A k c a C E T h
  have hs : Γ ⊢[PRAAx] GaussianEulerPositiveScalingConstant.source B c one := .andI g.andE₁.andE₁.andE₁ g.andE₂
  have hv := GaussianEulerDampedCompactName.name_regular _ _ _ _ _ _ _ _ _ (scaled_source z R B A k c a C E T h)
  have stable := GaussianGammaCompactCutoffSplit.point_data_congr Damp _ V (pulled_data_congr z R B c a C E T).eqSymm hv
  have hx := GaussianEulerCompactAdditivity.name_regular z R B (c*a) (c*C) E T g.andE₁
  have dilate := GaussianEulerPositiveScalingCompact.original_compact_cross z R B (c*a) (c*C) E T c one g
  have invert := GaussianEulerPositiveScalingCancellation.cancel Euler Damp X V z B c one hs hx stable dilate
  exact cross_trans Damp Damp (multiplyF inverseF Euler) _ V _ (unscale_cross z R B A k c a C E T h) invert

theorem original_rate (z R B A k c a C E T : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A k c a C E T) :
    Γ ⊢[PRAAx] independentRate Damp Improper (data z R B c a C E T)
      (GaussianEulerPositiveScalingImproper.data z R B A c one) (gain z R B A c) (denominator k) := by
  let F := GaussianEulerImproperName.nameF
  let X := GaussianEulerCompactAdditivity.data z R B (c*a) (c*C) E T
  let W := GaussianEulerPositivePowerChartImageCompactModulus.data z R B (c*a) (c*C) E E T
  let Y := GaussianEulerImproperName.data z R B A
  let v := inverseData z B c one
  let D := denominator k
  have hD : Γ ⊢[PRAAx] le one D := unit_positive _
  have hs : Γ ⊢[PRAAx] GaussianEulerPositiveScalingGamma.source z R B A c one :=
    .andI h.andE₁.andE₁ (.andI h.andE₂.andE₁ (le_refl one))
  have hi := GaussianEulerPositiveScalingGamma.improper_source z R B A c one hs
  have hb := GaussianEulerPositiveScalingImproper.constant_source z R B A c one hi
  have hv := inverse_regular z B c one hb
  have hY := GaussianEulerImproperName.name_regular z R B A hi.andE₁
  have hX := GaussianEulerCompactAdditivity.name_regular z R B (c*a) (c*C) E T
    (image_source z R B A k c a C E T h).andE₁
  have hrate := GaussianEulerCompactExhaustion.original_improper_rate z R B A k (c*a) (c*C) E E T h.andE₁
  have align := cross_symm Euler Euler W X (image_clock_equivalent z R B A k (c*a) (c*C) E E T h.andE₁)
  have rate := GaussianNamedRateTransport.transport Euler F Euler F W Y X Y (budget A R) D hD hrate align
    (cross_refl F Y hY)
  have bbX : Γ ⊢[PRAAx] GaussianNamedMultiplyRate.sampleBound Euler X (U Euler X) := by
    simpa only [GaussianNamedMultiplyRate.sampleBound,GaussianRootApproximationWitness.pointBounds]
      using all_samples_bounded Euler X hX
  have bbv : Γ ⊢[PRAAx] GaussianNamedMultiplyRate.sampleBound inverseF v (inverseBound z B c one) := by
    simpa only [GaussianNamedMultiplyRate.sampleBound,GaussianRootApproximationWitness.pointBounds,inverseBound]
      using all_samples_bounded inverseF v hv
  have raw := GaussianNamedMultiplyRate.independent_rate inverseF Euler inverseF F v X v Y zero one (budget A R) D
    (U Euler X) (inverseBound z B c one) (le_refl one) hD hv hX hv hY bbX bbv
    (GaussianNamedDifferenceRate.self_rate inverseF v hv) rate
  have clean := GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ _ _ (gain z R B A c) D
    (by unfold GaussianNamedMultiplyRate.leadingNumerator gain; ipra_ring)
    (by unfold GaussianNamedMultiplyRate.leadingDenominator; ipra_ring) raw
  exact GaussianNamedRateTransport.transport _ _ _ _ _ _ _ _ _ _ hD clean
    (compact_cross z R B A k c a C E T h)
    (GaussianEulerPositiveScalingImproper.original_cross z R B A c one hi)

/-- Sufficient later observation clock, shared without reference to the scale. -/
def gridPrecision (p T : PTm n) : PTm n := GaussianCompactRiemannName.precision p T

/-- Required grid count depends on the time modulus of the chosen scale. -/
def gridCount (p R c E T : PTm n) : PTm n :=
  unit (p+num 6)*lipschitz R E T c one*T*T

theorem grid_to_panel (p q M z R B c a C E T : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerDampedCompactName.source z R B c one a C E T)
    (hM : Γ ⊢[PRAAx] le one M) (hq : Γ ⊢[PRAAx] le (gridPrecision p T) q)
    (hmesh : Γ ⊢[PRAAx] le (gridCount p R c E T) M) : Γ ⊢[PRAAx]
    distanceBounded (quadrature evaluatorF q M a C E (fixedData z B c one))
      (ap2 Damp p (data z R B c a C E T)) (num 6) (unit (p+num 6)) := by
  let x := fixedData z B c one
  let L := lipschitz R E T c one
  let K := unit (p+num 6)
  let N := mesh p L T
  let Uq := unit q
  have hm := GaussianEulerDampedCompactName.compact_input z R B c one a C E T h
  have hE := hm.andE₂.andE₁
  have hN := GaussianCompactRiemannName.mesh_positive (Γ := Γ) p L T
  have hK := unit_positive (Γ := Γ) (p+num 6)
  have later := le_trans (GaussianCompactRiemannName.precision_lower (Γ := Γ) p T)
    (GaussianCompactRiemannName.dyadic_monotone _ _ hq)
  have coarse := GaussianCompactRiemannName.quadrature_refinement evaluatorF q q M N a C E L x
    hm.andE₁ hE hM hN hm.andE₂.andE₂.andE₂
  have hbound := GaussianCompactRiemannName.quadrature_budget C E L M Uq Uq K T hm.andE₂.andE₂.andE₁ hmesh later later
  have denom := positive_product _ _ hE (GaussianNamedInverseRate.denominator_positive (E*M) q q
    (positive_product _ _ hE hM))
  have first := distance_symmetric _ _ _ _ hK (distance_radius_mono _ _ _ _ (num 3) K denom hK hbound coarse)
  have second := GaussianCompactMeshIndependence.arbitrary_refinement evaluatorF p q M a C E L T x hm hM hq
  have read := GaussianCompactRiemannName.quadrature_index_congr (Γ := Γ) evaluatorF q (M*N) (N*M) a C E x (by ipra_ring)
  have sample := GaussianEulerDampedCompactName.name_at (Γ := Γ) p z R B c one a C E T
  have second' := distance_congr read sample.eqSymm (.eqRefl _) (.eqRefl _) second
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold num; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hK first second')

/-- Exact error for a shared original grid and an independently read improper scale. -/
theorem original_grid_observations (p q r M z R B A k c a C E T : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A k c a C E T)
    (hM : Γ ⊢[PRAAx] le one M) (hq : Γ ⊢[PRAAx] le (gridPrecision p T) q)
    (hmesh : Γ ⊢[PRAAx] le (gridCount p R c E T) M) : Γ ⊢[PRAAx]
    distanceBounded (quadrature evaluatorF q M a C E (fixedData z B c one))
      (ap2 Improper r (GaussianEulerPositiveScalingImproper.data z R B A c one))
      (num 6*rateDenominator (denominator k) p r+
        rateNumerator (gain z R B A c) (denominator k) p r*unit (p+num 6))
      (unit (p+num 6)*rateDenominator (denominator k) p r) := by
  have first := grid_to_panel p q M z R B c a C E T (damped_source z R B A k c a C E T h) hM hq hmesh
  have second := GaussianNamedInverseRate.rate_at Damp Improper _ _ _ _ p r
    (original_rate z R B A k c a C E T h)
  exact GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ (unit_positive _)
    (GaussianNamedInverseRate.denominator_positive (denominator k) p r (unit_positive _)) first second

end LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinDampedExhaustion
