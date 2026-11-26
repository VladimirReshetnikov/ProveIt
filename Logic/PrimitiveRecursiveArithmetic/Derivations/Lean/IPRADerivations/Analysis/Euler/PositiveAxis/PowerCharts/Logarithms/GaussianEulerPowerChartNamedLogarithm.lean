import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.ImageGrids.GaussianEulerPositivePowerChartImage
import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.Logarithms.GaussianEulerPositivePowerChartRealLogarithm
import IPRADerivations.Analysis.Exponential.PositiveAxis.GaussianNamedPositiveLogarithmExponential
import IPRADerivations.Analysis.Euler.PowerScaling.GaussianEulerPowerScalingKernel

/-!
# The original logarithm and rescaled kernel at the power-chart image

Retiming preserves the chart and makes every sample a certified compact
positive rational time. The lifted original logarithm recovers the
chart under exponential, so real exponential injectivity identifies it
with the affine logarithmic coordinate. The original rescaled Euler
kernel therefore agrees on both logarithm names.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPowerChartNamedLogarithm

open_ipra
open GaussianEulerPositivePowerChart (source majorant)
open GaussianEulerPositivePowerChartImage (reciprocalMargin query)
open GaussianEulerPositivePowerChartLogarithm (logarithmF logarithmData)
open GaussianEulerPowerScalingParameter (scaled)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans)
open GaussianRationalHorner (canonical positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "C" => GaussianEulerPositivePowerChart.nameF

abbrev lateF : PR 2 := GaussianFastValueCut.nameF C
def lateData (e f d h Q S E T a b : PTm n) : PTm n :=
  GaussianFastValueCut.nameData (reciprocalMargin h Q E T) (GaussianEulerPositivePowerChart.data e f d h S a b)
abbrev logF : PR 2 := GaussianNamedPositiveLogarithm.nameF lateF
def logData (e f d h Q S E T a b : PTm n) : PTm n :=
  GaussianNamedPositiveLogarithm.data (lateData e f d h Q S E T a b) (reciprocalMargin h Q E T)
abbrev kernelF : PR 2 := GaussianEulerExponentialSubstitutionNamedKernel.nameF logF
def kernelData (z B e f d h Q S E T a b : PTm n) : PTm n :=
  GaussianEulerExponentialSubstitutionNamedKernel.data logF (scaled z f) (B*e) (logData e f d h Q S E T a b)

ipra_subst lateData
ipra_subst logData
ipra_subst kernelData [GaussianEulerPowerScalingParameter.scaled, ComplexLogarithmRemainder.scale]

theorem late_at (p e f d h Q S E T a b : PTm n)
    (hf : Γ ⊢[PRAAx] le one f) (hh : Γ ⊢[PRAAx] le one h) :
    Γ ⊢[PRAAx] ap2 lateF p (lateData e f d h Q S E T a b) ≐
      GaussianEulerPositivePowerChartImage.sample p e f d h Q S E T a b :=
  (GaussianFastValueCut.name_at C (reciprocalMargin h Q E T) _ p).eqTrans
    (GaussianExponentialReference.recode_fixed _
      (GaussianEulerPositivePowerChartLower.original_sample_real (query p h Q E T) e f d h S a b hf hh).andE₁)

theorem late_observations (p q e f d h Q S E T a b : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S E T a b) :
    Γ ⊢[PRAAx] distanceBounded (ap2 lateF p (lateData e f d h Q S E T a b))
      (ap2 C q (GaussianEulerPositivePowerChart.data e f d h S a b)) (unit p+unit q) (unit p*unit q) := by
  have code := late_at p e f d h Q S E T a b hs.andE₁.andE₁.andE₂ hs.andE₁.andE₂.andE₁.andE₂
  have node := GaussianEulerPositivePowerChartImage.fraction_exact p e f d h Q S E T a b hs
  exact distance_congr (node.eqTrans code.eqSymm) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (GaussianEulerPositivePowerChartImage.original_observations p q e f d h Q S E T a b hs)

theorem late_cross (e f d h Q S E T a b : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S E T a b) :
    Γ ⊢[PRAAx] crossEquivalent lateF C (lateData e f d h Q S E T a b) (GaussianEulerPositivePowerChart.data e f d h S a b) := by
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  have ss : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source (sh e) (sh f) (sh d) (sh h)
      (sh Q) (sh S) (sh E) (sh T) (sh a) (sh b) := by
    simpa only [Fm.shift,Syn.shift,GaussianEulerPositivePowerChart.subst_source,sh] using hs.shift.shift
  refine .allI (.allI ?_)
  simpa only [crossEquivalent,subst_lateData,GaussianEulerPositivePowerChart.subst_data,Syn.shift,sh] using
    late_observations (var 1) (var 0) (sh e) (sh f) (sh d) (sh h) (sh Q) (sh S) (sh E) (sh T) (sh a) (sh b) ss

private theorem retime_regular (F : PR 2) (L x : PTm n) (hm : Γ ⊢[PRAAx] le one L)
    (hx : Γ ⊢[PRAAx] pointCN F x) :
    Γ ⊢[PRAAx] pointCN (GaussianFastValueCut.nameF F) (GaussianFastValueCut.nameData L x) := by
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  have hd : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one (sh L) := by
    simpa [Fm.shift,Syn.shift,sh,one] using hm.shift.shift
  have xr : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] pointCN F (sh x) := by
    simpa [Fm.shift,Syn.shift,sh] using hx.shift.shift
  apply GaussianFastValueCut.name_fast
  refine .allI (.allI ?_)
  let p : PTm (n+2) := var 1
  let q : PTm (n+2) := var 0
  have raw := GaussianNameEquivalence.point_at F (sh x) p q xr
  have dd := positive_product _ _ (unit_positive (Γ := (Γ.map Fm.shift).map Fm.shift) p) (unit_positive q)
  exact distance_radius_mono _ _ _ _ (sh L*(unit p+unit q)) (unit p*unit q) dd dd
    (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right ((unit p+unit q)*(unit p*unit q)) hd)) raw

theorem late_regular (e f d h Q S E T a b : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S E T a b) : Γ ⊢[PRAAx] pointCN lateF (lateData e f d h Q S E T a b) :=
  retime_regular _ _ _ (GaussianEulerPositivePowerChartImage.margin_positive h Q E T hs.andE₁.andE₂.andE₁.andE₂)
    (GaussianEulerPositivePowerChart.name_regular e f d h Q S E T a b hs)

theorem late_sample_source (p e f d h Q S E T a b : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S E T a b) :
    Γ ⊢[PRAAx] canonical (ap2 lateF p (lateData e f d h Q S E T a b)) ⋏
      GaussianPositiveCompactInputDecoding.source (ap2 lateF p (lateData e f d h Q S E T a b))
        (reciprocalMargin h Q E T) (majorant Q S E T) := by
  have eq := late_at p e f d h Q S E T a b hs.andE₁.andE₁.andE₂ hs.andE₁.andE₂.andE₁.andE₂
  have c := GaussianFastValueCut.name_canonical (Γ := Γ) C (reciprocalMargin h Q E T) (GaussianEulerPositivePowerChart.data e f d h S a b) p
  have old := GaussianEulerPositivePowerChartImage.original_sample_source p e f d h Q S E T a b hs
  refine .andI c ?_
  simpa [GaussianPositiveCompactInputDecoding.source] using Prf.eqSubst1 (Ax := PRAAx) (Γ := Γ)
    (GaussianPositiveCompactInputDecoding.source (var 0) (Syn.shift (reciprocalMargin h Q E T)) (Syn.shift (majorant Q S E T)))
    eq.eqSymm (by simpa [GaussianPositiveCompactInputDecoding.source] using old)

theorem late_source (e f d h Q S E T a b : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S E T a b) :
    Γ ⊢[PRAAx] GaussianNamedPositiveLogarithm.source lateF (lateData e f d h Q S E T a b)
      (reciprocalMargin h Q E T) (majorant Q S E T) := by
  refine .andI (late_regular e f d h Q S E T a b hs)
    (.andI (GaussianEulerPositivePowerChartImage.margin_positive h Q E T hs.andE₁.andE₂.andE₁.andE₂) (.allI ?_))
  let sh (t : PTm n) := Syn.shift t
  have ss : Γ.map Fm.shift ⊢[PRAAx] source (sh e) (sh f) (sh d) (sh h) (sh Q) (sh S) (sh E) (sh T) (sh a) (sh b) := by
    simpa only [Fm.shift,Syn.shift,GaussianEulerPositivePowerChart.subst_source,sh] using hs.shift
  simpa only [GaussianNamedPositiveLogarithm.admissible,subst_lateData,GaussianEulerPositivePowerChartImage.subst_reciprocalMargin,
    GaussianEulerPositivePowerChart.subst_majorant,Syn.shift,sh] using
    late_sample_source (var 0) (sh e) (sh f) (sh d) (sh h) (sh Q) (sh S) (sh E) (sh T) (sh a) (sh b) ss

theorem original_logarithm (e f d h Q S E T a b : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S E T a b) :
    Γ ⊢[PRAAx] crossEquivalent logF logarithmF (logData e f d h Q S E T a b) (logarithmData e f d h a b) := by
  let y := logarithmData e f d h a b
  let L := GaussianEulerPositivePowerChartRealLogarithm.disk h Q S E T
  let x := lateData e f d h Q S E T a b
  let G := reciprocalMargin h Q E T
  let H := majorant Q S E T
  have src := late_source e f d h Q S E T a b hs
  have input := GaussianEulerPositivePowerChartRealLogarithm.original_input e f d h Q S E T a b hs
  have regular := GaussianEulerPositivePowerChartLogarithm.logarithm_regular e f d h Q S E T a b hs
  have expLog := GaussianNamedPositiveLogarithmExponential.original_recovery lateF x G H src
  have old := GaussianEulerPositivePowerChartLogarithm.original_chart e f d h Q S E T a b hs
  have change := GaussianExponentialRadiusIndependence.same_input_cross logarithmF (GaussianNameBounds.U logarithmF y) L y
    (GaussianGammaFiniteApproximantName.exponential_input _ _ regular) input
  have expChart := cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ old) change
  exact GaussianRealNameExponentialInjectivity.independent_radii_injective logF logarithmF
    (GaussianCompactLogarithmBounds.radius G H) L (logData e f d h Q S E T a b) y
    (GaussianNamedPositiveLogarithm.exponential_input lateF x G H src) input
    (GaussianNamedPositiveLogarithm.real_samples lateF x G)
    (GaussianEulerPositivePowerChartRealLogarithm.real_samples e f d h a b hs.andE₁.andE₁.andE₂)
    (cross_trans _ _ _ _ _ _ expLog (cross_trans _ _ _ _ _ _ (late_cross e f d h Q S E T a b hs) expChart))

theorem original_image_kernel (z B e f d h Q S E T a b : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S E T a b) :
    Γ ⊢[PRAAx] crossEquivalent kernelF GaussianEulerPowerScalingKernel.transformedF
      (kernelData z B e f d h Q S E T a b) (GaussianEulerPowerScalingKernel.transformedData z B e f d h a b) :=
  GaussianEulerExponentialSubstitutionNamedKernel.name_proper logF logarithmF (scaled z f) (B*e) _ _
    (GaussianNamedPositiveLogarithm.name_regular lateF _ _ _ (late_source e f d h Q S E T a b hs))
    (GaussianEulerPositivePowerChartLogarithm.logarithm_regular e f d h Q S E T a b hs)
    (original_logarithm e f d h Q S E T a b hs)

theorem actual_original_power_chart_named_logarithm_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
      (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) ⟶
        crossEquivalent logF logarithmF (logData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9))
          (logarithmData (var 0) (var 1) (var 2) (var 3) (var 8) (var 9))) :=
  closeUniv 10 (.impI (original_logarithm _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerPowerChartNamedLogarithm
