import IPRADerivations.Analysis.Gamma.FunctionalEquations.Multiplication.ReferenceProduct.GaussianGammaGaussReference
import IPRADerivations.Analysis.Gamma.EulerProducts.Gauss.GaussianGaussEulerPositiveExponents
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Multiplication.PowerEstimates.GaussianGaussMultiplicationPowerPerturbation
import IPRADerivations.Analysis.Exponential.Names.GaussianNamedRepeatedExponential
import IPRADerivations.Analysis.Names.Scaling.GaussianNaturalScaleProductName

/-!
# Collecting the positive Euler offset in Gauss multiplication

The repeated positive offset is (N^{mz-1}). Its product with the
unit Euler exponential at (L=m(N+1)-1) agrees with the named ratio
power times the actual scaled positive Euler exponential.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGaussEulerPositiveOffset

open_ipra
open ComplexLogarithmRemainder (oneCode scale)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaEulerFullHeadInverse (negExpF negExpData negative_exponential_regular)
open GaussianGammaFiniteApproximantName (logF log_regular exponential_input)
open GaussianGammaGaussReference (offset scaled_offset)
open GaussianGammaGaussEulerHeads (cutoff)
open GaussianGaussEulerPowerRatio (fixedExponentF fixedExponentData fixed_exponent_regular fixedPowerF fixedPowerData ratio_power_restore)
open GaussianGaussEulerPositiveExponents (positive_from_original fixed_power_regular fixed_power_sum fixed_power_coeff_congr fixed_exponent_coeff_congr)
open GaussianGaussMultiplicationPowerRate (multiplier row_power_input powerF)
open GaussianGaussMultiplicationPowerPerturbation (rowData)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianRationalHorner (ofGaussian qadd qmul)
open GaussianRationalNaturalScale (naturalPoint natScale_as_product)
open GaussianRationalSyntheticDivision (qone)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def offsetExponent (z B m N : PTm n) : PTm n := fixedExponentData (offset z B m) N
def radius (z B m N : PTm n) : PTm n := GaussianNameBounds.U fixedExponentF (offsetExponent z B m N)
abbrev offsetStageF : PR 2 := GaussianBoundedIntegerExponentialStages.expF fixedExponentF
def offsetStageData (z B m N : PTm n) : PTm n := GaussianBoundedIntegerExponentialStages.expData m one (radius z B m N) (offsetExponent z B m N)
abbrev repeatedOffsetF : PR 2 := GaussianNamedFiniteProductName.nameF (GaussianNamedRepeatedProduct.repeatF offsetStageF)
def repeatedOffsetData (z B m N : PTm n) : PTm n := GaussianNamedRepeatedExponential.repeatedData m m (radius z B m N) (offsetExponent z B m N)

ipra_subst offsetStageData [radius, offsetExponent, fixedExponentData, offset, one]

theorem offset_input (z B m N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] GaussianRadiusExponentialName.input fixedExponentF (radius z B m N) (offsetExponent z B m N) :=
  exponential_input _ _ (fixed_exponent_regular (offset z B m) N hN)

theorem offset_stage_regular (z B m N : PTm n) (hm : Γ ⊢[PRAAx] le one m) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] pointCN offsetStageF (offsetStageData z B m N) :=
  GaussianRadiusExponentialName.name_regular _ _ _
    (GaussianBoundedIntegerExponentialSample.stage_input fixedExponentF m one _ _ (offset_input z B m N hN) hm)

theorem offset_stage_cross (z B m N : PTm n) (hm : Γ ⊢[PRAAx] le one m) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] crossEquivalent offsetStageF fixedPowerF (offsetStageData z B m N) (fixedPowerData (offset z B m) N) :=
  GaussianBoundedIntegerExponentialSample.one_cross fixedExponentF m _ _ (offset_input z B m N hN) hm

theorem repeated_offset_regular (z B m N : PTm n) (hm : Γ ⊢[PRAAx] le one m) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] pointCN repeatedOffsetF (repeatedOffsetData z B m N) :=
  GaussianNamedFiniteProductName.name_regular _ _ _ _ _
    (GaussianNamedRepeatedProduct.repeated_row_bounds _ _ _ _
      (GaussianNamedRepeatedExponential.exponential_bounds fixedExponentF m _ _ (offset_input z B m N hN) hm))
    (GaussianNamedRepeatedProduct.repeated_row_regular _ _ _ (offset_stage_regular z B m N hm hN))

private theorem scale_offset_exponent (z B m N : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hm : Γ ⊢[PRAAx] le one m) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] crossEquivalent (GaussianNamedNaturalScale.nameF fixedExponentF) fixedExponentF
      (GaussianNamedNaturalScale.data m m (offsetExponent z B m N)) (fixedExponentData (multiplier z B m) N) := by
  let a := offset z B m
  let c := multiplier z B m
  let M := naturalPoint m
  let X := offsetExponent z B m N
  have scaled := GaussianNaturalScaleProductName.scale_product_cross fixedExponentF m m (radius z B m N) X
    (offset_input z B m N hN) (le_refl m)
  have merged := GaussianGammaEulerShift.merge_head logF M a N (log_regular N hN)
  have coeff : Γ ⊢[PRAAx] qmul M a ≐ c := (natScale_as_product m a).eqSymm.eqTrans (scaled_offset z B m hB hm)
  exact cross_trans _ _ _ _ _ _ scaled (cross_trans _ _ _ _ _ _ merged (fixed_exponent_coeff_congr _ _ N hN coeff))

theorem offset_product (z B m N : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hm : Γ ⊢[PRAAx] le one m) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] crossEquivalent repeatedOffsetF fixedPowerF (repeatedOffsetData z B m N)
      (fixedPowerData (multiplier z B m) N) := by
  let X := offsetExponent z B m N
  let R := radius z B m N
  let c := multiplier z B m
  have input := offset_input z B m N hN
  have repeated := GaussianNamedRepeatedExponential.repeated_exponential fixedExponentF m m R X input hm (le_refl m)
  have scaled := GaussianNamedNaturalScale.exponential_input fixedExponentF m m R X input (le_refl m)
  have fixed := exponential_input _ _ (fixed_exponent_regular c N hN)
  have target := GaussianExponentialRadiusIndependence.independent_radii_proper
    (GaussianNamedNaturalScale.nameF fixedExponentF) fixedExponentF _ _ _ _ scaled fixed
    (scale_offset_exponent z B m N hB hm hN)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ repeated) target

theorem scaled_exponential_split (z B m L : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hL : Γ ⊢[PRAAx] le one L) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF fixedPowerF negExpF) negExpF
      (multiplyData fixedPowerF negExpF (fixedPowerData (multiplier z B m) L) (negExpData oneCode one L))
      (negExpData (scale m z) B L) := by
  let c := multiplier z B m
  let u := ofGaussian (scale m z) B
  let w := negExpData oneCode one L
  let E := fixedPowerData c L
  have hc := fixed_power_regular (Γ := Γ) c L hL
  have one := positive_from_original (Γ := Γ) oneCode one L hL
  have lift := multiply_cross fixedPowerF fixedPowerF negExpF fixedPowerF E E w (fixedPowerData qone L)
    hc hc (negative_exponential_regular oneCode _ L hL) (fixed_power_regular qone L hL) (cross_refl _ _ hc) one
  have split := fixed_power_sum c qone L hL
  have coeff : Γ ⊢[PRAAx] qadd c qone ≐ u :=
    (GaussianReciprocalHorner.qadd_commutative c qone).eqTrans (GaussianRationalLinearProduct.add_sub_right qone u
      (GaussianRationalHorner.ofGaussian_canonical _ _ hB))
  have last := cross_trans _ _ _ _ _ _ (fixed_power_coeff_congr _ _ L hL coeff)
    (cross_symm _ _ _ _ (positive_from_original (scale m z) B L hL))
  exact cross_trans _ _ _ _ _ _ lift (cross_trans _ _ _ _ _ _ split last)

theorem offset_and_unit (z R B m N : PTm n)
    (hm : Γ ⊢[PRAAx] le one m) (hN : Γ ⊢[PRAAx] le one N) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF repeatedOffsetF negExpF) (multiplyF powerF negExpF)
      (multiplyData repeatedOffsetF negExpF (repeatedOffsetData z B m N) (negExpData oneCode one (cutoff m N)))
      (multiplyData powerF negExpF (rowData z R B m N) (negExpData (scale m z) B (cutoff m N))) := by
  let L := cutoff m N
  let c := multiplier z B m
  let a := rowData z R B m N
  let b := fixedPowerData c L
  let e := fixedPowerData c N
  let u := negExpData oneCode one L
  let v := negExpData (scale m z) B L
  let l := multiplyData powerF fixedPowerF a b
  let j := multiplyData fixedPowerF negExpF b u
  have hL := le_trans hN (GaussianGaussEulerCutoff.scaled_cutoff_later m N hm)
  have ha := GaussianRadiusExponentialName.name_regular _ _ _ (row_power_input z R B m N hm hN hB hz)
  have hb := fixed_power_regular c L hL
  have he := fixed_power_regular c N hN
  have hu := negative_exponential_regular (Γ := Γ) oneCode one L hL
  have hv := negative_exponential_regular (Γ := Γ) (scale m z) B L hL
  have first := multiply_cross repeatedOffsetF fixedPowerF negExpF negExpF (repeatedOffsetData z B m N) e u u
    (repeated_offset_regular z B m N hm hN) he hu hu (offset_product z B m N hB hm hN) (cross_refl _ _ hu)
  have restored := multiply_cross (multiplyF powerF fixedPowerF) fixedPowerF negExpF negExpF l e u u
    (multiply_fast _ _ _ _ ha hb) he hu hu (ratio_power_restore z R B m N hm hN hB hz) (cross_refl _ _ hu)
  have assoc := GaussianNameRingLaws.multiply_associative powerF fixedPowerF negExpF a b u ha hb hu
  have scaled := multiply_cross powerF powerF (multiplyF fixedPowerF negExpF) negExpF a a j v ha ha
    (multiply_fast _ _ _ _ hb hu) hv (cross_refl _ _ ha) (scaled_exponential_split z B m L hB hL)
  exact cross_trans _ _ _ _ _ _ first
    (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ restored) (cross_trans _ _ _ _ _ _ assoc scaled))

end LeanProofs.IPRA.Analysis.GaussianGaussEulerPositiveOffset
