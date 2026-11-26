import IPRADerivations.Analysis.Stirling.Binet.StirlingBounds.GaussianBinetStirlingRemainder
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.GaussianLogGammaEulerChartAgreement

/-!
# Rescaling the original complex Stirling remainder

Changing the common numerator and denominator scale preserves the
canonical logarithm, the canonical log-Gamma name, and the exact
Gaussian rational coefficient of the logarithm.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

namespace LeanProofs.IPRA.Analysis.GaussianBinetStirlingRescale

open_ipra
open GaussianBinetStirlingRemainder (offset weightedF weightedData coreF coreData nameF data weighted_regular core_regular)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaInputProperness (code_data_cross)
open GaussianLogGammaEulerChartAgreement (scaled_argument)
open GaussianLogGammaEulerCofinal (canonicalData canonical_regular)
open GaussianLogGammaEulerHead (argument)
open GaussianNameEquivalence (crossEquivalent cross_refl)
open GaussianNamedDifferenceQuotientProperness (difference_proper)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianRationalHorner (positive_product)
open GaussianRationalSyntheticDivision (qsub_congr)
open GaussianRightHalfPlaneLogarithm (source)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "LogF" => GaussianRightHalfPlaneLogarithm.nameF
local notation "logData" => GaussianRightHalfPlaneLogarithm.data
local notation "GammaF" => GaussianLogGammaEulerCofinal.nameF
local notation "DifferenceF" => GaussianNamedDifference.nameF
local notation "differenceData" => GaussianNamedDifference.data

theorem rescale (A B D neg x k : PTm n) (h : Γ ⊢[PRAAx] source A D neg)
    (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] crossEquivalent nameF nameF (data (k*A) (k*B) (k*D) neg x) (data A B D neg x) := by
  let a := k*A
  let b := k*B
  let d := k*D
  let z := argument A B D neg
  let v := argument a b d neg
  let C := GaussianStirlingConstant.nameF
  let c := GaussianStirlingConstant.nameData x
  have hs : Γ ⊢[PRAAx] source a d neg :=
    .andI (.andI (positive_product k A hk h.andE₁.andE₁) h.andE₁.andE₂) (positive_product k D hk h.andE₂)
  have value := scaled_argument A B D neg k d h hk (.eqRefl d)
  have exactArg := code_data_cross constantF v z (constant_regular v) (constant_regular z) value
  have exactOffset := code_data_cross constantF (offset a b d neg) (offset A B D neg)
    (constant_regular _) (constant_regular _) (qsub_congr value (.eqRefl _))
  have hl := GaussianRightHalfPlaneLogarithm.regular a b d neg hs
  have hr := GaussianRightHalfPlaneLogarithm.regular A B D neg h
  have log := GaussianRightHalfPlaneLogarithmRescale.rescale A B D neg k h hk
  have weights : Γ ⊢[PRAAx] crossEquivalent weightedF weightedF (weightedData a b d neg) (weightedData A B D neg) :=
    multiply_cross constantF constantF LogF LogF _ _ (logData a b d neg) (logData A B D neg)
      (constant_regular _) (constant_regular _) hl hr exactOffset log
  have gl := canonical_regular a b d neg hs
  have gr := canonical_regular A B D neg h
  have wl := weighted_regular a b d neg hs
  have wr := weighted_regular A B D neg h
  have gamma := GaussianLogGammaEulerRescale.canonical_rescale A B D neg k d h hk (.eqRefl d) value
  have main := difference_proper GammaF GammaF weightedF weightedF
    (canonicalData a b d neg) (canonicalData A B D neg) (weightedData a b d neg) (weightedData A B D neg)
    gl gr wl wr gamma weights
  have core : Γ ⊢[PRAAx] crossEquivalent coreF coreF (coreData a b d neg) (coreData A B D neg) :=
    add_cross (DifferenceF GammaF weightedF) (DifferenceF GammaF weightedF) constantF constantF
      (differenceData (canonicalData a b d neg) (weightedData a b d neg))
      (differenceData (canonicalData A B D neg) (weightedData A B D neg)) v z
      (GaussianNamedDifference.name_regular _ _ _ _ gl wl) (GaussianNamedDifference.name_regular _ _ _ _ gr wr)
      (constant_regular v) (constant_regular z) main exactArg
  have hc := GaussianStirlingConstant.name_regular (Γ := Γ) x
  exact difference_proper coreF coreF C C (coreData a b d neg) (coreData A B D neg) c c
    (core_regular a b d neg hs) (core_regular A B D neg h) hc hc core (cross_refl C c hc)

theorem actual_complex_Stirling_remainder_rescale_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 0) (var 2) (var 3) ⟶ le one (var 5) ⟶
      crossEquivalent nameF nameF
        (data (var 5*var 0) (var 5*var 1) (var 5*var 2) (var 3) (var 4))
        (data (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 6 (.impI (.impI (rescale _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBinetStirlingRescale
