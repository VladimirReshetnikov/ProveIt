import IPRADerivations.Analysis.Barnes.FunctionalEquations.Duplication.GaussianBarnesCanonicalDuplicationShift
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.NamedValues.GaussianLogGammaEulerPositiveAxis
import IPRADerivations.Analysis.Stirling.Duplication.GaussianStirlingNativeDuplication

/-! # The Barnes half-step multiplier is the original Gamma duplication factor -/

set_option autoImplicit false
set_option maxHeartbeats 1300000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDuplicationGamma

open_ipra
open GaussianBarnesCanonicalHyperfactorial (specialLogData logarithm_source)
open GaussianBarnesCanonicalHyperfactorialPowerStep (gammaPowerF gammaPowerData gamma_power_regular logarithm_regular exponential_input)
open GaussianBarnesCanonicalDuplicationShift (gammaPairF gammaPairData)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianRationalHorner (positive_product)
open GaussianStirlingGammaLogarithm (gammaData gamma_regular arg)
open GaussianStirlingNativeDuplication (halfNumerator halfDenominator half_source)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "L" => GaussianLogGammaEulerCofinal.nameF
local notation "G" => GaussianGammaReciprocalInverse.gammaF
local notation "S" => GaussianStirlingGammaLogarithm.source

theorem canonical_gamma (A D : PTm n) (h : Γ ⊢[PRAAx] S A D) :
    Γ ⊢[PRAAx] crossEquivalent gammaPowerF G (gammaPowerData A D) (gammaData A D) := by
  let x := specialLogData A D
  let R := GaussianNameBounds.U L x
  let W := GaussianLogGammaEulerExponentialLimit.disk A zero D zero
  have hl := logarithm_source A D h.andE₁ h.andE₂
  have input := exponential_input L x (logarithm_regular A D h.andE₁ h.andE₂)
  have wide := GaussianExponentialRadiusIndependence.input_widen L R W x input (le_add_right R two)
  exact cross_trans _ _ _ _ _ _ (GaussianExponentialRadiusIndependence.same_input_cross L R W x input wide)
    (GaussianLogGammaEulerPositiveAxis.axis_exponential_gamma A D zero hl)

private theorem gamma_data_congr {a b c d : PTm n} (hn : Γ ⊢[PRAAx] a ≐ c) (hd : Γ ⊢[PRAAx] b ≐ d) :
    Γ ⊢[PRAAx] gammaData a b ≐ gammaData c d := by
  have sameArg : Γ ⊢[PRAAx] arg a ≐ arg c := by
    ipra_congr (arg (var 0) : PTm 1) with [hn] using [arg]
  exact GaussianGammaFactorialValues.gamma_fields_congr sameArg hn hd hd

theorem second_argument (A B : PTm n) (h : Γ ⊢[PRAAx] S A B) : Γ ⊢[PRAAx]
    crossEquivalent gammaPowerF G (gammaPowerData (A+B) (two*B))
      (gammaData (halfNumerator A (two*B)) (halfDenominator (two*B))) := by
  let D := two*B
  let b := A+B
  let y := gammaData (two*b) (two*D)
  let z := gammaData (halfNumerator A D) (halfDenominator D)
  have hD : Γ ⊢[PRAAx] le one D := positive_product two B (le_succ_self one) h.andE₂
  have hb : Γ ⊢[PRAAx] S b D := .andI (le_trans h.andE₁ (le_add_right A B)) hD
  have halfEq : Γ ⊢[PRAAx] y ≐ z := gamma_data_congr (by dsimp [b,D,halfNumerator]; ipra_ring)
    (by dsimp [D,halfDenominator]; ipra_ring)
  have rescale := GaussianStirlingNativeDuplication.gamma_rescale b D two hb (le_succ_self one)
  have aligned := GaussianGammaCompactCutoffAlignment.cross_data_congr G G y z (gammaData b D) (gammaData b D)
    halfEq (.eqRefl _) rescale
  exact cross_trans _ _ _ _ _ _ (canonical_gamma b D hb) (cross_symm _ _ _ _ aligned)

theorem pair_binding (A B : PTm n) (h : Γ ⊢[PRAAx] S A B) :
    Γ ⊢[PRAAx] crossEquivalent gammaPairF GaussianStirlingNativeDuplication.leftF (gammaPairData A B)
      (GaussianStirlingNativeDuplication.leftData A (two*B)) := by
  let D := two*B
  have hD : Γ ⊢[PRAAx] le one D := positive_product two B (le_succ_self one) h.andE₂
  have hAD : Γ ⊢[PRAAx] S A D := .andI h.andE₁ hD
  have hb := le_trans h.andE₁ (le_add_right A B)
  exact multiply_cross gammaPowerF G gammaPowerF G (gammaPowerData A D) (gammaData A D)
    (gammaPowerData (A+B) D) (gammaData (halfNumerator A D) (halfDenominator D))
    (gamma_power_regular A D h.andE₁ hD) (gamma_regular A D hAD)
    (gamma_power_regular (A+B) D hb hD) (gamma_regular _ _ (half_source A D hAD))
    (canonical_gamma A D hAD) (second_argument A B h)

theorem duplication_multiplier (A B : PTm n) (h : Γ ⊢[PRAAx] S A B) :
    Γ ⊢[PRAAx] crossEquivalent gammaPairF GaussianStirlingNativeDuplication.rightF (gammaPairData A B)
      (GaussianStirlingNativeDuplication.rightData A (two*B)) :=
  cross_trans _ _ _ _ _ _ (pair_binding A B h)
    (GaussianStirlingNativeDuplication.native_duplication A (two*B)
      (.andI h.andE₁ (positive_product two B (le_succ_self one) h.andE₂)))

theorem actual_Barnes_duplication_Gamma_multiplier_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (let A := var 0; let B := var 1
       S A B ⟶ crossEquivalent gammaPairF GaussianStirlingNativeDuplication.rightF (gammaPairData A B)
        (GaussianStirlingNativeDuplication.rightData A (two*B))) :=
  closeUniv 2 (.impI (duplication_multiplier _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDuplicationGamma
