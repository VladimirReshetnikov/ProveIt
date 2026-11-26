import IPRADerivations.Analysis.GaussianEulerCompactPowerParameterRate
import IPRADerivations.Analysis.GaussianGammaZetaDirichletReciprocalRow
import IPRADerivations.Analysis.GaussianGammaZetaMellinReciprocalRate

/-!
# Parameter rates for the original Mellin and Dirichlet rows

The compact Euler-power modulus applies to the actual Mellin product at
a fixed time and to each actual Dirichlet term on a bounded prefix.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaParameterRates

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCompactLogarithmBounds (domain)
open GaussianEulerCompactPowerParameterRate (gain original_power_rate)
open GaussianEulerExponentCompactBounds (source)
open GaussianEulerIntegrandName (powerF powerData)
open GaussianEulerPositiveScalingConstant (inverseF inverseData shifted_power_data shifted_coefficient)
open GaussianGammaEulerHeadShift (shifted)
open GaussianGammaZetaMellinIntegrand (reciprocalF reciprocalData denominatorF denominatorData)
open GaussianNamedDifferenceRate (rate_parameters_congr self_rate)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedMultiplyRate (leadingNumerator leadingDenominator)
open GaussianNameEquivalence (crossEquivalent)
open GaussianRationalHorner (ofGaussian qadd)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalSyntheticDivision (qone qadd_congr)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem shifted_distance (z w B D H N : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D) (hN : Γ ⊢[PRAAx] le one N)
    (h : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w D) H N) :
    Γ ⊢[PRAAx] distanceBounded (ofGaussian (shifted z B) B) (ofGaussian (shifted w D) D) H N := by
  have left := (qadd_congr (.eqRefl qone) (shifted_coefficient z B hB).eqSymm).eqTrans
    (GaussianEulerIntegrationByPartsLinear.coefficient_plus_one (shifted z B) B hB)
  have right := (qadd_congr (.eqRefl qone) (shifted_coefficient w D hD).eqSymm).eqTrans
    (GaussianEulerIntegrationByPartsLinear.coefficient_plus_one (shifted w D) D hD)
  have raw := GaussianNameRingLaws.sum_left_error _ _ qone H N hN h
  exact GaussianRationalDistanceOrder.distance_congr
    ((GaussianRationalLinearProduct.qadd_commutative _ _).eqTrans left)
    ((GaussianRationalLinearProduct.qadd_commutative _ _).eqTrans right) (.eqRefl _) (.eqRefl _) raw

private theorem dirichlet_is_power (z B j : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hj : Γ ⊢[PRAAx] le one j) :
    Γ ⊢[PRAAx] crossEquivalent inverseF powerF (inverseData z B j one) (powerData (shifted z B) B one j) := by
  have e := GaussianGammaZetaDirichletReciprocalRow.inverse_reciprocal z B j one
    (.andI hB (.andI hj (le_refl one)))
  exact GaussianGammaCompactCutoffAlignment.cross_data_congr inverseF powerF _ _ _ _
    (.eqRefl _) (shifted_power_data z B one j hB).eqSymm e

theorem dirichlet_rate (z w R B D E j H N : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B E) (hw : Γ ⊢[PRAAx] source w R D E)
    (hj : Γ ⊢[PRAAx] le one j) (hE : Γ ⊢[PRAAx] le j E) (hN : Γ ⊢[PRAAx] le one N)
    (hd : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w D) H N) :
    Γ ⊢[PRAAx] independentRate inverseF inverseF (inverseData z B j one) (inverseData w D j one)
      (gain (R+one) E one*H) N := by
  have ha := hz.andE₁
  have hb := hw.andE₁
  have hza : Γ ⊢[PRAAx] source (shifted z B) (R+one) B E :=
    .andI ha (.andI hz.andE₂.andE₁ (GaussianGammaEulerShiftLimit.shifted_bound z R B hz.andE₂.andE₂))
  have hwb : Γ ⊢[PRAAx] source (shifted w D) (R+one) D E :=
    .andI hb (.andI hw.andE₂.andE₁ (GaussianGammaEulerShiftLimit.shifted_bound w R D hw.andE₂.andE₂))
  have ht : Γ ⊢[PRAAx] domain one j E one :=
    .andI (.andI (le_refl one) hj) (.andI
      (le_congr (.eqRefl _) (by ipra_ring) hE) (le_congr (.eqRefl _) (one_mul j).eqSymm hj))
  have hr := original_power_rate (shifted z B) (shifted w D) (R+one) B D E one one j H N
    (.andI hza (.andI hwb (.andI ht (.andI hN (shifted_distance z w B D H N ha hb hN hd)))))
  exact GaussianNamedRateTransport.transport powerF powerF inverseF inverseF
    (powerData (shifted z B) B one j) (powerData (shifted w D) D one j)
    (inverseData z B j one) (inverseData w D j one) (gain (R+one) E one*H) N hN hr
    (dirichlet_is_power z B j ha hj) (dirichlet_is_power w D j hb hj)

def mellinGain (R E T : PTm n) : PTm n := E*gain R E T

@[simp] theorem subst_mellinGain {m : ℕ} (σ : Fin n → PTm m) (R E T : PTm n) :
    Syn.subst σ (mellinGain R E T) = mellinGain (Syn.subst σ R) (Syn.subst σ E) (Syn.subst σ T) := by
  simp [mellinGain]

theorem mellin_rate (z w R B D E T a b H N : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerCompactPowerParameterRate.input z w R B D E T a b H N) :
    Γ ⊢[PRAAx] independentRate GaussianGammaZetaMellinIntegrand.nameF GaussianGammaZetaMellinIntegrand.nameF
      (GaussianGammaZetaMellinIntegrand.data z B a b) (GaussianGammaZetaMellinIntegrand.data w D a b)
      (mellinGain R E T*H) N := by
  let x := powerData z B a b
  let y := powerData w D a b
  let t := reciprocalData a b
  let f := GaussianGammaZetaMellinIntegrand.nameF
  let d := @GaussianGammaZetaMellinIntegrand.data n
  let ht := h.andE₂.andE₂.andE₁
  have den := h.andE₂.andE₂.andE₂.andE₁
  have hx := GaussianEulerIntegrandName.power_regular z B a b (.andI h.andE₁.andE₁ ht.andE₁)
  have hy := GaussianEulerIntegrandName.power_regular w D a b (.andI h.andE₂.andE₁.andE₁ ht.andE₁)
  have hr := GaussianNameReciprocal.name_fast denominatorF b (denominatorData a b)
    (GaussianGammaZetaMellinIntegrand.denominator_regular a b)
    (GaussianGammaZetaMellinIntegrand.denominator_apart a b ht.andE₁.andE₁ ht.andE₁.andE₂)
  have raw := GaussianNamedMultiplyRate.independent_rate powerF reciprocalF powerF reciprocalF x t y t
    (gain R E T*H) N zero one E (GaussianNameBounds.U powerF y)
    den (le_refl one) hx hr hy hr (GaussianGammaZetaMellinReciprocalRate.reciprocal_samples a b E T ht)
    (GaussianNameBounds.all_samples_bounded powerF y hy) (original_power_rate z w R B D E T a b H N h)
    (self_rate reciprocalF t hr)
  exact rate_parameters_congr f f (d z B a b) (d w D a b)
    (leadingNumerator (gain R E T*H) N zero one E (GaussianNameBounds.U powerF y))
    (leadingDenominator N one) (mellinGain R E T*H) N
    (by unfold leadingNumerator mellinGain; ipra_ring) (by unfold leadingDenominator; ipra_ring) raw

theorem actual_original_Mellin_parameter_row_rate_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
      (GaussianEulerCompactPowerParameterRate.input (var 0) (var 1) (var 2) (var 3) (var 4)
        (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) ⟶
        independentRate GaussianGammaZetaMellinIntegrand.nameF GaussianGammaZetaMellinIntegrand.nameF
          (GaussianGammaZetaMellinIntegrand.data (var 0) (var 3) (var 7) (var 8))
          (GaussianGammaZetaMellinIntegrand.data (var 1) (var 4) (var 7) (var 8))
          (mellinGain (var 2) (var 5) (var 6)*var 9) (var 10)) :=
  closeUniv 11 (.impI (mellin_rate _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaZetaParameterRates
