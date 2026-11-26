import IPRADerivations.Analysis.Stirling.Binet.Laplace.Moments.GaussianBinetLaplaceMomentForwardMargin
import IPRADerivations.Analysis.Stirling.Binet.Laplace.Moments.GaussianBinetLaplaceMomentBackwardQuotient
import IPRADerivations.Analysis.Stirling.Binet.Laplace.Moments.GaussianBinetLaplaceMomentVariation
import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.GaussianNamedDifferenceQuotientProperness
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateComposition
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateTransport
import IPRADerivations.Analysis.Euler.PowerScaling.GaussianEulerPowerScalingCompactRate

/-!
# Two-sided moment quotient on a fixed positive margin

Translate the backward quotient to the exact original right quotient at
the lower endpoint. Variation of the successor moment pays for moving
the target back to the same base as the forward quotient.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentTwoSidedMargin

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianBinetLaplaceMomentBackwardQuotient (forwardData)
open GaussianBinetLaplaceMomentBackwardWindow (lowerData lowerNumerator)
open GaussianBinetLaplaceMomentForwardQuotient (quotientF quotientData targetF targetData)
open GaussianBinetLaplaceMomentForwardMargin (upperRadius forward_rate)
open GaussianBinetLaplaceMomentImproper (nameF data regular)
open GaussianBinetLaplaceMomentRescale (rational_proper)
open GaussianDominantPairAlgebra (radiusNumerator)
open GaussianLogGammaEulerResidualRadius (radius source_of_right_half_plane)
open GaussianNameEquivalence (cross_refl cross_symm)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner (positive_product)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (LeanProofs.IPRA.Q.mk Γ t)
local notation "realSource" => GaussianLogGammaEulerResidualDomain.source
local notation "Bdata" => GaussianBinetLaplaceMomentBackwardQuotient.quotientData
local notation "Fbudget" => GaussianBinetLaplaceMomentForwardMargin.linearBudget
local notation "gain" => GaussianBinetLaplaceMomentVariation.gain

def source (X D R K H Q : PTm n) : Fm PTm n :=
  realSource X zero D zero R ⋏ ((le one K ⋏ le D (K*X)) ⋏
    (le one H ⋏ (le one Q ⋏ le (two*(K*H)) Q)))

def backwardBudget (j K H : PTm n) : PTm n := Fbudget j (two*K) H + gain (succ j) (two*K)*H

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (X D R K H Q : PTm n) :
    (source X D R K H Q).subst σ =
      source (Syn.subst σ X) (Syn.subst σ D) (Syn.subst σ R) (Syn.subst σ K) (Syn.subst σ H) (Syn.subst σ Q) := by
  simp [source,one,two]

@[simp] theorem subst_backwardBudget {m : ℕ} (σ : Fin n → PTm m) (j K H : PTm n) :
    Syn.subst σ (backwardBudget j K H) = backwardBudget (Syn.subst σ j) (Syn.subst σ K) (Syn.subst σ H) := by
  simp [backwardBudget,two]

theorem window_geometry (X D R K H Q : PTm n) (h : Γ ⊢[PRAAx] source X D R K H Q) :
    let Y := lowerNumerator X D H Q
    Γ ⊢[PRAAx] (Y+H*D ≐ X*Q) ⋏ (le one Y ⋏ (le (D*Q) ((two*K)*Y) ⋏ le H Q)) := by
  let A := H*D
  let Y := lowerNumerator X D H Q
  have hD := h.andE₁.andE₁.andE₂
  have hK := h.andE₂.andE₁.andE₁
  have hH := h.andE₂.andE₂.andE₁
  have hM := h.andE₂.andE₁.andE₂
  have hSmall : Γ ⊢[PRAAx] le (two*(K*H)) Q := h.andE₂.andE₂.andE₂.andE₂
  have hA : Γ ⊢[PRAAx] le one A := positive_product _ _ hH hD
  have doubledStep : Γ ⊢[PRAAx] le (two*K*A) (D*Q) :=
    le_congr (by dsimp only [A]; ipra_ring) (mul_comm _ _) (mul_le_mul_right D hSmall)
  have hBound : Γ ⊢[PRAAx] le (D*Q) (K*(X*Q)) :=
    le_congr (.eqRefl _) (by ipra_ring) (mul_le_mul_right Q hM)
  have doubleA : Γ ⊢[PRAAx] le (two*A) (X*Q) :=
    RationalValueBounds.positive_cancel hK (le_congr (by ipra_ring) (.eqRefl _) (le_trans doubledStep hBound))
  have below : Γ ⊢[PRAAx] le A (X*Q) :=
    le_trans (le_congr (.eqRefl _) (by ipra_ring) (le_add_right A A)) doubleA
  have e : Γ ⊢[PRAAx] Y+A ≐ X*Q := (add_comm Y A).eqTrans (eq_add_of_le below).eqSymm
  have room : Γ ⊢[PRAAx] le (one+A) (two*A) :=
    le_congr (.eqRefl _) (by ipra_ring) (add_le_add₂ hA (le_refl A))
  have hY : Γ ⊢[PRAAx] le one Y :=
    le_of_add_le_add_right (c := A) (le_congr (.eqRefl _) e.eqSymm (le_trans room doubleA))
  have both : Γ ⊢[PRAAx] le (D*Q+D*Q) ((two*K)*(X*Q)) :=
    le_congr (.eqRefl _) (by ipra_ring) (add_le_add₂ hBound hBound)
  have twoMargin : Γ ⊢[PRAAx] le ((D*Q)+(two*K)*A) ((two*K)*(X*Q)) :=
    le_trans (add_le_add₂ (le_refl (D*Q)) doubledStep) both
  have margin : Γ ⊢[PRAAx] le (D*Q) ((two*K)*Y) :=
    le_of_add_le_add_right (c := (two*K)*A)
      (le_congr (.eqRefl _) ((congrMul (.eqRefl _) e.eqSymm).eqTrans (by ipra_ring)) twoMargin)
  have hU : Γ ⊢[PRAAx] le one (two*K) := positive_product _ _ (le_succ_self one) hK
  have step : Γ ⊢[PRAAx] le H (two*(K*H)) :=
    le_congr (one_mul H) (mul_assoc _ _ _) (mul_le_mul_right H hU)
  exact .andI e (.andI hY (.andI margin (le_trans step hSmall)))

theorem lower_source (X D R K H Q : PTm n) (h : Γ ⊢[PRAAx] source X D R K H Q) :
    let Y := lowerNumerator X D H Q
    Γ ⊢[PRAAx] realSource Y zero (D*Q) zero (radius Y zero) :=
  source_of_right_half_plane _ _ _ _
    (.andI (.andI (window_geometry X D R K H Q h).andE₂.andE₁ (.orI₁ (.eqRefl zero)))
      (positive_product _ _ h.andE₁.andE₁.andE₂ h.andE₂.andE₂.andE₂.andE₁))

theorem lower_parameter_eq (X D R K H Q : PTm n) (h : Γ ⊢[PRAAx] source X D R K H Q) :
    let Y := lowerNumerator X D H Q
    let E := D*Q
    Γ ⊢[PRAAx] (Y*Q+H*E)*D ≐ X*(E*Q) := by
  have add := natEq (window_geometry X D R K H Q h).andE₁
  apply deriveNat
  ipra_simps
  linear_combination 𝔞(D)*𝔞(Q)*add

theorem backward_rate (j X D R K H Q : PTm n) (h : Γ ⊢[PRAAx] source X D R K H Q) :
    Γ ⊢[PRAAx] independentRate quotientF targetF (Bdata j X D R H Q) (targetData j X D R)
      (backwardBudget j K H) Q := by
  let Y := lowerNumerator X D H Q
  let E := D*Q
  let S := radius Y zero
  let T := upperRadius Y E H Q
  let A := Y*Q+H*E
  let B := E*Q
  let d := data j X D R
  let e := lowerData j X D H Q
  let a := data j A B T
  let c := targetData j Y E S
  let v := targetData j X D R
  let U := two*K
  have hQ := h.andE₂.andE₂.andE₂.andE₁
  have hH := h.andE₂.andE₂.andE₁
  have hl := lower_source X D R K H Q h
  have hU := positive_product two K (le_succ_self one) h.andE₂.andE₁.andE₁
  have geom := window_geometry X D R K H Q h
  have step := geom.andE₂.andE₂.andE₂
  have eq := lower_parameter_eq X D R K H Q h
  have hu := GaussianBinetLaplaceMomentForwardMargin.upper_source Y E S H Q hl hQ
  have ha := regular j A B T hu
  have hd := regular j X D R h.andE₁
  have he := regular j Y E S hl
  have charts := rational_proper j X D R A B T h.andE₁ hu eq.eqSymm
  have moved : Γ ⊢[PRAAx] independentRate quotientF targetF (quotientData j Y E S T H Q) c (Fbudget j U H) Q :=
    forward_rate j Y E S U H Q (.andI hl (.andI (.andI hU geom.andE₂.andE₂.andE₁) (.andI hH (.andI hQ step))))
  have left := GaussianNamedDifferenceQuotientProperness.proper nameF nameF nameF nameF
    d a e e (radiusNumerator H) Q hd ha he he charts (cross_refl nameF e he)
  have hc := regular (succ j) Y E S hl
  have hv := regular (succ j) X D R h.andE₁
  have first := GaussianNamedRateTransport.transport quotientF targetF quotientF targetF
    (quotientData j Y E S T H Q) c (Bdata j X D R H Q) c (Fbudget j U H) Q hQ moved left
    (cross_refl targetF c (GaussianNameRingLaws.negative_fast _ _ hc))
  have variation := GaussianBinetLaplaceMomentVariation.ordered_rate (succ j) Y E S X D R U H Q
    (.andI (.andI hl h.andE₁) (.andI (.andI hU geom.andE₂.andE₂.andE₁) (.andI hQ (.andI step eq))))
  have second := GaussianEulerPowerScalingCompactRate.negative_rate nameF nameF
    (data (succ j) Y E S) (data (succ j) X D R) (gain (succ j) U*H) Q hc hv hQ
    (GaussianNamedRateComposition.symmetric _ _ _ _ _ _ hQ variation)
  exact GaussianNamedRateComposition.same_denominator quotientF targetF targetF
    (Bdata j X D R H Q) c v (Fbudget j U H) Q (gain (succ j) U*H) hQ first second

theorem two_sided_rate (j X D R K H Q : PTm n) (h : Γ ⊢[PRAAx] source X D R K H Q) :
    Γ ⊢[PRAAx] independentRate quotientF targetF (forwardData j X D R H Q) (targetData j X D R)
        (Fbudget j K H) Q ⋏
      independentRate quotientF targetF (Bdata j X D R H Q) (targetData j X D R) (backwardBudget j K H) Q :=
  .andI (forward_rate j X D R K H Q
    (.andI h.andE₁ (.andI h.andE₂.andE₁ (.andI h.andE₂.andE₂.andE₁
      (.andI h.andE₂.andE₂.andE₂.andE₁ (window_geometry X D R K H Q h).andE₂.andE₂.andE₂)))))
    (backward_rate j X D R K H Q h)

theorem actual_original_Binet_moment_two_sided_quotient_with_margin_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      (let j := var 0
       let X := var 1
       let D := var 2
       let R := var 3
       let K := var 4
       let H := var 5
       let Q := var 6
       source X D R K H Q ⟶
         (independentRate quotientF targetF (forwardData j X D R H Q) (targetData j X D R)
           (Fbudget j K H) Q ⋏
         independentRate quotientF targetF (Bdata j X D R H Q) (targetData j X D R) (backwardBudget j K H) Q)) :=
  closeUniv 7 (.impI (two_sided_rate _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentTwoSidedMargin
