import IPRADerivations.Analysis.Gamma.Zeta.Dirichlet.GaussianGammaZetaDirichletOverlap
import IPRADerivations.Analysis.Gamma.Zeta.Dirichlet.GaussianGammaZetaDirichletParameterRate
import IPRADerivations.Analysis.Names.GaussianNameConjugation

/-!
# Dirichlet values at equal rational parameters in different encodings

The original cofinal names agree when their native numerator and
denominator encode the same rational point. The proof also allows
independent admitted radii and reciprocal real-part margins.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaDirichletPresentation

open_ipra
open ComplexLogarithmRemainder (re)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEulerIntegralGammaIdentification (source)
open GaussianEulerLowerPowerCoefficients (realLower)
open GaussianGammaZetaDirichletCofinal (nameF regular)
open GaussianGammaZetaDirichletParameterRate (demand original_demand_rate)
open GaussianNameEquivalence (crossEquivalent cross_trans)
open GaussianNamedInverseRate (rateNumerator rateDenominator denominator_positive rate_at)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalHorner (ofGaussian)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "cd" => GaussianGammaZetaDirichletCofinal.data

private theorem margin_weaken (z B A J : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (hAJ : Γ ⊢[PRAAx] le A J) (h : Γ ⊢[PRAAx] realLower z A B) :
    Γ ⊢[PRAAx] realLower z J B := by
  let x := ZT.ofNat B
  let y := ZT.ofNat A*re z
  have e := zle_toZ h
  have d := natEq (eq_add_of_le hAJ)
  apply PolynomialBisection.zle_scale_cancel (c := A) hA
  apply zle_of_toZ (J*PolynomialBisection.slack x y+monus J A*B)
  dsimp only [PolynomialBisection.slack,x,y]
  simp only [ZT.toZ_mul,ZT.toZ_ofNat] at e ⊢
  ipra_simps
  linear_combination 𝔞(J)*e - 𝔞(B)*d

theorem widen_source (z R S B A J : PTm n) (h : Γ ⊢[PRAAx] source z R B A)
    (hRS : Γ ⊢[PRAAx] le R S) (hAJ : Γ ⊢[PRAAx] le A J) :
    Γ ⊢[PRAAx] source z S B J := by
  have hA := h.andE₁.andE₁
  have disk := ComplexLogarithmRemainder.bounded_mono h.andE₁.andE₂.andE₁.andE₂ (mul_le_mul_right B hRS)
  exact .andI (.andI (le_trans hA hAJ) (.andI (.andI h.andE₁.andE₂.andE₁.andE₁ disk)
    (margin_weaken z B A J hA hAJ h.andE₁.andE₂.andE₂))) (le_trans h.andE₂ hRS)

private theorem same_guard_observations (p z w R B D A : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B A) (hw : Γ ⊢[PRAAx] source w R D A)
    (he : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (cd z R B A)) (ap2 nameF p (cd w R D A)) (num 3) (unit p) := by
  let U := unit (demand p R A)
  have hu := unit_positive (Γ := Γ) (demand p R A)
  have hp := unit_positive (Γ := Γ) p
  have d := GaussianNameConjugation.equal_distance (ofGaussian z B) (ofGaussian w D) U hu he
  have e := distance_radius_mono _ _ zero U one U hu hu (by ipra_le 𝔞 U) d
  have rate := original_demand_rate p z w R B D A hz hw e
  exact distance_radius_mono _ _ _ _ (num 3) (unit p) (denominator_positive _ _ _ hp) hp
    (le_of_eq_add (d := zero) (by unfold rateNumerator rateDenominator; ipra_ring))
    (rate_at nameF nameF (cd z R B A) (cd w R D A) one (unit p) p p rate)

theorem same_guard (z w R B D A : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B A) (hw : Γ ⊢[PRAAx] source w R D A)
    (he : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] crossEquivalent nameF nameF (cd z R B A) (cd w R D A) := by
  refine GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (num 3)
    (regular z R B A hz) (regular w R D A hw) (.allI ?_)
  let sh (a : PTm n) := Syn.shift a
  let Δ := Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh A) := by simpa [Fm.shift,Syn.shift,sh,Δ] using hz.shift
  have hs' : Δ ⊢[PRAAx] source (sh w) (sh R) (sh D) (sh A) := by simpa [Fm.shift,Syn.shift,sh,Δ] using hw.shift
  have h : Δ ⊢[PRAAx] ofGaussian (sh z) (sh B) ≐ ofGaussian (sh w) (sh D) := by
    simpa [Fm.shift,Syn.shift,sh,Δ] using he.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,GaussianGammaZetaDirichletCofinal.data,
    GaussianGammaZetaMellinDampedImproper.subst_parameters,PTm.subst_num,Syn.shift,sh,Δ] using
    same_guard_observations (var 0) (sh z) (sh w) (sh R) (sh B) (sh D) (sh A) hs hs' h

theorem original_cross_encoding (z w R S B D A J : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B A) (hw : Γ ⊢[PRAAx] source w S D J)
    (he : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] crossEquivalent nameF nameF (cd z R B A) (cd w S D J) := by
  let U := R+S
  let V := A+J
  have ha := widen_source z R U B A V hz (le_add_right R S) (le_add_right A J)
  have hj := widen_source w S U D J V hw (le_add_left S R) (le_add_left J A)
  have xa := GaussianGammaZetaDirichletOverlap.original_overlap z R U B A V hz ha
  have xy := same_guard z w U B D V ha hj he
  have yb := GaussianGammaZetaDirichletOverlap.original_overlap w U S D V J hj hw
  exact cross_trans _ _ _ _ _ _ xa (cross_trans _ _ _ _ _ _ xy yb)

theorem actual_original_Dirichlet_cross_encoding_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (source (var 0) (var 2) (var 4) (var 6) ⟶ source (var 1) (var 3) (var 5) (var 7) ⟶
        (ofGaussian (var 0) (var 4) ≐ ofGaussian (var 1) (var 5)) ⟶
        crossEquivalent nameF nameF (cd (var 0) (var 2) (var 4) (var 6)) (cd (var 1) (var 3) (var 5) (var 7))) :=
  closeUniv 8 (.impI (.impI (.impI (original_cross_encoding _ _ _ _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianGammaZetaDirichletPresentation
