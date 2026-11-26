import IPRADerivations.Analysis.Exponential.GaussianRightHalfPlaneExponentialSmall
import IPRADerivations.Analysis.Exponential.GaussianRightHalfPlaneExponentialCharts
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.GaussianLogGammaEulerHead

/-!
# The exponential of the original canonical logarithm

Both small-chart conclusions used by the chart proof come from the
actual separated square comparison. The target is the same signed
fraction code used in the finite Euler head.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneLogarithmExponential

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaCanonicalExponent (constantF)
open GaussianGammaFiniteApproximantName (exponentialInputData)
open GaussianNameEquivalence (crossEquivalent cross_trans)
open GaussianRightHalfPlaneLogarithm (source nameF data)
open GaussianRightHalfPlaneExponentialCharts (signedPoint negativePoint)
open GaussianRightHalfPlaneExponentialMargin (point)
open GaussianLogGammaEulerHead (argument)
open RationalArithmetic (select select_zero select_one)
open ComplexLogarithmRemainder (code)
open GaussianRationalHorner (ofGaussian)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "E" => GaussianRadiusExponentialName.nameF

private theorem argument_coordinates (A B D neg a b : PTm n) (ha : Γ ⊢[PRAAx] select neg B zero ≐ a)
    (hb : Γ ⊢[PRAAx] select neg zero B ≐ b) :
    Γ ⊢[PRAAx] argument A B D neg ≐ ofGaussian (code (ZT.ofNat A) ⟨a,b⟩) D := by
  have ec := Prf.eqCongr (Γ := Γ) (Ax := PRAAx)
    (ofGaussian (code (ZT.ofNat (var 0)) ⟨var 1,var 2⟩) (var 3) : PTm 4)
    (σ := ![A,select neg B zero,select neg zero B,D]) (σ' := ![A,a,b,D])
    (fun j => by fin_cases j; exact .eqRefl _; exact ha; exact hb; exact .eqRefl _)
  simpa [argument,ZT.subst,ZT.ofNat] using ec

theorem point_binding (A B D neg : PTm n) (h : Γ ⊢[PRAAx] neg ≐ zero ⋎ neg ≐ one) :
    Γ ⊢[PRAAx] signedPoint A B D neg ≐ argument A B D neg := by
  refine .orE h ?_ ?_
  · exact (select_zero neg (point A B D) (negativePoint A B D) Prf.hyp0).eqTrans
      (argument_coordinates A B D neg B zero
        (select_zero neg B zero Prf.hyp0) (select_zero neg zero B Prf.hyp0)).eqSymm
  · exact (select_one neg (point A B D) (negativePoint A B D) Prf.hyp0).eqTrans
      (argument_coordinates A B D neg zero B
        (select_one neg B zero Prf.hyp0) (select_one neg zero B Prf.hyp0)).eqSymm

theorem recovery (A B D neg : PTm n) (h : Γ ⊢[PRAAx] source A D neg) :
    Γ ⊢[PRAAx] crossEquivalent (E nameF) constantF
      (exponentialInputData nameF (data A B D neg)) (argument A B D neg) := by
  have hA := h.andE₁.andE₁
  have hD := h.andE₂
  have e := GaussianRightHalfPlaneExponentialCharts.recover A B D neg h
    (GaussianRightHalfPlaneExponentialSmall.product_recovery A B D hA.wk Prf.hyp0 hD.wk)
    (GaussianRightHalfPlaneExponentialSmall.product_recovery B A D
      (le_trans hA.wk (le_of_lt Prf.hyp0)) (le_of_lt Prf.hyp0) hD.wk)
  exact cross_trans _ _ _ _ _ _ e
    (GaussianGammaWeierstrassApproximant.constant_data_cross _ _ (point_binding A B D neg h.andE₁.andE₂))

theorem actual_right_half_plane_logarithm_exponential_recovers_input_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (source (var 0) (var 2) (var 3) ⟶ crossEquivalent (E nameF) constantF
        (exponentialInputData nameF (data (var 0) (var 1) (var 2) (var 3)))
        (argument (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (recovery _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneLogarithmExponential
