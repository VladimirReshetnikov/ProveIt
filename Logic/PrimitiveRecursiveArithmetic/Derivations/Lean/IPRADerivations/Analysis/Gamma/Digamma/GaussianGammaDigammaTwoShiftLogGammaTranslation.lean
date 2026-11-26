import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianLogGammaEulerPositiveAxis
import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianLogGammaEulerRationalContinuity

/-!
# Original positive log-Gamma under a small rational translation

The chart repair changes each argument from a/b to (a+u)/b.
The actual positive log-Gamma programs at these two encodings have
an independent error proportional to u/b, with a coefficient obtained
from a shared disk and inverse real margin.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftLogGammaTranslation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (normSq code eval_re_code eval_im_code)
open GaussianLogGammaEulerResidualDomain (native)
open GaussianLogGammaEulerRationalContinuity (response)
open GaussianNamedInverseRate (independentRate)
open GaussianRootAlgebra (sub equal equal_of_values normSq_equal re_sub im_sub)
open GaussianStirlingGammaLogarithm (source logGammaF logGammaData)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

private theorem axis_point (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source a b zero :=
  .andI (.andI h.andE₁ (.orI₁ (.eqRefl _))) h.andE₂

theorem axis_displacement (a u : PTm n) :
    Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (sub (native (a+u) zero zero) (native a zero zero)) u := by
  let e := sub (native (a+u) zero zero) (native a zero zero)
  let v := code (ZT.ofNat u) (ZT.ofNat zero)
  have he : Γ ⊢[PRAAx] equal e v := by
    refine equal_of_values ?_ ?_
    · simp only [e,v,re_sub,native,eval_re_code,ZT.toZ_ofNat]
      ipra_simps
      ring
    · simp only [e,v,im_sub,native,eval_im_code,ZT.toZ_ofNat]
      ipra_simps
      ring
  have hV : Γ ⊢[PRAAx] normSq v ≐ u*u := by
    apply deriveNat
    simp only [v,ComplexLogarithmRemainder.normSq_code,ZT.toZ_ofNat]
    ipra_simps
    ring
  exact le_congr ((normSq_equal he).eqTrans hV).eqSymm (.eqRefl _) (le_refl _)

def domain (a b u K C : PTm n) : Fm PTm n :=
  source a b ⋏ (le one K ⋏ (le b (K*a) ⋏ (le (a+(a+u)) (C*b) ⋏
    GaussianRightHalfPlaneLogarithmIncrementMargin.smallStep u K C b)))

theorem original_rate (a b u K C : PTm n) (hs : Γ ⊢[PRAAx] domain a b u K C) :
    Γ ⊢[PRAAx] independentRate logGammaF logGammaF (logGammaData (a+u) b) (logGammaData a b)
      (response K C*u) b := by
  let F := GaussianLogGammaEulerCofinal.nameF
  let x := GaussianLogGammaEulerCofinal.canonicalData (a+u) zero b zero
  let y := GaussianLogGammaEulerCofinal.canonicalData a zero b zero
  have ha := hs.andE₁
  have hh : Γ ⊢[PRAAx] source (a+u) b := .andI (le_trans ha.andE₁ (le_add_right a u)) ha.andE₂
  have left := axis_point a b ha
  have right := axis_point (a+u) b hh
  have hm := hs.andE₂.andE₂.andE₁
  have hm' : Γ ⊢[PRAAx] le b (K*(a+u)) := by ipra_le sl hm+𝔞 K*𝔞 u
  have hC := hs.andE₂.andE₂.andE₂.andE₁
  have hC' : Γ ⊢[PRAAx] le (a+zero+(a+u)+zero) (C*b) := by ipra_le sl hC
  have input : Γ ⊢[PRAAx] GaussianLogGammaEulerTaylorUniform.source a zero zero (a+u) zero zero b u K C :=
    .andI left (.andI right (.andI (axis_displacement a u) (.andI hs.andE₂.andE₁
      (.andI hm (.andI hm' (.andI hC' hs.andE₂.andE₂.andE₂.andE₂))))))
  have raw := GaussianLogGammaEulerRationalContinuity.independent_rate a zero zero (a+u) zero zero b u K C input
  exact GaussianNamedRateTransport.transport F F logGammaF logGammaF x y (logGammaData (a+u) b) (logGammaData a b)
    (response K C*u) b ha.andE₂ raw
    (GaussianNameEquivalence.cross_symm _ _ _ _ (GaussianLogGammaEulerPositiveAxis.equivalent (a+u) b zero right))
    (GaussianNameEquivalence.cross_symm _ _ _ _ (GaussianLogGammaEulerPositiveAxis.equivalent a b zero left))

theorem actual_original_log_Gamma_chart_translation_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (domain (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
        independentRate logGammaF logGammaF (logGammaData (var 0+var 2) (var 1)) (logGammaData (var 0) (var 1))
          (response (var 3) (var 4)*var 2) (var 1)) :=
  closeUniv 5 (.impI (original_rate _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftLogGammaTranslation
