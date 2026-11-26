import IPRADerivations.Analysis.Barnes.FunctionalEquations.GaussianBarnesCanonicalNamedHyperfactorialPowerStep
import IPRADerivations.Analysis.Barnes.FunctionalEquations.GaussianBarnesCanonicalNamedPoleFreeRecurrence
import IPRADerivations.Analysis.Gamma.Names.PoleFree.GaussianGammaNamedPoleFreeProperness

/-! # Matching the actual shifted Barnes denominator on named inputs -/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNamedHyperfactorialBarnesStep

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalNamedHyperfactorial (barnes_source barnes_regular)
open GaussianBarnesCanonicalNamedHyperfactorialExponentStep (shifted_center_is_input restored_center)
open GaussianBarnesCanonicalNamedHyperfactorialPowerStep (gammaPowerF gammaPowerData)
open GaussianBarnesCanonicalOrdinaryUpperGrowth (minusOne valueData)
open GaussianEulerNamedShiftInput (shiftF shiftData)
open GaussianNameArithmetic (addF addData multiplyF multiplyData)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianGammaCanonicalExponent (constantF)
open GaussianLogGammaEulerNamed (source)
open GaussianGammaAdjacentCutoff (multiply_cross)
open ComplexLogarithmRemainder (bounded normSq_neg normSq_one oneCode)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "G" => GaussianBarnesCanonicalOrdinaryUpperGrowth.nameF
local notation "P" => GaussianGammaNamedPoleFree.nameF
local notation "Pd" => GaussianGammaNamedPoleFree.data

def centerF (f : PR 2) : PR 2 := addF f constantF
def centerData (x : PTm n) : PTm n := addData x minusOne
def gammaSource (f : PR 2) (x R E : PTm n) : Fm PTm n :=
  GaussianGammaNamedPoleFree.source f x (R+one+one) E ⋏
    GaussianGammaNamedPoleFree.source (shiftF (centerF f)) (shiftData (centerData x)) (R+one+one) E

def denominatorF (f : PR 2) : PR 2 := multiplyF (G f) (gammaPowerF f)
def denominatorData (f : PR 2) (x M R : PTm n) : PTm n :=
  multiplyData (G f) (gammaPowerF f) (valueData x R) (gammaPowerData f x M R)

private theorem minus_source : Γ ⊢[PRAAx] GaussianBarnesCanonicalNamedDemand.source constantF minusOne one := by
  have h : Γ ⊢[PRAAx] bounded (ComplexLogarithmRemainder.neg oneCode) (one*one) :=
    le_congr ((normSq_neg oneCode).eqTrans normSq_one).eqSymm (by ipra_ring) (le_refl one)
  exact GaussianBarnesCanonicalNamed.constant_source _ _ _ (.andI (le_refl one) h)

theorem centered_source (f : PR 2) (x M R : PTm n) (h : Γ ⊢[PRAAx] source f x M R) :
    Γ ⊢[PRAAx] GaussianBarnesCanonicalNamedDemand.source (centerF f) (centerData x) (R+one) :=
  GaussianBarnesCanonicalNamedIncrementEndpoints.shifted_source f constantF x minusOne R
    (barnes_source f x M R h) minus_source

theorem gamma_matches (f : PR 2) (x M R E : PTm n) (h : Γ ⊢[PRAAx] source f x M R)
    (hG : Γ ⊢[PRAAx] gammaSource f x R E) :
    Γ ⊢[PRAAx] crossEquivalent (gammaPowerF f) (P (shiftF (centerF f))) (gammaPowerData f x M R)
      (Pd (shiftData (centerData x)) (R+one+one) E) := by
  let y := shiftData (centerData x)
  let g := shiftF (centerF f)
  let S := R+one+one
  have move := GaussianGammaNamedPoleFree.proper g f y x S E hG.andE₂ hG.andE₁
    (restored_center f x h.andE₁.andE₁)
  have first := GaussianLogGammaEulerNamedExponential.pole_free_equivalent f x M R S E h hG.andE₁
  exact cross_trans _ _ _ _ _ _ first (cross_symm _ _ _ _ move)

theorem denominator_step (f : PR 2) (x M R S E : PTm n) (h : Γ ⊢[PRAAx] source f x M R)
    (hNext : Γ ⊢[PRAAx] source (shiftF f) (shiftData x) M S) (hG : Γ ⊢[PRAAx] gammaSource f x R E) :
    Γ ⊢[PRAAx] crossEquivalent (G (shiftF f)) (denominatorF f) (valueData (shiftData x) S)
      (denominatorData f x M R) := by
  let cf := centerF f
  let cx := centerData x
  let sf := shiftF f
  let sx := shiftData x
  let t := shiftF cf
  let y := shiftData cx
  let U := R+one
  let V := U+one
  let d := valueData x R
  let a := Pd y V E
  let b := gammaPowerData f x M R
  have hc := centered_source f x M R h
  have ht := GaussianBarnesCanonicalNamedFunctionalEquation.shifted_source cf cx U hc
  have hq := centered_source sf sx M S hNext
  have center := cross_trans (centerF sf) f t (centerData sx) x y
    (shifted_center_is_input f x h.andE₁.andE₁)
    (cross_symm t f y x (restored_center f x h.andE₁.andE₁))
  have moved := GaussianBarnesCanonicalNamedFrozen.proper (centerF sf) t (centerData sx) y (S+one) V hq ht center
  have shiftedGamma : Γ ⊢[PRAAx] GaussianGammaNamedPoleFree.source t y V E := hG.andE₂
  have step := GaussianBarnesCanonicalNamedPoleFreeRecurrence.recurrence cf cx U E hc shiftedGamma
  have gReg := barnes_regular f x M R h
  have pReg := GaussianGammaNamedPoleFree.name_regular t y V E shiftedGamma
  have expReg := GaussianLogGammaEulerNamedExponential.name_regular f x M R h
  have changeGamma := multiply_cross (G f) (G f) (P t) (gammaPowerF f) d d a b
    gReg gReg pReg expReg (cross_refl _ _ gReg)
    (cross_symm (gammaPowerF f) (P t) b a (gamma_matches f x M R E h hG))
  exact cross_trans _ _ _ _ _ _ moved (cross_trans _ _ _ _ _ _ step changeGamma)

theorem actual_original_named_Barnes_hyperfactorial_denominator_step_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (let x := var 0; let M := var 1; let R := var 2; let S := var 3; let E := var 4
       source f x M R ⟶ source (shiftF f) (shiftData x) M S ⟶ gammaSource f x R E ⟶
         crossEquivalent (G (shiftF f)) (denominatorF f) (valueData (shiftData x) S) (denominatorData f x M R)) :=
  closeUniv 5 (.impI (.impI (.impI (denominator_step f _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp0.wk Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNamedHyperfactorialBarnesStep
