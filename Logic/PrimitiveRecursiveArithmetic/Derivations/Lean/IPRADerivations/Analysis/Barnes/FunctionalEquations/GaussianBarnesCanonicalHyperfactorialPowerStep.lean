import IPRADerivations.Analysis.Barnes.FunctionalEquations.GaussianBarnesCanonicalHyperfactorialExponentStep
import IPRADerivations.Analysis.Exponential.GaussianExponentialAddition
import IPRADerivations.Analysis.Exponential.Names.GaussianExponentialRadiusIndependence

/-! # Exponentiating the hyperfactorial numerator increment -/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHyperfactorialPowerStep

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalHyperfactorial
  (exponentF exponentData exponent_regular powerF powerData power_regular specialLogData logarithm_source)
open GaussianBarnesCanonicalHyperfactorialExponentStep
  (stepExponentF stepExponentData step_exponent_regular incrementF incrementData totalF totalData exponent_step)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameBounds (U U_positive all_samples_bounded)
open GaussianGammaAdjacentCutoff (multiply_cross)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "E" => GaussianRadiusExponentialName.nameF
local notation "Ed" => GaussianRadiusExponentialName.data
local notation "L" => GaussianLogGammaEulerCofinal.nameF

def exponentialData (f : PR 2) (x : PTm n) : PTm n := Ed (U f x) x
abbrev gammaPowerF : PR 2 := E L
def gammaPowerData (A B : PTm n) : PTm n := exponentialData L (specialLogData A B)
abbrev stepPowerF : PR 2 := E stepExponentF
def stepPowerData (A B : PTm n) : PTm n := exponentialData stepExponentF (stepExponentData A B)
abbrev pairF : PR 2 := multiplyF gammaPowerF stepPowerF
def pairData (A B : PTm n) : PTm n := multiplyData gammaPowerF stepPowerF (gammaPowerData A B) (stepPowerData A B)
abbrev shiftedPowerF : PR 2 := multiplyF powerF pairF
def shiftedPowerData (A B : PTm n) : PTm n := multiplyData powerF pairF (powerData A B) (pairData A B)

theorem exponential_input (f : PR 2) (x : PTm n) (hx : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] GaussianRadiusExponentialName.input f (U f x) x :=
  .andI hx (all_samples_bounded f x hx)

theorem exponential_regular (f : PR 2) (x : PTm n) (hx : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] pointCN (E f) (exponentialData f x) :=
  GaussianRadiusExponentialName.name_regular _ _ _ (exponential_input f x hx)

private theorem exp_add (f g : PR 2) (x y : PTm n)
    (hx : Γ ⊢[PRAAx] pointCN f x) (hy : Γ ⊢[PRAAx] pointCN g y) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF (E f) (E g)) (E (addF f g))
      (multiplyData (E f) (E g) (exponentialData f x) (exponentialData g y))
      (exponentialData (addF f g) (addData x y)) := by
  let R := U f x+U g y
  have hxI := exponential_input f x hx
  have hyI := exponential_input g y hy
  have hR : Γ ⊢[PRAAx] le one R := le_trans (U_positive f x) (le_add_right _ _)
  have widerX := GaussianExponentialRadiusIndependence.input_widen f (U f x) R x hxI (le_add_right _ _)
  have widerY := GaussianExponentialRadiusIndependence.input_widen g (U g y) R y hyI (le_add_left _ _)
  have rx := exponential_regular f x hx
  have ry := exponential_regular g y hy
  have rx' := GaussianRadiusExponentialName.name_regular _ _ _ widerX
  have ry' := GaussianRadiusExponentialName.name_regular _ _ _ widerY
  have adjust := multiply_cross (E f) (E f) (E g) (E g)
    (exponentialData f x) (Ed R x) (exponentialData g y) (Ed R y) rx rx' ry ry'
    (GaussianExponentialRadiusIndependence.same_input_cross f _ _ _ hxI widerX)
    (GaussianExponentialRadiusIndependence.same_input_cross g _ _ _ hyI widerY)
  have combined := GaussianExponentialAddition.exponential_add_cross f g R x y hR widerX widerY
  have narrow := GaussianExponentialRadiusIndependence.same_input_cross (addF f g)
    (R+R) (U (addF f g) (addData x y)) (addData x y)
    (GaussianExponentialReference.add_input f g R x y widerX widerY)
    (exponential_input _ _ (add_fast f g x y hx hy))
  exact cross_trans _ _ _ _ _ _ adjust (cross_trans _ _ _ _ _ _ combined narrow)

theorem logarithm_regular (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] pointCN L (specialLogData A B) :=
  GaussianLogGammaEulerCofinal.canonical_regular A zero B zero (logarithm_source A B hA hB)

theorem gamma_power_regular (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] pointCN gammaPowerF (gammaPowerData A B) :=
  exponential_regular L _ (logarithm_regular A B hA hB)

theorem step_power_regular (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] pointCN stepPowerF (stepPowerData A B) :=
  exponential_regular stepExponentF _ (step_exponent_regular A B hA hB)

theorem numerator_step (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] crossEquivalent powerF shiftedPowerF (powerData (A+B) B) (shiftedPowerData A B) := by
  let d := exponentData A B
  let l := specialLogData A B
  let t := stepExponentData A B
  let s := incrementData A B
  have hd := exponent_regular A B hA hB
  have hl := logarithm_regular A B hA hB
  have ht := step_exponent_regular A B hA hB
  have hs := add_fast L stepExponentF l t hl ht
  have htotal := add_fast exponentF incrementF d s hd hs
  have later := exponent_regular (A+B) B (le_trans hA (le_add_right _ _)) hB
  have mapped := GaussianExponentialRadiusIndependence.independent_radii_proper exponentF totalF _ _ _ _
    (exponential_input _ _ later) (exponential_input _ _ htotal) (exponent_step A B hA hB)
  have outer := exp_add exponentF incrementF d s hd hs
  have inner := exp_add L stepExponentF l t hl ht
  have hp := power_regular A B hA hB
  have pair := multiply_fast gammaPowerF stepPowerF (gammaPowerData A B) (stepPowerData A B)
    (gamma_power_regular A B hA hB) (step_power_regular A B hA hB)
  have expanded := multiply_cross powerF powerF (E incrementF) pairF
    (powerData A B) (powerData A B) (exponentialData incrementF s) (pairData A B)
    hp hp (exponential_regular incrementF s hs) pair (cross_refl _ _ hp) (cross_symm _ _ _ _ inner)
  exact cross_trans _ _ _ _ _ _ mapped
    (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ outer) expanded)

theorem actual_Barnes_hyperfactorial_numerator_step_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (let A := var 0; let B := var 1
     le one A ⟶ le one B ⟶ crossEquivalent powerF shiftedPowerF (powerData (A+B) B) (shiftedPowerData A B)) :=
  closeUniv 2 (.impI (.impI (numerator_step _ _ Prf.hyp0.wk Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHyperfactorialPowerStep
