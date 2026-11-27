import IPRADerivations.Analysis.Barnes.FunctionalEquations.Hyperfactorial.Named.GaussianBarnesCanonicalNamedHyperfactorialExponentStep
import IPRADerivations.Analysis.Barnes.FunctionalEquations.Hyperfactorial.Recurrence.GaussianBarnesCanonicalHyperfactorialPowerStep
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.Exponentiation.GaussianLogGammaEulerNamedExponential

/-! # The unit step of the original named hyperfactorial numerator -/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNamedHyperfactorialPowerStep

open_ipra
open GaussianBarnesCanonicalNamedHyperfactorial
  (exponentF exponentData exponent_regular powerF powerData powerRadius power_input power_regular)
open GaussianBarnesCanonicalNamedHyperfactorialExponentStep
  (stepExponentF stepExponentData step_exponent_regular incrementF incrementData totalF totalData exponent_step)
open GaussianBarnesCanonicalHyperfactorialPowerStep (exponentialData exponential_input exponential_regular)
open GaussianLogGammaEulerNamed (source)
open GaussianEulerNamedShiftInput (shiftF shiftData)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameBounds (U)
open GaussianGammaAdjacentCutoff (multiply_cross)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "E" => GaussianRadiusExponentialName.nameF
local notation "Ed" => GaussianRadiusExponentialName.data
local notation "L" => GaussianLogGammaEulerNamed.nameF
local notation "Ld" => GaussianLogGammaEulerNamed.data

abbrev gammaPowerF (f : PR 2) : PR 2 := GaussianLogGammaEulerNamedExponential.nameF f
abbrev gammaPowerData (f : PR 2) (x M R : PTm n) : PTm n := GaussianLogGammaEulerNamedExponential.data f x M R
abbrev stepPowerF (f : PR 2) : PR 2 := E (stepExponentF f)
def stepPowerData (f : PR 2) (x M R : PTm n) : PTm n := exponentialData (stepExponentF f) (stepExponentData f x M R)
abbrev pairF (f : PR 2) : PR 2 := multiplyF (gammaPowerF f) (stepPowerF f)
def pairData (f : PR 2) (x M R : PTm n) : PTm n :=
  multiplyData (gammaPowerF f) (stepPowerF f) (gammaPowerData f x M R) (stepPowerData f x M R)
abbrev shiftedPowerF (f : PR 2) : PR 2 := multiplyF (powerF f) (pairF f)
def shiftedPowerData (f : PR 2) (x M R : PTm n) : PTm n :=
  multiplyData (powerF f) (pairF f) (powerData f x M R) (pairData f x M R)

private theorem exp_add (f g : PR 2) (r s t x y : PTm n)
    (hx : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input f r x)
    (hy : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input g s y)
    (ha : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input (addF f g) t (addData x y)) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF (E f) (E g)) (E (addF f g))
      (multiplyData (E f) (E g) (Ed r x) (Ed s y)) (Ed t (addData x y)) := by
  let R := succ (r+s)
  have left := le_trans (le_add_right (Γ := Γ) r s) (le_succ_self (r+s))
  have right := le_trans (le_add_left (Γ := Γ) s r) (le_succ_self (r+s))
  have hR : Γ ⊢[PRAAx] le one R := LeanProofs.IPRA.Common.one_le_succ (r+s)
  have wx := GaussianExponentialRadiusIndependence.input_widen f r R x hx left
  have wy := GaussianExponentialRadiusIndependence.input_widen g s R y hy right
  have adjust := multiply_cross (E f) (E f) (E g) (E g) (Ed r x) (Ed R x) (Ed s y) (Ed R y)
    (GaussianRadiusExponentialName.name_regular f r x hx) (GaussianRadiusExponentialName.name_regular f R x wx)
    (GaussianRadiusExponentialName.name_regular g s y hy) (GaussianRadiusExponentialName.name_regular g R y wy)
    (GaussianExponentialRadiusIndependence.same_input_cross f r R x hx wx)
    (GaussianExponentialRadiusIndependence.same_input_cross g s R y hy wy)
  have combined := GaussianExponentialAddition.exponential_add_cross f g R x y hR wx wy
  have last := GaussianExponentialRadiusIndependence.same_input_cross (addF f g) (R+R) t (addData x y)
    (GaussianExponentialReference.add_input f g R x y wx wy) ha
  exact cross_trans _ _ _ _ _ _ adjust (cross_trans _ _ _ _ _ _ combined last)

theorem step_power_regular (f : PR 2) (x M R : PTm n) (h : Γ ⊢[PRAAx] source f x M R) :
    Γ ⊢[PRAAx] pointCN (stepPowerF f) (stepPowerData f x M R) :=
  exponential_regular _ _ (step_exponent_regular f x M R h)

theorem numerator_step (f : PR 2) (x M R S : PTm n) (h : Γ ⊢[PRAAx] source f x M R)
    (hS : Γ ⊢[PRAAx] le (GaussianNamedRightHalfPlane.radius (shiftF f) (shiftData x)) S) :
    Γ ⊢[PRAAx] crossEquivalent (powerF (shiftF f)) (shiftedPowerF f) (powerData (shiftF f) (shiftData x) M S)
      (shiftedPowerData f x M R) := by
  let g := shiftF f
  let y := shiftData x
  let d := exponentData f x M R
  let l := Ld x M R
  let t := stepExponentData f x M R
  let s := incrementData f x M R
  let w := totalData f x M R
  have hd := exponent_regular f x M R h
  have hl := GaussianLogGammaEulerNamed.name_regular f x M R h
  have ht := step_exponent_regular f x M R h
  have hi := add_fast (L f) (stepExponentF f) l t hl ht
  have hw := add_fast (exponentF f) (incrementF f) d s hd hi
  have next := GaussianLogGammaEulerShiftedChart.shift_source f x M R S h hS
  have mapped := GaussianExponentialRadiusIndependence.independent_radii_proper (exponentF g) (totalF f)
    (powerRadius g y M S) (U (totalF f) w) (exponentData g y M S) w
    (power_input g y M S next) (exponential_input _ _ hw) (exponent_step f x M R S h hS)
  have outer := exp_add (exponentF f) (incrementF f) (powerRadius f x M R) (U (incrementF f) s) (U (totalF f) w)
    d s (power_input f x M R h) (exponential_input _ _ hi) (exponential_input _ _ hw)
  have inner := exp_add (L f) (stepExponentF f) (GaussianNamedRadiusExponentialFreeze.radius (L f) l)
    (U (stepExponentF f) t) (U (incrementF f) s) l t
    (GaussianNamedRadiusExponentialFreeze.original_input _ _ hl) (exponential_input _ _ ht)
    (exponential_input _ _ hi)
  have hp := power_regular f x M R h
  have pair := multiply_fast (gammaPowerF f) (stepPowerF f) (gammaPowerData f x M R) (stepPowerData f x M R)
    (GaussianLogGammaEulerNamedExponential.name_regular f x M R h) (step_power_regular f x M R h)
  have expanded := multiply_cross (powerF f) (powerF f) (E (incrementF f)) (pairF f)
    (powerData f x M R) (powerData f x M R) (exponentialData (incrementF f) s) (pairData f x M R)
    hp hp (exponential_regular _ _ hi) pair (cross_refl _ _ hp) (cross_symm _ _ _ _ inner)
  exact cross_trans _ _ _ _ _ _ mapped (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ outer) expanded)

theorem actual_original_named_Barnes_hyperfactorial_numerator_step_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (let x := var 0; let M := var 1; let R := var 2; let S := var 3
       source f x M R ⟶ le (GaussianNamedRightHalfPlane.radius (shiftF f) (shiftData x)) S ⟶
        crossEquivalent (powerF (shiftF f)) (shiftedPowerF f) (powerData (shiftF f) (shiftData x) M S)
          (shiftedPowerData f x M R)) :=
  closeUniv 4 (.impI (.impI (numerator_step f _ _ _ _ Prf.hyp0.wk Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNamedHyperfactorialPowerStep
