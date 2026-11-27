import IPRADerivations.Analysis.Barnes.FunctionalEquations.Hyperfactorial.Named.GaussianBarnesCanonicalNamedHyperfactorialBarnesStep
import IPRADerivations.Analysis.Barnes.FunctionalEquations.Hyperfactorial.Recurrence.GaussianBarnesCanonicalHyperfactorialRecurrence

/-!
# The original named hyperfactorial unit recurrence on certified charts

At both inputs the Barnes value has a certified reciprocal. The two
pole-free Gamma chart certificates identify the multiplier in the
Barnes recurrence with the actual exponential of the original named
Euler logarithm of Gamma. Cancelling the shifted Barnes value gives
`H(z+1)=H(z)exp(z Log z)` for the actual named hyperfactorial.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNamedHyperfactorialRecurrence

open_ipra
open GaussianBarnesCanonicalNamedHyperfactorial
  (source nameF data regular cleared_relation powerF powerData power_regular barnes_regular)
open GaussianBarnesCanonicalNamedHyperfactorialPowerStep
  (stepPowerF stepPowerData step_power_regular gammaPowerF gammaPowerData pairF pairData numerator_step)
open GaussianBarnesCanonicalNamedHyperfactorialBarnesStep (gammaSource denominatorF denominatorData denominator_step)
open GaussianBarnesCanonicalOrdinaryUpperGrowth (valueData)
open GaussianEulerNamedShiftInput (shiftF shiftData)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianBarnesCanonicalHyperfactorialRecurrence (regroup cancel_right)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "M" => multiplyF
local notation "Md" => multiplyData
local notation "G" => GaussianBarnesCanonicalOrdinaryUpperGrowth.nameF

def stepF (f : PR 2) : PR 2 := M (nameF f) (stepPowerF f)
def stepData (f : PR 2) (x m R h : PTm n) : PTm n :=
  Md (nameF f) (stepPowerF f) (data f x m R h) (stepPowerData f x m R)

theorem recurrence (f : PR 2) (x m R S h k E : PTm n) (hf : Γ ⊢[PRAAx] source f x m R h)
    (hs : Γ ⊢[PRAAx] source (shiftF f) (shiftData x) m S k)
    (hg : Γ ⊢[PRAAx] gammaSource f x R E) :
    Γ ⊢[PRAAx] crossEquivalent (nameF (shiftF f)) (stepF f) (data (shiftF f) (shiftData x) m S k)
      (stepData f x m R h) := by
  let sf := shiftF f
  let sx := shiftData x
  let a := data f x m R h
  let b := stepPowerData f x m R
  let c := valueData x R
  let d := gammaPowerData f x m R
  let e := stepData f x m R h
  let u := valueData sx S
  have ha := regular f x m R h hf
  have hb := step_power_regular f x m R hf.andE₁
  have hc := barnes_regular f x m R hf.andE₁
  have hd := GaussianLogGammaEulerNamedExponential.name_regular f x m R hf.andE₁
  have he := multiply_fast (nameF f) (stepPowerF f) a b ha hb
  have hu := barnes_regular sf sx m S hs.andE₁
  have hp := multiply_fast (gammaPowerF f) (stepPowerF f) d b hd hb
  have start := multiply_cross (stepF f) (stepF f) (G sf) (denominatorF f)
    e e u (denominatorData f x m R) he he hu
    (multiply_fast (G f) (gammaPowerF f) c d hc hd) (cross_refl _ _ he)
    (denominator_step f x m R S E hf.andE₁ hs.andE₁ hg)
  have reorder := regroup (nameF f) (stepPowerF f) (G f) (gammaPowerF f) a b c d ha hb hc hd
  have toNumerator := multiply_cross (M (nameF f) (G f)) (powerF f) (pairF f) (pairF f)
    (Md (nameF f) (G f) a c) (powerData f x m R) (pairData f x m R) (pairData f x m R)
    (multiply_fast _ _ _ _ ha hc) (power_regular f x m R hf.andE₁) hp hp
    (cleared_relation f x m R h hf) (cross_refl _ _ hp)
  have right := cross_trans _ _ _ _ _ _ start
    (cross_trans _ _ _ _ _ _ reorder
      (cross_trans _ _ _ _ _ _ toNumerator (cross_symm _ _ _ _ (numerator_step f x m R S hf.andE₁ hs.andE₁.andE₂))))
  have left := cleared_relation sf sx m S k hs
  exact cancel_right (nameF sf) (stepF f) (G sf) (data sf sx m S k) e u k
    (regular sf sx m S k hs) he hu hs.andE₂
    (cross_trans _ _ _ _ _ _ left (cross_symm _ _ _ _ right))

theorem actual_original_named_Barnes_hyperfactorial_unit_recurrence_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      (let x := var 0; let m := var 1; let R := var 2; let S := var 3
       let h := var 4; let k := var 5; let E := var 6
       source f x m R h ⟶ source (shiftF f) (shiftData x) m S k ⟶ gammaSource f x R E ⟶
         crossEquivalent (nameF (shiftF f)) (stepF f) (data (shiftF f) (shiftData x) m S k) (stepData f x m R h)) :=
  closeUniv 7 (.impI (.impI (.impI (recurrence f _ _ _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp0.wk Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNamedHyperfactorialRecurrence
