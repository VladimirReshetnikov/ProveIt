import IPRADerivations.Analysis.Gamma.CriticalPoints.PositiveMinimum.GaussianGammaMinimumFreezeRational
import IPRADerivations.Analysis.Euler.Logarithms.Exhaustion.GaussianNamedEulerLogarithmicFrozenRate
import IPRADerivations.Analysis.Euler.Logarithms.GaussianEulerLogarithmicImproperInputProperness

/-!
# Freeze the original positive named Gamma and its Euler integrals

One demand clock suffices for the original Gamma and logarithmic
Euler programs. Their frozen values use the exact real sample of
the same input, with independent output clocks.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaPositiveNamedRationalFreeze

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaMinimumFreezeRational (numerator denominator fraction_at frozen_rational_domain frozen_gamma_cross)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm)
open GaussianNamedGammaPositiveLower (source)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedRightHalfPlane (threshold radius actual_late_source)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (ofGaussian ofGaussian_canonical)
open GaussianStirlingGammaLogarithm (arg gammaData euler_real_source)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "G" => GaussianNamedGamma.nameF
local notation "gd" => GaussianNamedGamma.data
local notation "E" => GaussianNamedEulerLogarithmicImproper.nameF
local notation "ed" => GaussianNamedEulerLogarithmicImproper.data
local notation "I" => GaussianEulerLogarithmicImproperName.nameF
local notation "ir" => GaussianEulerLogarithmicImproperName.data

def clock (f : PR 2) (s j x A : PTm n) : PTm n :=
  GaussianNamedGammaPositiveLower.clock f s x A+
    succ (GaussianEulerLogarithmicContinuity.modulus s j (radius f x) (two*A))

def eulerData (f : PR 2) (j k x : PTm n) : PTm n :=
  ir j (arg (numerator f k x)) (numerator f k x) (denominator f k x) (denominator f k x)

ipra_subst clock [two, one]

ipra_subst eulerData

theorem threshold_le (f : PR 2) (s j x A : PTm n) : Γ ⊢[PRAAx] le (threshold A) (clock f s j x A) :=
  le_trans (le_add_right _ _) (le_add_right _ _)

theorem gamma_rate (f : PR 2) (s j k x A : PTm n) (h : Γ ⊢[PRAAx] source f x A)
    (hk : Γ ⊢[PRAAx] le (clock f s j x A) k) :
    Γ ⊢[PRAAx] independentRate (G f) gammaF (gd x A) (gammaData (numerator f k x) (denominator f k x)) one (unit s) := by
  let u := GaussianNamedGammaLateInput.encodedData f k x A
  have hl : Γ ⊢[PRAAx] le (GaussianNamedGammaPositiveLower.clock f s x A) k := le_trans (le_add_right _ _) hk
  have hin : Γ ⊢[PRAAx] GaussianNamedGammaLateInput.input f s k x A :=
    .andI h.andE₁ (.andI (le_trans (le_add_right _ _) hl) (le_trans (le_add_left _ _) hl))
  have he := frozen_gamma_cross f s k x A h hin
  exact GaussianNamedRateTransport.transport (G f) gammaF (G f) gammaF (gd x A) u (gd x A)
    (gammaData (numerator f k x) (denominator f k x)) one (unit s) (unit_positive s)
    (GaussianNamedGammaLateInput.original_independent_rate f s k x A hin)
    (cross_refl _ _ (GaussianNamedGamma.name_regular f x A h.andE₁))
    (cross_symm _ _ _ _ he)

theorem euler_cross (f : PR 2) (j k x A : PTm n) (h : Γ ⊢[PRAAx] source f x A)
    (hk : Γ ⊢[PRAAx] le (threshold A) k) :
    Γ ⊢[PRAAx] crossEquivalent I I (GaussianNamedEulerLogarithmicFrozenRate.frozenData f j x A k) (eulerData f j k x) := by
  let a := numerator f k x
  let b := denominator f k x
  let z := GaussianNamedRightHalfPlane.numerator f k x
  let B := GaussianNamedRightHalfPlane.denominator f k x
  have H := frozen_rational_domain f k x A h hk
  have decoded := fraction_at f k x A h hk
  have left := actual_late_source f x A k h.andE₁ hk
  have right := euler_real_source a b H.andE₁
  have r : Γ ⊢[PRAAx] ofGaussian z B ≐ fraction a b :=
    (GaussianNameArithmetic.recode_congr decoded).eqTrans
      (GaussianExponentialReference.recode_fixed _ (ofGaussian_canonical _ _ H.andE₁.andE₂))
  exact GaussianEulerLogarithmicImproperInputProperness.original_improper_proper j z (arg a)
    (radius f x) a B b (two*A) b (.andI left (.andI right.andE₁ r))

theorem euler_rate (f : PR 2) (s j k x A : PTm n) (h : Γ ⊢[PRAAx] source f x A)
    (hk : Γ ⊢[PRAAx] le (clock f s j x A) k) :
    Γ ⊢[PRAAx] independentRate (E f) I (ed j x A) (eulerData f j k x) (num 5) (unit s) := by
  have hm := le_trans (threshold_le (Γ := Γ) f s j x A) hk
  have hi : Γ ⊢[PRAAx] GaussianNamedEulerLogarithmicFrozenRate.source f s j x A k :=
    .andI h.andE₁ (.andI hm (le_trans (le_add_left _ _) hk))
  exact GaussianNamedRateTransport.transport (E f) I (E f) I (ed j x A) _ (ed j x A)
    (eulerData f j k x) (num 5) (unit s) (unit_positive s)
    (GaussianNamedEulerLogarithmicFrozenRate.frozen_rate f s j x A k hi)
    (cross_refl _ _ (GaussianNamedEulerLogarithmicImproper.name_regular f j x A h.andE₁))
    (cross_symm _ _ _ _ (euler_cross f j k x A h hm))

theorem actual_original_positive_gamma_and_euler_rational_freeze_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      ((source f (var 0) (var 1) ⋏ le (clock f (var 2) (var 3) (var 0) (var 1)) (var 4)) ⟶
        (independentRate (G f) gammaF (gd (var 0) (var 1))
          (gammaData (numerator f (var 4) (var 0)) (denominator f (var 4) (var 0))) one (unit (var 2)) ⋏
         independentRate (E f) I (ed (var 3) (var 0) (var 1)) (eulerData f (var 3) (var 4) (var 0))
          (num 5) (unit (var 2)))) :=
  closeUniv 5 (.impI (.andI (gamma_rate f _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂)
    (euler_rate f _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianGammaPositiveNamedRationalFreeze
