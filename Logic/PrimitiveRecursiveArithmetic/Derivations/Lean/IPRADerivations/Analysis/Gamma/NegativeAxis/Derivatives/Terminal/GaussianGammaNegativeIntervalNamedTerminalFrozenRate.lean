import IPRADerivations.Analysis.Gamma.NegativeAxis.Derivatives.Terminal.GaussianGammaNegativeIntervalNamedTerminalDerivative
import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaDigammaNative
import IPRADerivations.Analysis.Euler.Logarithms.Exhaustion.GaussianNamedEulerLogarithmicFrozenRate
import IPRADerivations.Analysis.Euler.Logarithms.GaussianEulerLogarithmicImproperInputProperness

/-!
# Native rational readback for the terminal Gamma derivative

The order-one Euler integral at a shifted real offset can be compared with
the original native positive rational derivative at that offset's actual
finite observation. The frozen numerator and denominator use the same
shifted-input clock as the terminal Gamma value.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedTerminalFrozenRate

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaNegativeIntervalNamedTerminalDerivative
  (terminalF terminalData terminal_rational_at terminal_source derivativeF derivativeData)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm)
open GaussianNamedInverseRate (independentRate)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (ofGaussian ofGaussian_canonical)
open GaussianUnitIntervalInputDecoding (numerator denominator denominator_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "IF" => GaussianEulerLogarithmicImproperName.nameF
local notation "offsetSource" => GaussianNamedEulerUnitTime.source

def terminalNumerator (f : PR 2) (k x : PTm n) : PTm n :=
  let q := ap2 f (GaussianEulerNamedShiftInput.clock k) x
  denominator q+numerator q

def terminalDenominator (f : PR 2) (k x : PTm n) : PTm n :=
  denominator (ap2 f (GaussianEulerNamedShiftInput.clock k) x)

def nativeData (f : PR 2) (k x : PTm n) : PTm n :=
  GaussianGammaDigammaNative.derivativeData (terminalNumerator f k x) (terminalDenominator f k x)

def minimumClock (f : PR 2) (s x : PTm n) : PTm n :=
  GaussianNamedRightHalfPlane.threshold one+
    succ (GaussianEulerLogarithmicContinuity.modulus s one
      (GaussianNamedRightHalfPlane.radius (terminalF f) (terminalData x)) (two*one))

ipra_subst terminalNumerator

ipra_subst terminalDenominator

ipra_subst nativeData

ipra_subst minimumClock [one, two]

theorem native_source (f : PR 2) (k x : PTm n) :
    Γ ⊢[PRAAx] GaussianStirlingGammaLogarithm.source (terminalNumerator f k x) (terminalDenominator f k x) := by
  have hb := denominator_positive (Γ := Γ) (ap2 f (GaussianEulerNamedShiftInput.clock k) x)
  exact .andI (le_trans hb (le_add_right _ _)) hb

theorem native_readback (f : PR 2) (k x E : PTm n) (h : Γ ⊢[PRAAx] offsetSource f x E) :
    Γ ⊢[PRAAx] ofGaussian (GaussianNamedRightHalfPlane.numerator (terminalF f) k (terminalData x))
      (GaussianNamedRightHalfPlane.denominator (terminalF f) k (terminalData x)) ≐
      fraction (terminalNumerator f k x) (terminalDenominator f k x) := by
  have he := terminal_rational_at f k x E h
  have hf : Γ ⊢[PRAAx] GaussianRationalHorner.canonical
      (fraction (terminalNumerator f k x) (terminalDenominator f k x)) :=
    ofGaussian_canonical _ _ (native_source f k x).andE₂
  exact (GaussianNameArithmetic.recode_congr he).eqTrans
    (GaussianNamedSmallPerturbationTransport.recode_fixed _ hf)

theorem native_cross (f : PR 2) (k x E : PTm n) (h : Γ ⊢[PRAAx] offsetSource f x E)
    (hk : Γ ⊢[PRAAx] le (GaussianNamedRightHalfPlane.threshold one) k) :
    Γ ⊢[PRAAx] crossEquivalent IF IF
      (GaussianNamedEulerLogarithmicFrozenRate.frozenData (terminalF f) one (terminalData x) one k)
      (nativeData f k x) := by
  let a := terminalNumerator f k x
  let b := terminalDenominator f k x
  let t := terminalData x
  have hg := GaussianNamedRightHalfPlane.actual_late_source (terminalF f) t one k (terminal_source f x E h) hk
  have hn := GaussianStirlingGammaLogarithm.euler_real_source (Γ := Γ) a b (native_source f k x)
  exact GaussianEulerLogarithmicImproperInputProperness.original_improper_proper one
    (GaussianNamedRightHalfPlane.numerator (terminalF f) k t) (GaussianStirlingGammaLogarithm.arg a)
    (GaussianNamedRightHalfPlane.radius (terminalF f) t) a
    (GaussianNamedRightHalfPlane.denominator (terminalF f) k t) b (two*one) b
    (.andI hg (.andI hn.andE₁ (native_readback f k x E h)))

theorem original_rate (f : PR 2) (s k x E : PTm n) (h : Γ ⊢[PRAAx] offsetSource f x E)
    (hk : Γ ⊢[PRAAx] le (minimumClock f s x) k) :
    Γ ⊢[PRAAx] independentRate (derivativeF f) IF (derivativeData x) (nativeData f k x) (num 5) (unit s) := by
  let t := terminalData x
  let u := GaussianNamedEulerLogarithmicFrozenRate.frozenData (terminalF f) one t one k
  have margin : Γ ⊢[PRAAx] le (GaussianNamedRightHalfPlane.threshold one) k :=
    le_trans (le_add_right _ _) hk
  have demand : Γ ⊢[PRAAx] le (succ (GaussianEulerLogarithmicContinuity.modulus s one
      (GaussianNamedRightHalfPlane.radius (terminalF f) t) (two*one))) k :=
    le_trans (le_add_left _ _) hk
  have ht := terminal_source f x E h
  have frozen := GaussianNamedEulerLogarithmicFrozenRate.frozen_rate (terminalF f) s one t one k
    (.andI ht (.andI margin demand))
  have left : Γ ⊢[PRAAx] pointCN (derivativeF f) (derivativeData x) :=
    GaussianNamedEulerLogarithmicImproper.name_regular (terminalF f) one t one ht
  exact GaussianNamedRateTransport.transport (derivativeF f) IF (derivativeF f) IF
    (derivativeData x) u (derivativeData x) (nativeData f k x) (num 5) (unit s)
    (unit_positive s) frozen (cross_refl _ _ left)
    (cross_symm IF IF u (nativeData f k x) (native_cross f k x E h margin))

theorem actual_original_terminal_derivative_native_frozen_rate_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      ((offsetSource f (var 2) (var 3) ⋏ le (minimumClock f (var 0) (var 2)) (var 1)) ⟶
        independentRate (derivativeF f) IF (derivativeData (var 2)) (nativeData f (var 1) (var 2))
          (num 5) (unit (var 0))) :=
  closeUniv 4 (.impI (original_rate f _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedTerminalFrozenRate
