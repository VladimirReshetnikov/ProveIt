import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaDigammaPositiveStationary
import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaPositiveNamedDigammaInjective
import IPRADerivations.Analysis.Gamma.Digamma.GaussianNamedPositiveDigammaProperness
import IPRADerivations.Analysis.Gamma.GaussianGammaRationalWendelBoundary

/-!
# Critical points of the original Gamma on the positive half-line

The actual first Euler derivative vanishes exactly at the selected
positive location. The comparison uses the positive digamma inverse
slope and applies to every certified positive real name, with an
independently chosen positivity margin.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

namespace LeanProofs.IPRA.Analysis.GaussianGammaPositiveNamedCritical

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaDigammaDyadicLocation (locationF)
open GaussianGammaDigammaLocationInput (named_real_source)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (zeroF)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedPositiveDigamma (source derivativeF derivativeData nameF data digamma_zero_of_derivative_zero)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem selected_derivative_zero (y : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent (derivativeF locationF) zeroF (derivativeData y one) zero :=
  cross_trans (derivativeF locationF) zeroF zeroF (derivativeData y one) y zero
    (GaussianGammaDigammaPositiveStationary.original_integral_zero y)
    (GaussianGammaRationalWendelBoundary.zero_data_cross y zero)

theorem selected_digamma_zero (y : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent (nameF locationF) zeroF (data locationF y one) zero :=
  digamma_zero_of_derivative_zero locationF y one (named_real_source y) (selected_derivative_zero y)

theorem selected_of_derivative_zero (f : PR 2) (x y A : PTm n) (hf : Γ ⊢[PRAAx] source f x A)
    (hz : Γ ⊢[PRAAx] crossEquivalent (derivativeF f) zeroF (derivativeData x A) zero) :
    Γ ⊢[PRAAx] crossEquivalent f locationF x y := by
  have h := digamma_zero_of_derivative_zero f x A hf hz
  exact GaussianGammaPositiveNamedDigammaInjective.injective f locationF x y A one hf (named_real_source y)
    (cross_trans (nameF f) zeroF (nameF locationF) (data f x A) zero (data locationF y one)
      h (cross_symm _ _ _ _ (selected_digamma_zero y)))

theorem derivative_zero_of_selected (f : PR 2) (x y A : PTm n) (hf : Γ ⊢[PRAAx] source f x A)
    (he : Γ ⊢[PRAAx] crossEquivalent f locationF x y) :
    Γ ⊢[PRAAx] crossEquivalent (derivativeF f) zeroF (derivativeData x A) zero :=
  cross_trans (derivativeF f) (derivativeF locationF) zeroF (derivativeData x A) (derivativeData y one) zero
    (GaussianNamedPositiveDigammaProperness.derivative_proper f locationF x y A one hf (named_real_source y) he)
    (selected_derivative_zero y)

theorem stationary_quotient_rate (f K : PR 2) (p x z A a y : PTm n)
    (hf : Γ ⊢[PRAAx] source f x A)
    (hk : Γ ⊢[PRAAx] GaussianNamedGammaEulerFirstDerivative.source f K p x z A a)
    (he : Γ ⊢[PRAAx] crossEquivalent f locationF x y) :
    Γ ⊢[PRAAx] independentRate (GaussianNamedGammaEulerFirstDerivative.quotientF f K) zeroF
      (GaussianNamedGammaEulerFirstDerivative.quotientData f K x z A a) zero one (unit p) := by
  let Q := GaussianNamedGammaEulerFirstDerivative.quotientF f K
  let q := GaussianNamedGammaEulerFirstDerivative.quotientData f K x z A a
  have qr := GaussianNamedGammaEulerFirstDerivative.quotient_regular f K p x z A a hk
  have h := GaussianNamedGammaEulerFirstDerivative.original_first_derivative_rate f K p x z A a hk
  exact GaussianNamedRateTransport.transport Q (derivativeF f) Q zeroF q (derivativeData x A) q zero one (unit p)
    (unit_positive p) h (cross_refl _ _ qr)
    (cross_symm _ _ _ _ (derivative_zero_of_selected f x y A hf he))

theorem actual_positive_named_Gamma_stationary_exactly_selected_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (source f (var 0) (var 2) ⟶
        ((crossEquivalent (derivativeF f) zeroF (derivativeData (var 0) (var 2)) zero ⟶
          crossEquivalent f locationF (var 0) (var 1)) ⋏
         (crossEquivalent f locationF (var 0) (var 1) ⟶
          crossEquivalent (derivativeF f) zeroF (derivativeData (var 0) (var 2)) zero))) :=
  closeUniv 3 (.impI (.andI
    (.impI (selected_of_derivative_zero f _ _ _ Prf.hyp1 Prf.hyp0))
    (.impI (derivative_zero_of_selected f _ _ _ Prf.hyp1 Prf.hyp0))))

theorem actual_positive_named_Gamma_stationary_quotient_closed (f K : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      ((source f (var 1) (var 3) ⋏ GaussianNamedGammaEulerFirstDerivative.source f K (var 0) (var 1) (var 2) (var 3) (var 4)) ⟶
        crossEquivalent f locationF (var 1) (var 5) ⟶
        independentRate (GaussianNamedGammaEulerFirstDerivative.quotientF f K) zeroF
          (GaussianNamedGammaEulerFirstDerivative.quotientData f K (var 1) (var 2) (var 3) (var 4)) zero one (unit (var 0))) :=
  closeUniv 6 (.impI (.impI (stationary_quotient_rate f K _ _ _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaPositiveNamedCritical
