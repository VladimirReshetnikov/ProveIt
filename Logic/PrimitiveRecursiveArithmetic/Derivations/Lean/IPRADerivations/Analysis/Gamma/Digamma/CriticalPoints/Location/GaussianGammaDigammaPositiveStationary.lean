import IPRADerivations.Analysis.Gamma.Digamma.CriticalPoints.Location.GaussianGammaDigammaLocationProduct
import IPRADerivations.Analysis.Gamma.Digamma.CriticalPoints.Location.GaussianGammaDigammaLocationIntegral
import IPRADerivations.Analysis.Gamma.EulerProducts.Derivatives.GaussianNamedGammaEulerFirstDerivative

/-!
# Stationarity of the original Gamma program at the positive location

The native logarithmic integral residual is uniform along the selected
dyadic fractions. The actual first named Euler logarithmic integral at
the completed location is therefore zero. The original first derivative
comparison now bounds the actual Gamma difference quotients by the
independent clock allowances and the prescribed increment tolerance.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaPositiveStationary

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaDigammaDyadicLocation (locationF)
open GaussianGammaDigammaLocationIntegral (nativeResidual integral_zero)
open GaussianGammaDigammaLocationProduct (derivativeBudget subst_derivativeBudget native_derivative_residual_at)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm)
open GaussianNameRingLaws (zeroF)
open GaussianNamedGammaEulerFirstDerivative (source quotientF quotientData quotient_regular original_first_derivative_rate)
open GaussianNamedInverseRate (independentRate)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "LF" => GaussianNamedEulerLogarithmicImproper.nameF locationF
local notation "ld" x:max => GaussianNamedEulerLogarithmicImproper.data one x one

theorem native_residual : Γ ⊢[PRAAx] nativeResidual (derivativeBudget : PTm n) := by
  refine .allI ?_
  simpa only [Syn.shift,subst_derivativeBudget] using
    native_derivative_residual_at (Γ := Γ.map Fm.shift) (var 0)

theorem original_integral_zero (x : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent LF zeroF (ld x) x :=
  integral_zero x derivativeBudget native_residual

theorem original_difference_quotient_rate (K : PR 2) (p x y a : PTm n)
    (h : Γ ⊢[PRAAx] source locationF K p x y one a) :
    Γ ⊢[PRAAx] independentRate (quotientF locationF K) zeroF
      (quotientData locationF K x y one a) x one (unit p) := by
  let Q := quotientF locationF K
  let d := quotientData locationF K x y one a
  exact GaussianNamedRateTransport.transport Q LF Q zeroF d (ld x) d x one (unit p) (unit_positive p)
    (original_first_derivative_rate locationF K p x y one a h)
    (cross_refl Q d (quotient_regular locationF K p x y one a h))
    (cross_symm LF zeroF (ld x) x (original_integral_zero x))

theorem actual_positive_gamma_location_integral_zero_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
      (crossEquivalent LF zeroF (ld (var 0)) (var 0)) :=
  closeUniv 1 (original_integral_zero _)

theorem actual_positive_gamma_stationary_location_closed (K : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (source locationF K (var 0) (var 1) (var 2) one (var 3) ⟶
        independentRate (quotientF locationF K) zeroF
          (quotientData locationF K (var 1) (var 2) one (var 3)) (var 1) one (unit (var 0))) :=
  closeUniv 4 (.impI (original_difference_quotient_rate K _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaPositiveStationary
