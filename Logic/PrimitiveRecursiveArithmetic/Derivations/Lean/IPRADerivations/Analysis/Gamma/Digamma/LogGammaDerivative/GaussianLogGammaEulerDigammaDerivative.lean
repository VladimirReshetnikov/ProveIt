import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.Derivatives.GaussianLogGammaEulerDerivativeQuotient
import IPRADerivations.Analysis.Gamma.Digamma.LogGammaDerivative.Fractions.GaussianLogGammaEulerDigammaFractionsCofinal

/-!
# The digamma series as the derivative of cofinal log-Gamma

For two signed rational arguments in the right half-plane, the actual
punctured log-Gamma difference quotient tends to the regular name for
`-γ - 1/z + ∑ (1/k - 1/(z+k))`, with the same error and the same two
independently chosen observation precisions as the Euler quotient estimate.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerDigammaDerivative

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianLogGammaEulerDerivativeQuotient (errorNumerator uniformSource)
open GaussianLogGammaEulerStepReciprocal (certified_step numerator radius)
open GaussianNameEquivalence (cross_refl cross_symm)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator rate_at)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "quotientF" => GaussianLogGammaEulerDerivativeQuotient.nameF
local notation "quotientData" => GaussianLogGammaEulerDerivativeQuotient.data
local notation "slopeF" => GaussianLogGammaEulerReciprocalSlopeCofinal.nameF
local notation "slopeData" => GaussianLogGammaEulerReciprocalSlopeCofinal.canonicalData
local notation "digammaF" => GaussianLogGammaEulerDigammaFractionsCofinal.nameF
local notation "digammaData" => GaussianLogGammaEulerDigammaFractionsCofinal.data

private theorem to_digamma (A B neg a b sign D K C E N : PTm n)
    (h : Γ ⊢[PRAAx] uniformSource A B neg a b sign D K C)
    (hN : Γ ⊢[PRAAx] le one N)
    (hrate : Γ ⊢[PRAAx] independentRate quotientF slopeF
      (quotientData A B neg a b sign D) (slopeData A B D neg) E N) :
    Γ ⊢[PRAAx] independentRate quotientF digammaF
      (quotientData A B neg a b sign D) (digammaData A B D neg) E N := by
  have hbase := h.andE₁.andE₁
  have hend := h.andE₁.andE₂.andE₁
  have hstep := certified_step A B neg a b sign D hbase.andE₂ h.andE₂
  have hquot := GaussianLogGammaEulerDerivativeQuotient.regular A B neg a b sign D hbase hend hstep
  have hseries := GaussianLogGammaEulerDigammaFractionsCofinal.cofinal_equivalent A B D neg hbase
  exact GaussianNamedRateTransport.transport quotientF slopeF quotientF digammaF
    _ _ _ _ E N hN hrate (cross_refl _ _ hquot) (cross_symm _ _ _ _ hseries)

theorem uniform_rate (A B neg a b sign D K C : PTm n)
    (h : Γ ⊢[PRAAx] uniformSource A B neg a b sign D K C) :
    Γ ⊢[PRAAx] independentRate quotientF digammaF
      (quotientData A B neg a b sign D) (digammaData A B D neg)
      (errorNumerator (radius (numerator A B neg a b sign)) K) D :=
  to_digamma A B neg a b sign D K C _ D h h.andE₁.andE₁.andE₂
    (GaussianLogGammaEulerDerivativeQuotient.uniform_rate A B neg a b sign D K C h)

theorem modulus_rate (r A B neg a b sign D K C : PTm n)
    (h : Γ ⊢[PRAAx] uniformSource A B neg a b sign D K C)
    (hsmall : Γ ⊢[PRAAx] le (errorNumerator (radius (numerator A B neg a b sign)) K * unit r) D) :
    Γ ⊢[PRAAx] independentRate quotientF digammaF
      (quotientData A B neg a b sign D) (digammaData A B D neg) one (unit r) :=
  to_digamma A B neg a b sign D K C one (unit r) h (unit_positive r)
    (GaussianLogGammaEulerDerivativeQuotient.modulus_rate r A B neg a b sign D K C h hsmall)

theorem observations (p q A B neg a b sign D K C : PTm n)
    (h : Γ ⊢[PRAAx] uniformSource A B neg a b sign D K C) :
    Γ ⊢[PRAAx] distanceBounded (ap2 quotientF p (quotientData A B neg a b sign D))
      (ap2 digammaF q (digammaData A B D neg))
      (rateNumerator (errorNumerator (radius (numerator A B neg a b sign)) K) D p q)
      (rateDenominator D p q) :=
  rate_at quotientF digammaF _ _ _ _ p q (uniform_rate A B neg a b sign D K C h)

theorem actual_log_Gamma_digamma_derivative_rate_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
      (uniformSource (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
        independentRate quotientF digammaF
          (quotientData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
          (digammaData (var 0) (var 1) (var 6) (var 2))
          (errorNumerator (radius (numerator (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))) (var 7))
          (var 6)) :=
  closeUniv 9 (.impI (uniform_rate _ _ _ _ _ _ _ _ _ Prf.hyp0))

theorem actual_log_Gamma_digamma_derivative_modulus_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
      (uniformSource (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
        le (errorNumerator (radius (numerator (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))) (var 7) *
          unit (var 9)) (var 6) ⟶
        independentRate quotientF digammaF
          (quotientData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
          (digammaData (var 0) (var 1) (var 6) (var 2)) one (unit (var 9))) :=
  closeUniv 10 (.impI (.impI (modulus_rate _ _ _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerDigammaDerivative
