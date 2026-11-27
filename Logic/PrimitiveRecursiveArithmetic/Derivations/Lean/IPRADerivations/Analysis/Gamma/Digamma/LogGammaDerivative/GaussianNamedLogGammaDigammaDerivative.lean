import IPRADerivations.Analysis.Gamma.Names.Derivatives.GaussianNamedLogGammaTaylorEstimate
import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.DerivativeRates.GaussianNamedTaylorDifferenceQuotient
import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedRateRadius

/-!
# The actual named log-Gamma quotient with a certified apartness witness

The denominator is the actual named displacement. A native apartness
witness bounds its reciprocal and gives the stated explicit rate from the
quadratic estimate to the original named digamma program.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedLogGammaDigammaDerivative

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianLogGammaEulerNamed (name_regular)
open GaussianNameReciprocal (R apart)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedLogGammaTaylorEstimate (input quadraticBudget)
open GaussianRationalHorner (positive_product)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "stepF" => GaussianNamedDifference.nameF
local notation "stepData" => GaussianNamedDifference.data
local notation "logF" => GaussianLogGammaEulerNamed.nameF
local notation "logData" => GaussianLogGammaEulerNamed.data
local notation "psiF" => GaussianLogGammaEulerNamedDigamma.nameF
local notation "psiData" => GaussianLogGammaEulerNamedDigamma.data

def nameF (f g : PR 2) : PR 2 :=
  GaussianNamedIncrementDifferenceQuotient.nameF (logF g) (logF f) (stepF g f)

def data (f g : PR 2) (x y M S a : PTm n) : PTm n :=
  GaussianNamedIncrementDifferenceQuotient.data (logF g) (logF f) (stepF g f)
    (logData y M S) (logData x M S) (stepData y x) a

def coefficient (a P M : PTm n) : PTm n := R a * quadraticBudget P (two*M)

theorem rate (f g : PR 2) (x y M S P Q a : PTm n)
    (h : Γ ⊢[PRAAx] input f g x y M S P Q)
    (ha : Γ ⊢[PRAAx] apart (stepF g f) a (stepData y x)) :
    Γ ⊢[PRAAx] independentRate (nameF f g) (psiF f) (data f g x y M S a) (psiData x M S)
      (coefficient a P M) (Q*Q) := by
  have hf := h.andE₁
  have hg := h.andE₂.andE₁
  have hQ := h.andE₂.andE₂.andE₁
  have hs := GaussianNamedDifference.name_regular g f y x hg.andE₁.andE₁ hf.andE₁.andE₁
  exact GaussianNamedTaylorDifferenceQuotient.quotient_rate (logF g) (logF f) (stepF g f) (psiF f)
    (logData y M S) (logData x M S) (stepData y x) (psiData x M S) a (quadraticBudget P (two*M)) (Q*Q)
    (.andI (.andI (name_regular g y M S hg) (.andI (name_regular f x M S hf) (.andI hs ha)))
      (.andI (GaussianLogGammaEulerNamedDigamma.name_regular f x M S hf)
        (.andI (positive_product Q Q hQ hQ) (GaussianNamedLogGammaTaylorEstimate.independent_rate f g x y M S P Q h))))

theorem modulus (f g : PR 2) (x y M S P Q a r : PTm n)
    (h : Γ ⊢[PRAAx] input f g x y M S P Q)
    (ha : Γ ⊢[PRAAx] apart (stepF g f) a (stepData y x))
    (small : Γ ⊢[PRAAx] le (coefficient a P M * unit r) (Q*Q)) :
    Γ ⊢[PRAAx] independentRate (nameF f g) (psiF f) (data f g x y M S a) (psiData x M S) one (unit r) :=
  GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _
    (positive_product Q Q h.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₁) (unit_positive r)
    (le_congr (.eqRefl _) (one_mul _).eqSymm small) (rate f g x y M S P Q a h ha)

theorem actual_named_log_Gamma_apart_difference_quotient_closed (f g : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      (input f g (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
        apart (stepF g f) (var 6) (stepData (var 1) (var 0)) ⟶
        independentRate (nameF f g) (psiF f) (data f g (var 0) (var 1) (var 2) (var 3) (var 6))
          (psiData (var 0) (var 2) (var 3)) (coefficient (var 6) (var 4) (var 2)) (var 5 * var 5)) :=
  closeUniv 7 (.impI (.impI (rate f g _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_named_log_Gamma_apart_derivative_modulus_closed (f g : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (input f g (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
        apart (stepF g f) (var 6) (stepData (var 1) (var 0)) ⟶
        le (coefficient (var 6) (var 4) (var 2) * unit (var 7)) (var 5 * var 5) ⟶
        independentRate (nameF f g) (psiF f) (data f g (var 0) (var 1) (var 2) (var 3) (var 6))
          (psiData (var 0) (var 2) (var 3)) one (unit (var 7))) :=
  closeUniv 8 (.impI (.impI (.impI (modulus f g _ _ _ _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianNamedLogGammaDigammaDerivative
