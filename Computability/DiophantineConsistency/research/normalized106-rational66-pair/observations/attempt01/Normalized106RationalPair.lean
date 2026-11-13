import Normalized106RationalActual
import DiophantineConsistency.ModelCarrierCurrent

/-! External actual-port rational evaluation and the historical integer-syntax
iPRA endpoint are separate conjuncts; there is no rational internal formula. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Normalized106RationalPair
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open Normalized106Rational66 Normalized106RationalSpecialization
open Normalized106RationalActual AdaptiveEquationSyntax2011

attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix

theorem external_and_integer_ipra :
    ((∃ v : Fin 14 → ℤ, (∀ j, 0 < v j) ∧
      value66 (portsQ CurrentWindowCarry2011.ports) (inputQ v)
        ((CurrentWindowCarry2011.ports 3 : ℚ) / (CurrentWindowCarry2011.ports 0 : ℚ))
        ((CurrentWindowCarry2011.ports 2 : ℚ) - (CurrentWindowCarry2011.ports 3 : ℚ)) = 0) ↔
     (∃ v : Fin 14 → ℤ, (∀ j, 0 < v j) ∧
      (ModelCarrierCurrent.expressionAt106 CurrentWindowCarry2011.ports).eval v = 0)) ∧
    (IPRAStandardTheory.standardTheory ⊢ IPRAExpressionNative.nativeNoZero
      (positiveShift (ModelCarrierCurrent.expressionAt106 CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding) :=
  ⟨actual_positive_zero_iff, ModelCarrierCurrent.standard_equivalence106⟩

#print axioms external_and_integer_ipra

end DiophantineConsistency.Normalized106RationalPair
