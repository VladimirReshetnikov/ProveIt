import RationalCarrier64ActualExternal
import DiophantineConsistency.IPRAStandardCurrentEndpoint

/-! An external rational-evaluation fact and the pre-existing iPRA theorem
about integer syntax, as separate conjuncts. No rational internal formula. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.RationalCarrier64CurrentPair
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage IPRAStandardTheory IPRAFoundationZFCMappedNegation
open IPRACurrentNativeZFC RationalCarrier64Current
open RationalCarrier64CurrentSpecialization RationalCarrier64ActualExternal

attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix

theorem external_and_ipra :
    ((∃ v : Fin 14 → ℤ, (∀ j, 0 < v j) ∧
      value64 (portsQ CurrentWindowCarry2011.ports) (inputQ v)
        ((CurrentWindowCarry2011.ports 3 : ℚ) / (CurrentWindowCarry2011.ports 0 : ℚ))
        ((CurrentWindowCarry2011.ports 2 : ℚ) - (CurrentWindowCarry2011.ports 3 : ℚ)) = 0) ↔
     (∃ v : Fin 14 → ℤ, (∀ j, 0 < v j) ∧
      (ObjectCurrentEquation2011.expressionAt CurrentWindowCarry2011.ports).eval v = 0)) ∧
    (standardTheory ⊢ noZero14 🡘 ∼mappedNativeRefutation embedding) :=
  ⟨actual_rational_zero_iff, IPRAStandardCurrentEndpoint.ipra_current_iff_consistency⟩

#print axioms external_and_ipra

end DiophantineConsistency.RationalCarrier64CurrentPair
