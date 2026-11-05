import ClearedCurrentIPRA

/-! An external rational zero equivalence and the iPRA theorem for the
selected cleared integer sentence. No rational object-language syntax. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ClearedCurrentPair
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage IPRAStandardTheory IPRAFoundationZFCMappedNegation
open RationalCarrier64Current RationalCarrier64CurrentSpecialization
open RationalCarrier64CurrentPair ClearedCurrentIPRA

attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix

theorem external_and_cleared_ipra :
    ((∃ v : Fin 14 → ℤ, (∀ j, 0 < v j) ∧
      value64 (portsQ CurrentWindowCarry2011.ports) (inputQ v)
        ((CurrentWindowCarry2011.ports 3 : ℚ) / (CurrentWindowCarry2011.ports 0 : ℚ))
        ((CurrentWindowCarry2011.ports 2 : ℚ) - (CurrentWindowCarry2011.ports 3 : ℚ)) = 0) ↔
     (∃ v : Fin 14 → ℤ, (∀ j, 0 < v j) ∧
      clearedExpression.eval v = 0)) ∧
    (standardTheory ⊢ clearedNoZero 🡘 ∼mappedNativeRefutation embedding) :=
  ⟨external_and_ipra.1, cleared_ipra⟩

#print axioms external_and_cleared_ipra

end DiophantineConsistency.ClearedCurrentPair
