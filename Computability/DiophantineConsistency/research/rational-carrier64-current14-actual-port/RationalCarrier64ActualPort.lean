import RationalCarrier64CurrentSpecialization
import StructuredEndpointMF

/-! Actual current ports: external rational evaluation and the existing
integer-syntax iPRA endpoint are stated as separate claims. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.RationalCarrier64ActualPort

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage IPRAStandardTheory IPRAFoundationZFCMappedNegation
open IPRACurrentNativeZFC RationalCarrier64Current
open RationalCarrier64CurrentSpecialization

attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix

theorem actual_beta_ne : CurrentWindowCarry2011.ports 0 ≠ 0 := by
  change (CurrentMasks2011.beta : ℤ) ≠ 0
  have hr : 1 < CurrentMasks2011.radix := by
    unfold CurrentMasks2011.radix
    norm_num
  have hp : 1 < CurrentMasks2011.radix ^ 2011 := one_lt_pow₀ hr (by decide)
  have hn : 0 < CurrentMasks2011.beta := by
    unfold CurrentMasks2011.beta
    omega
  exact_mod_cast (ne_of_gt hn)

theorem actual_rational_zero_iff :
    (∃ v : Fin 14 → ℤ, (∀ j, 0 < v j) ∧
      value64 (portsQ CurrentWindowCarry2011.ports) (inputQ v)
        ((CurrentWindowCarry2011.ports 3 : ℚ) / (CurrentWindowCarry2011.ports 0 : ℚ))
        ((CurrentWindowCarry2011.ports 2 : ℚ) - (CurrentWindowCarry2011.ports 3 : ℚ)) = 0) ↔
    (∃ v : Fin 14 → ℤ, (∀ j, 0 < v j) ∧
      (ObjectCurrentEquation2011.expressionAt CurrentWindowCarry2011.ports).eval v = 0) :=
  positive_zero_iff CurrentWindowCarry2011.ports actual_beta_ne

/-- This is the existing iPRA theorem about the integer-language syntax. -/
theorem actual_integer_ipra : standardTheory ⊢
    Current14StructuredEndpointMF.noZeroAt CurrentWindowCarry2011.ports 🡘
      ∼mappedNativeRefutation embedding := by
  change standardTheory ⊢ noZero14 🡘 ∼mappedNativeRefutation embedding
  exact IPRAStandardCurrentEndpoint.ipra_current_iff_consistency

#print axioms actual_beta_ne
#print axioms actual_rational_zero_iff
#print axioms actual_integer_ipra

end DiophantineConsistency.RationalCarrier64ActualPort
