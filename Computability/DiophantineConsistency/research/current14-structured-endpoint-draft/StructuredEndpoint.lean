import Current14LiteralPorts
import DiophantineConsistency.IPRAStandardCurrentEndpoint

/-! Unchecked draft: state the endpoint with the four structured port recipes.
The existential tuple avoids normalizing a huge closed finite vector in the
kernel; it is not a TeX or PDF semantics. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Current14StructuredEndpoint
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ObjectCurrentEquation2011
open PRALanguage PRATheory PRANoZeroUnary FoundationHANoZero
open IPRAStandardTheory IPRAFoundationZFCMappedNegation IPRACurrentNativeZFC

def noZeroAt (p : Fin 4 → ℤ) : Sentenceᵢ language :=
  let e := positiveShift (expressionAt p)
  ∀⁰* (∼(Semiformulaᵢ.rel Language.ORing.Rel.eq
    ![Semiterm.lMap embedding (sourceTerm 14 (ArithmeticExpression.term Fin.val e.splitNatural.1)),
      Semiterm.lMap embedding (sourceTerm 14 (ArithmeticExpression.term Fin.val e.splitNatural.2))]))

/-- Prospective structured arithmetic statement, conditional on coherent imports. -/
theorem recipe_endpoint : ∃ p : Fin 4 → ℤ,
    p 0 = Current14LiteralPorts.beta ∧
    (p 1 : ℚ) = Current14LiteralPorts.K ∧
    p 2 = Current14LiteralPorts.mu ∧
    p 3 = Current14LiteralPorts.omega ∧
    (standardTheory ⊢ noZeroAt p 🡘 ∼mappedNativeRefutation embedding) := by
  refine ⟨CurrentWindowCarry2011.ports, ?_⟩
  obtain ⟨h0,h1,h2,h3⟩ := Current14LiteralPorts.all_ports
  refine ⟨h0,h1,h2,h3,?_⟩
  change standardTheory ⊢ noZero14 🡘 ∼mappedNativeRefutation embedding
  exact IPRAStandardCurrentEndpoint.ipra_current_iff_consistency

#print axioms recipe_endpoint
end Current14StructuredEndpoint
