import Current14LiteralPortsMF
import DiophantineConsistency.IPRAStandardCurrentEndpoint

/-! Draft structured-port endpoint using only the authenticated matrix-free
base and the new port assembly. No TeX/PDF semantics or checked claim yet. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Current14StructuredEndpointMF
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

theorem recipe_endpoint : ∃ p : Fin 4 → ℤ,
    p 0 = Current14LiteralPortsMF.beta ∧
    (p 1 : ℚ) = Current14LiteralPortsMF.K ∧
    p 2 = Current14LiteralPortsMF.mu ∧
    p 3 = Current14LiteralPortsMF.omega ∧
    (standardTheory ⊢ noZeroAt p 🡘 ∼mappedNativeRefutation embedding) := by
  refine ⟨CurrentWindowCarry2011.ports, ?_⟩
  obtain ⟨h0,h1,h2,h3⟩ := Current14LiteralPortsMF.all_ports
  refine ⟨h0,h1,h2,h3,?_⟩
  change standardTheory ⊢ noZero14 🡘 ∼mappedNativeRefutation embedding
  exact IPRAStandardCurrentEndpoint.ipra_current_iff_consistency

#print axioms Current14StructuredEndpointMF.recipe_endpoint
end Current14StructuredEndpointMF
