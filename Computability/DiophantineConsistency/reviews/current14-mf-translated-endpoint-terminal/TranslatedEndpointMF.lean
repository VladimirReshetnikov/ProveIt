import Current14LiteralPortsMF
import StructuredEndpointMF
import DiophantineConsistency.IPRAStandardCurrentEndpoint

/-! The same structured port tuple, with Foundation's actual consistency
sentence mapped into the PRA language and Gödel–Gentzen translated. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Current14TranslatedEndpointMF
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ObjectCurrentEquation2011
open PRALanguage PRATheory PRANoZeroUnary FoundationHANoZero
open IPRAStandardTheory FoundationZFCConsistencyNat IPRACurrentNativeZFC
open Current14StructuredEndpointMF

theorem recipe_translated_endpoint : ∃ p : Fin 4 → ℤ,
    p 0 = Current14LiteralPortsMF.beta ∧
    (p 1 : ℚ) = Current14LiteralPortsMF.K ∧
    p 2 = Current14LiteralPortsMF.mu ∧
    p 3 = Current14LiteralPortsMF.omega ∧
    (standardTheory ⊢ noZeroAt p 🡘 (Semiformula.lMap embedding sourceSentence)ᴺ) := by
  refine ⟨CurrentWindowCarry2011.ports, ?_⟩
  obtain ⟨h0,h1,h2,h3⟩ := Current14LiteralPortsMF.all_ports
  refine ⟨h0,h1,h2,h3,?_⟩
  change standardTheory ⊢ noZero14 🡘 (Semiformula.lMap embedding sourceSentence)ᴺ
  exact IPRAStandardCurrentEndpoint.ipra_current_iff_translated_consistency

#print axioms Current14TranslatedEndpointMF.recipe_translated_endpoint
end Current14TranslatedEndpointMF
