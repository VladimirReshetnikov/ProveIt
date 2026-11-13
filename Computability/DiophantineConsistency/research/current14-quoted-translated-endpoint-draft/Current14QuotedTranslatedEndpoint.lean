import DiophantineConsistency.Current14QuotedPrefixEndpoint

/-! The checked normalized quote and Foundation's translated consistency sentence. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Current14QuotedPrefix
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory PRANoZeroUnary FoundationHANoZero
open IPRAStandardTheory FoundationZFCConsistencyNat
open Sign17LinesCurrent14Endpoint Sign17ReadableCurrent14Endpoint

theorem quoted_translated_endpoint : ∃ φ, quoteSentence = some φ ∧
    (standardTheory ⊢ φ 🡘 (Semiformula.lMap embedding sourceSentence)ᴺ) := by
  refine ⟨displayedNoZero, quoteSentence_eq, ?_⟩
  rw [displayedNoZero_eq]
  exact line_endpoint_translated

end DiophantineConsistency.Current14QuotedPrefix
#print axioms DiophantineConsistency.Current14QuotedPrefix.quoted_translated_endpoint
