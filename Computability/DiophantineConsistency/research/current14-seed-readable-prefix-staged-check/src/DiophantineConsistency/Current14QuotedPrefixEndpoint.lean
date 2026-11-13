import DiophantineConsistency.Current14QuotedPrefixQuote

/-! SOURCE ONLY. Staged from the independently reviewed prefix draft. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Current14QuotedPrefix
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory PRANoZeroUnary FoundationHANoZero
open ObjectCurrentEquation2011 IPRAStandardTheory IPRACurrentNativeZFC
open IPRAFoundationZFCMappedNegation Sign17LinesCurrent14Endpoint
open Sign17ReadableCurrent14Endpoint


def quoteSentence : Option (Sentenceᵢ language) := do
  let e ← quotedExpr linePorts
  let e := positiveShift e
  some (∀⁰* (∼(Semiformulaᵢ.rel Language.ORing.Rel.eq
    ![Semiterm.lMap embedding (sourceTerm 14 (ArithmeticExpression.term Fin.val e.splitNatural.1)),
      Semiterm.lMap embedding (sourceTerm 14 (ArithmeticExpression.term Fin.val e.splitNatural.2))])))

theorem quoteSentence_eq : quoteSentence = some displayedNoZero := by
  unfold quoteSentence
  rw [quotedExpr_eq]
  all_goals rfl

theorem quoted_endpoint : ∃ φ, quoteSentence = some φ ∧
    (standardTheory ⊢ φ 🡘 ∼mappedNativeRefutation embedding) := by
  exact ⟨displayedNoZero, quoteSentence_eq, displayed_endpoint⟩

end DiophantineConsistency.Current14QuotedPrefix
#print axioms DiophantineConsistency.Current14QuotedPrefix.quoteSentence_eq
#print axioms DiophantineConsistency.Current14QuotedPrefix.quoted_endpoint
