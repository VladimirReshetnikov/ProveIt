import DiophantineConsistency.IPRAStandardTheory

/-! The exceptional source constructor `I(0,0)=0` needs truth to be
interchangeable with truth implying itself. This file proves that fixed
propositional fact in the intuitionistic PRA language and separately in
classical first-order equality logic. It does not yet connect either proof
to a represented proof compiler. -/
set_option autoImplicit false
namespace PA194VerumAlias
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open IPRANativeTheory IPRAStandardTheory PRALanguage

def aliasSentence : Sentenceᵢ language :=
  (⊤ : Sentenceᵢ language) 🡘 ((⊤ : Sentenceᵢ language) 🡒 ⊤)

/-- An explicit intuitionistic derivation; this uses no consistency premise. -/
def nativeProof : nativeTheory ⊢! aliasSentence := by
  exact Entailment.E_intro
    (Entailment.C_of_conseq (Entailment.C_id : nativeTheory ⊢! (⊤ : Sentenceᵢ language) 🡒 ⊤))
    (Entailment.C_of_conseq (Entailment.verum : nativeTheory ⊢! (⊤ : Sentenceᵢ language)))

/-- The same propositional statement is provable in the standard iPRA theory. -/
theorem standardProof : standardTheory ⊢ aliasSentence := by
  exact (provable_iff _).2 ⟨nativeProof⟩

/-- The classical version requires only first-order equality logic, hence is
available in PA. This is a separate, non-internalized proof statement. -/
theorem classicalEqualityProof : (𝗘𝗤 ℒₒᵣ : ArithmeticTheory) ⊢
    ((⊤ : ArithmeticSentence) 🡘 ((⊤ : ArithmeticSentence) 🡒 (⊤ : ArithmeticSentence))) := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  simp [LogicalConnective.iff]

#print axioms nativeProof
#print axioms standardProof
#print axioms classicalEqualityProof
end PA194VerumAlias
