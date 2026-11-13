import DiophantineConsistency.IPRAStandardTheory
import DiophantineConsistency.IPRACurrentNativeZFC
/-! # Intuitionistic PRA proves: the current equation has no zero ↔ ZFC is consistent

`IPRACurrentNativeZFC.equivalence14` proves the equivalence in the candidate
native theory, and `IPRABoundedRhoZFC.zfcEquiv` identifies its consistency side
with the Gödel–Gentzen image of Foundation's actual ZFC consistency sentence.
`IPRAStandardTheory.provable_iff` shows that the candidate and the standard
presentation of intuitionistic PRA have the same theorems, so both
equivalences are theorems of standard iPRA.

The left side `noZero14` is `∀x̄ ¬(L(x̄) = R(x̄))` for the two sides of the
maintained 14-variable equation, the same equation as in
`PRACurrentConsistencyEndpoint.pra_current_iff_consistency`. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAStandardCurrentEndpoint
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRALanguage DiophantineConsistency.IPRAStandardTheory
open DiophantineConsistency.FoundationZFCConsistencyNat
open DiophantineConsistency.IPRAFoundationZFCMappedNegation DiophantineConsistency.IPRACurrentNativeZFC

/-- **Standard intuitionistic PRA proves that the maintained equation has no
solution iff ZFC is consistent**, with consistency read as the intuitionistic
negation of Foundation's `ZFC ⊢ ⊥` predicate. -/
theorem ipra_current_iff_consistency :
    standardTheory ⊢ noZero14 🡘 ∼mappedNativeRefutation embedding :=
  (provable_iff _).2 equivalence14

/-- The same equivalence with the Gödel–Gentzen translation of Foundation's
actual ZFC consistency sentence. -/
theorem ipra_current_iff_translated_consistency :
    standardTheory ⊢ noZero14 🡘 (Semiformula.lMap embedding sourceSentence)ᴺ := by
  apply (provable_iff _).2
  obtain ⟨h⟩ := equivalence14
  have z := IPRABoundedRhoZFC.zfcEquiv
  exact ⟨Entailment.K_intro
    (Entailment.C_trans (Entailment.K_left h) (Entailment.K_right z))
    (Entailment.C_trans (Entailment.K_left z) (Entailment.K_right h))⟩

end DiophantineConsistency.IPRAStandardCurrentEndpoint
