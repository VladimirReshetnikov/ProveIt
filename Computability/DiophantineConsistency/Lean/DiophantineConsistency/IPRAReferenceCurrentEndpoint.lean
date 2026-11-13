import DiophantineConsistency.IPRAReferenceInductionConversion
import DiophantineConsistency.IPRACurrentNativeZFC
/-! # Equality-only intuitionistic PRA proves: the current equation has no zero ↔ ZFC is consistent

`IPRAEqualityOnlyReference.referenceTheory` is intuitionistic PRA in the
language with `=` as its only relation symbol and the finite primitive-recursive
construction codes as function symbols. `IPRAOrderErasure.erase` reads every
native `<` atom as the comparison-code equation `ltBit(x,y) = 1` and leaves all
other syntax unchanged. Composing `IPRAReferenceInductionConversion.nativeToReference`
with the candidate-theory endpoint `IPRACurrentNativeZFC.equivalence14`
gives the 14-variable equivalence in the reference theory.

The left side is the erasure of `noZero14`, which contains no `<` atom, so it is
the same no-zero formula read in the equality-only language. The right side is
the erasure of the intuitionistic negation of Foundation's `ZFC ⊢ ⊥` predicate.
The second theorem uses the Gödel–Gentzen image of Foundation's ZFC consistency
sentence instead, via `IPRABoundedRhoZFC.zfcEquiv`. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAReferenceCurrentEndpoint
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRALanguage DiophantineConsistency.IPRAEqualityOnlyReference
open DiophantineConsistency.IPRAOrderErasure DiophantineConsistency.FoundationZFCConsistencyNat
open DiophantineConsistency.IPRAFoundationZFCMappedNegation DiophantineConsistency.IPRACurrentNativeZFC

/-- **Equality-only intuitionistic PRA proves that the maintained equation has
no solution iff ZFC is consistent**, with `<` erased to its comparison-code
equation and consistency read as the intuitionistic negation of Foundation's
`ZFC ⊢ ⊥` predicate. -/
theorem reference_current_iff_consistency :
    referenceTheory ⊢ erase noZero14 🡘 ∼erase (mappedNativeRefutation embedding) :=
  IPRAReferenceInductionConversion.nativeToReference equivalence14

/-- The same equivalence with the erased Gödel–Gentzen translation of
Foundation's actual ZFC consistency sentence. -/
theorem reference_current_iff_translated_consistency :
    referenceTheory ⊢ erase noZero14 🡘 erase ((Semiformula.lMap embedding sourceSentence)ᴺ) := by
  refine IPRAReferenceInductionConversion.nativeToReference
    (σ := noZero14 🡘 (Semiformula.lMap embedding sourceSentence)ᴺ) ?_
  obtain ⟨h⟩ := equivalence14
  have z := IPRABoundedRhoZFC.zfcEquiv
  exact ⟨Entailment.K_intro
    (Entailment.C_trans (Entailment.K_left h) (Entailment.K_right z))
    (Entailment.C_trans (Entailment.K_left z) (Entailment.K_right h))⟩

end DiophantineConsistency.IPRAReferenceCurrentEndpoint
