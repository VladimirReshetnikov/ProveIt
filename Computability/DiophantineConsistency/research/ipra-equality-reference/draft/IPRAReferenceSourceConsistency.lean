import DiophantineConsistency.IPRAReferenceInductionConversion
import DiophantineConsistency.IPRABoundedRhoZFC

/-! Uncompiled candidate transfer of the existing native-iPRA comparison to
the equality-only reference theory. It concerns the GG reading of Foundation's
own selected ZFC consistency sentence and the same mapped refutation formula;
it does not assert equivalence to an arbitrary alternative proof coding. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAReferenceSourceConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open IPRAOrderErasure IPRAEqualityOnlyReference IPRAFoundationZFCMappedNegation

def translatedSource : Sentenceᵢ IPRAEqualityOnlyReference.language :=
  erase ((Semiformula.lMap PRALanguage.embedding FoundationZFCConsistencyNat.sourceSentence)ᴺ)

theorem equivalence : referenceTheory ⊢ translatedSource 🡘
    ∼(erase (mappedNativeRefutation PRALanguage.embedding)) := by
  have hnative : IPRANativeTheory.nativeTheory ⊢
      (Semiformula.lMap PRALanguage.embedding FoundationZFCConsistencyNat.sourceSentence)ᴺ 🡘
        ∼mappedNativeRefutation PRALanguage.embedding :=
    ⟨IPRABoundedRhoZFC.zfcEquiv⟩
  have h := IPRAReferenceInductionConversion.nativeToReference hnative
  simpa only [translatedSource, LogicalConnective.iff, Semiformulaᵢ.neg_def, erase] using h

end DiophantineConsistency.IPRAReferenceSourceConsistency
