import DiophantineConsistency.Sign14Positive74ObjectSentenceIff
import DiophantineConsistency.Sign14Positive74IPRAEndpoint

/-! SOURCE ONLY: explicitly guarded positive-coordinate iPRA endpoints. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74ObjectEndpoint
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation FoundationZFCConsistencyNat
open Sign14Positive74ObjectGuard Sign14Positive74ObjectSentenceIff

attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
  CurrentWindowCarry2011.ports IPRAExpressionNative.nativeNoZero

theorem native_equivalence : nativeTheory ⊢
    currentPositiveNoZero 🡘 ∼mappedNativeRefutation embedding := by
  have a := sentenceIff (Sign14Positive74.expression CurrentWindowCarry2011.ports)
  obtain ⟨b⟩ := Sign14Positive74IPRA.native_equivalence
  apply Nonempty.intro
  exact Entailment.K_intro
    (Entailment.C_trans (Entailment.K_left a) (Entailment.K_left b))
    (Entailment.C_trans (Entailment.K_right b) (Entailment.K_right a))

theorem standard_equivalence : IPRAStandardTheory.standardTheory ⊢
    currentPositiveNoZero 🡘 ∼mappedNativeRefutation embedding :=
  (IPRAStandardTheory.provable_iff _).2 native_equivalence

theorem standard_translated_equivalence : IPRAStandardTheory.standardTheory ⊢
    currentPositiveNoZero 🡘 (Semiformula.lMap embedding sourceSentence)ᴺ := by
  apply (IPRAStandardTheory.provable_iff _).2
  obtain ⟨h⟩ := (IPRAStandardTheory.provable_iff _).1 standard_equivalence
  have z := IPRABoundedRhoZFC.zfcEquiv
  exact ⟨Entailment.K_intro
    (Entailment.C_trans (Entailment.K_left h) (Entailment.K_right z))
    (Entailment.C_trans (Entailment.K_left z) (Entailment.K_right h))⟩
end DiophantineConsistency.Sign14Positive74ObjectEndpoint
#print axioms DiophantineConsistency.Sign14Positive74ObjectEndpoint.native_equivalence
#print axioms DiophantineConsistency.Sign14Positive74ObjectEndpoint.standard_equivalence
#print axioms DiophantineConsistency.Sign14Positive74ObjectEndpoint.standard_translated_equivalence
