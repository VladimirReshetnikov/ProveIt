import DiophantineConsistency.IPRAFoundationZFCCandidateNegation

noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.FoundationZFCConsistencyNat
open DiophantineConsistency.FoundationHAConsistencyNormalization
open DiophantineConsistency.PRALanguage DiophantineConsistency.IPRANativeTheory
open DiophantineConsistency.IPRAFoundationZFCMappedNegation
open DiophantineConsistency.IPRAFoundationZFCCandidateNegation

example (hb : nativeTheory ⊢! (Semiformula.lMap embedding rho)ᴺ 🡒
    ∼∼mappedNativeRefutation embedding) :
    nativeTheory ⊢! (Semiformula.lMap embedding sourceSentence)ᴺ 🡘
      ∼mappedNativeRefutation embedding := candidateZFCConsistencyEquivalent hb

#print axioms DiophantineConsistency.IPRAFoundationZFCCandidateNegation.candidateZFCConsistencyEquivalent
