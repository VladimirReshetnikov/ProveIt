import DiophantineConsistency.IPRAFoundationZFCMappedErasure
import DiophantineConsistency.IPRANativeTheory
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAFoundationZFCCandidateErasure
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.FoundationZFCConsistencyNat DiophantineConsistency.FoundationHAConsistencyNormalization
open DiophantineConsistency.PRALanguage DiophantineConsistency.IPRANativeTheory
open DiophantineConsistency.IPRANativeFormula DiophantineConsistency.IPRAFoundationZFCWitnessBound
open DiophantineConsistency.IPRAFoundationZFCMappedErasure DiophantineConsistency.IPRAFoundationZFCMappedNegation
local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (DiophantineConsistency.PRAFiniteFunctionCodes.Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

def candidateErasure : nativeTheory ⊢! native (Semiformula.lMap embedding boundedRefutation) 🡒
    native (Semiformula.lMap embedding rho) := exactErasure embedding

def candidateTwoPremises
    (hbound : nativeTheory ⊢! (Semiformula.lMap embedding rho)ᴺ 🡒 (Semiformula.lMap embedding boundedRefutation)ᴺ)
    (hcompare : nativeTheory ⊢! (Semiformula.lMap embedding boundedRefutation)ᴺ 🡒
      ∼∼native (Semiformula.lMap embedding boundedRefutation)) :
    nativeTheory ⊢! (Semiformula.lMap embedding sourceSentence)ᴺ 🡘 ∼mappedNativeRefutation embedding :=
  mappedZFCNegationTwoPremises embedding hbound hcompare
end DiophantineConsistency.IPRAFoundationZFCCandidateErasure
