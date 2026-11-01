import DiophantineConsistency.IPRAFoundationZFCMappedNegation
import DiophantineConsistency.IPRANativeTheory

/-! Conditional exact Foundation ZFC normalization in candidate native iPRA. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAFoundationZFCCandidateNegation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open FoundationZFCConsistencyNat FoundationHAConsistencyNormalization
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (PRAFiniteFunctionCodes.Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

/-- No axiom-image or backward comparison is asserted; the latter is a premise. -/
def candidateZFCConsistencyEquivalent
    (hbackward : nativeTheory ⊢! (Semiformula.lMap embedding rho)ᴺ 🡒
      ∼∼mappedNativeRefutation embedding) :
    nativeTheory ⊢! (Semiformula.lMap embedding sourceSentence)ᴺ 🡘
      ∼mappedNativeRefutation embedding :=
  mappedZFCConsistencyEquivalent embedding hbackward
end DiophantineConsistency.IPRAFoundationZFCCandidateNegation
