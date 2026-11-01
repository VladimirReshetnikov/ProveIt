import DiophantineConsistency.IPRAFoundationZFCStabilityWitness
import DiophantineConsistency.IPRANativeTheory
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAFoundationZFCCandidateStability
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.FoundationZFCConsistencyNat DiophantineConsistency.FoundationHAConsistencyNormalization
open DiophantineConsistency.PRALanguage DiophantineConsistency.IPRANativeTheory
open DiophantineConsistency.IPRAFoundationZFCWitnessBound DiophantineConsistency.IPRAFoundationZFCMappedNegation
open DiophantineConsistency.IPRAStableBackward DiophantineConsistency.IPRAStableBackwardReach
open DiophantineConsistency.IPRAFoundationZFCReachStability DiophantineConsistency.IPRAFoundationZFCStabilityWitness
local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (DiophantineConsistency.PRAFiniteFunctionCodes.Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

def candidateEquiv
    (hbound : nativeTheory ⊢! (Semiformula.lMap embedding rho)ᴺ 🡒 (Semiformula.lMap embedding boundedRefutation)ᴺ)
    (witnesses : ∀ ψ, Reach (matrixOpen embedding) ψ → NeedsStability ψ → StabilityWitness nativeTheory ψ) :
    nativeTheory ⊢! (Semiformula.lMap embedding sourceSentence)ᴺ 🡘 ∼mappedNativeRefutation embedding :=
  zfcEquivFromWitnesses embedding hbound witnesses
end DiophantineConsistency.IPRAFoundationZFCCandidateStability
