import DiophantineConsistency.IPRAFoundationZFCCandidateFiniteStability
import DiophantineConsistency.IPRANativeAtomCoverage
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAFoundationZFCCompoundStability
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.FoundationZFCConsistencyNat DiophantineConsistency.FoundationHAConsistencyNormalization
open DiophantineConsistency.PRALanguage DiophantineConsistency.PRAFiniteFunctionCodes
open DiophantineConsistency.IPRANativeTheory DiophantineConsistency.IPRATheoryHilbertBridge
open DiophantineConsistency.IPRANativeAtomStability DiophantineConsistency.IPRANativeAtomCoverage
open DiophantineConsistency.IPRANativeFormula DiophantineConsistency.IPRAFoundationZFCWitnessBound
open DiophantineConsistency.IPRAFoundationZFCMappedNegation DiophantineConsistency.IPRAStableBackward
open DiophantineConsistency.IPRAStableBackwardReach DiophantineConsistency.IPRAStableBackwardFinite
open DiophantineConsistency.IPRAFoundationZFCReachStability DiophantineConsistency.IPRAFoundationZFCStabilityWitness
open DiophantineConsistency.IPRAFoundationZFCTheoryStability
local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

def CompoundNeed : Proposition language → Prop
  | .or _ _ => True
  | .exs _ => True
  | _ => False

def stableFromAtomsAndCompounds (heq : nativeTheory ⊢! eqDecSentence)
    (compounds : ∀ ψ, ψ ∈ reachList (matrixOpen embedding) → CompoundNeed ψ → StabilityWitness nativeTheory ψ) :
    ∀ ψ, Reach (matrixOpen embedding) ψ → NeedsStability ψ →
      extended nativeTheory ⊢! ∼∼native ψ 🡒 native ψ := by
  intro ψ hreach hneed
  cases ψ with
  | rel r v => exact atomStable heq r v
  | or φ χ => exact stabilityFromWitness _ (compounds _ (reachMem hreach) trivial)
  | exs φ => exact stabilityFromWitness _ (compounds _ (reachMem hreach) trivial)
  | nrel r v => cases hneed
  | verum => cases hneed
  | falsum => cases hneed
  | and φ χ => cases hneed
  | all φ => cases hneed

def zfcEquiv (hbound : nativeTheory ⊢! (Semiformula.lMap embedding rho)ᴺ 🡒 (Semiformula.lMap embedding boundedRefutation)ᴺ)
    (heq : nativeTheory ⊢! eqDecSentence)
    (compounds : ∀ ψ, ψ ∈ reachList (matrixOpen embedding) → CompoundNeed ψ → StabilityWitness nativeTheory ψ) :
    nativeTheory ⊢! (Semiformula.lMap embedding sourceSentence)ᴺ 🡘 ∼mappedNativeRefutation embedding :=
  zfcEquivFromTheory embedding hbound (stableFromAtomsAndCompounds heq compounds)
end DiophantineConsistency.IPRAFoundationZFCCompoundStability
