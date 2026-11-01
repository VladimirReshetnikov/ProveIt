import DiophantineConsistency.IPRAFoundationZFCCompoundStability
import DiophantineConsistency.IPRANativeOpenDecision
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAFoundationZFCQuantifiedStability
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.FoundationZFCConsistencyNat DiophantineConsistency.FoundationHAConsistencyNormalization
open DiophantineConsistency.PRALanguage DiophantineConsistency.PRAFiniteFunctionCodes
open DiophantineConsistency.IPRANativeTheory DiophantineConsistency.IPRATheoryHilbertBridge
open DiophantineConsistency.IPRANativeAtomStability DiophantineConsistency.IPRANativeAtomCoverage
open DiophantineConsistency.IPRANativeOpenDecision DiophantineConsistency.IPRANativeFormula
open DiophantineConsistency.IPRAFoundationZFCWitnessBound DiophantineConsistency.IPRAFoundationZFCMappedNegation
open DiophantineConsistency.IPRAStableBackward DiophantineConsistency.IPRAStableBackwardReach
open DiophantineConsistency.IPRAStableBackwardFinite DiophantineConsistency.IPRAFoundationZFCReachStability
open DiophantineConsistency.IPRAFoundationZFCStabilityWitness DiophantineConsistency.IPRAFoundationZFCTheoryStability
open DiophantineConsistency.IPRAFoundationZFCCompoundStability
local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

def stableFromOpenAndQuantified (heq : nativeTheory ⊢! eqDecSentence)
    (quantified : ∀ ψ, ψ ∈ reachList (matrixOpen embedding) → CompoundNeed ψ → ¬ψ.Open → StabilityWitness nativeTheory ψ) :
    ∀ ψ, Reach (matrixOpen embedding) ψ → NeedsStability ψ →
      extended nativeTheory ⊢! ∼∼native ψ 🡒 native ψ := by
  intro ψ hreach hneed
  classical
  by_cases hopen : ψ.Open
  · exact openStability heq ψ hopen
  · cases ψ with
    | rel r v => exact atomStable heq r v
    | or φ χ => exact stabilityFromWitness _ (quantified _ (reachMem hreach) trivial hopen)
    | exs φ => exact stabilityFromWitness _ (quantified _ (reachMem hreach) trivial hopen)
    | nrel r v => cases hneed
    | verum => cases hneed
    | falsum => cases hneed
    | and φ χ => cases hneed
    | all φ => cases hneed

def zfcEquiv (hbound : nativeTheory ⊢! (Semiformula.lMap embedding rho)ᴺ 🡒 (Semiformula.lMap embedding boundedRefutation)ᴺ)
    (heq : nativeTheory ⊢! eqDecSentence)
    (quantified : ∀ ψ, ψ ∈ reachList (matrixOpen embedding) → CompoundNeed ψ → ¬ψ.Open → StabilityWitness nativeTheory ψ) :
    nativeTheory ⊢! (Semiformula.lMap embedding sourceSentence)ᴺ 🡘 ∼mappedNativeRefutation embedding :=
  zfcEquivFromTheory embedding hbound (stableFromOpenAndQuantified heq quantified)
end DiophantineConsistency.IPRAFoundationZFCQuantifiedStability
