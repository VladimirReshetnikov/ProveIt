import DiophantineConsistency.IPRANativeDeepStability
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAFoundationZFCDeepStability
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.FoundationZFCConsistencyNat DiophantineConsistency.FoundationHAConsistencyNormalization
open DiophantineConsistency.PRALanguage DiophantineConsistency.PRAFiniteFunctionCodes
open DiophantineConsistency.IPRANativeTheory DiophantineConsistency.IPRATheoryHilbertBridge
open DiophantineConsistency.IPRANativeAtomStability DiophantineConsistency.IPRANativeFormula
open DiophantineConsistency.IPRAFoundationZFCWitnessBound DiophantineConsistency.IPRAFoundationZFCMappedNegation
open DiophantineConsistency.IPRAStableBackwardReach DiophantineConsistency.IPRAStableBackwardFinite
open DiophantineConsistency.IPRAFoundationZFCReachStability DiophantineConsistency.IPRAFoundationZFCStabilityWitness
open DiophantineConsistency.IPRAFoundationZFCTheoryStability DiophantineConsistency.IPRANativeDeepStability
local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

theorem atomicGuardNotDeep {k : ℕ} (r : language.Rel k) (v : Fin k → Term language ℕ)
    (q : Proposition language) : ¬ DeepNeed (Semiformula.nrel r v ⋎ q) := by
  simp [DeepNeed]

def zfcEquiv (hbound : nativeTheory ⊢! (Semiformula.lMap embedding rho)ᴺ 🡒 (Semiformula.lMap embedding boundedRefutation)ᴺ)
    (heq : nativeTheory ⊢! eqDecSentence)
    (deep : ∀ ψ, ψ ∈ reachList (matrixOpen embedding) → DeepNeed ψ → StabilityWitness nativeTheory ψ) :
    nativeTheory ⊢! (Semiformula.lMap embedding sourceSentence)ᴺ 🡘 ∼mappedNativeRefutation embedding :=
  zfcEquivFromTheory embedding hbound (fun ψ hr _ =>
    stableNative heq (matrixOpen embedding)
      (fun χ hc hn => stabilityFromWitness χ (deep χ (reachMem hc) hn)) ψ hr)
end DiophantineConsistency.IPRAFoundationZFCDeepStability
