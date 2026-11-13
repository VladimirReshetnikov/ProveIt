import DiophantineConsistency.IPRAFoundationZFCDeepStability
import DiophantineConsistency.IPRAZFCRefutationBoundGG
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRADeepBoundJoin
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder
open DiophantineConsistency.FoundationZFCConsistencyNat DiophantineConsistency.FoundationHAConsistencyNormalization
open DiophantineConsistency.PRALanguage DiophantineConsistency.IPRANativeTheory
open DiophantineConsistency.IPRANativeAtomStability DiophantineConsistency.IPRANativeDeepStability
open DiophantineConsistency.IPRAStableBackwardFinite DiophantineConsistency.IPRAFoundationZFCReachStability
open DiophantineConsistency.IPRAFoundationZFCStabilityWitness DiophantineConsistency.IPRAFoundationZFCMappedNegation

def zfcEquiv (heq : nativeTheory ⊢! eqDecSentence)
    (deep : ∀ ψ, ψ ∈ reachList (matrixOpen embedding) → DeepNeed ψ → StabilityWitness nativeTheory ψ) :
    nativeTheory ⊢! (Semiformula.lMap embedding sourceSentence)ᴺ 🡘 ∼mappedNativeRefutation embedding := by
  apply IPRAFoundationZFCDeepStability.zfcEquiv ?_ heq deep
  exact IPRAZFCRefutationBoundGG.refutation_bound_gg_proof
end DiophantineConsistency.IPRADeepBoundJoin
