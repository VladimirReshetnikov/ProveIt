import DiophantineConsistency.IPRADeepBoundJoin
import DiophantineConsistency.IPRANativeEqualityDecidable

/-! The exact Foundation ZFC comparison after discharging the translated
witness bound and native equality decidability. Deep matrix stability remains
an explicit proof schema. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRADeepEqualityJoin
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder
open DiophantineConsistency.FoundationZFCConsistencyNat
open DiophantineConsistency.PRALanguage DiophantineConsistency.IPRANativeTheory
open DiophantineConsistency.IPRANativeDeepStability DiophantineConsistency.IPRAStableBackwardFinite
open DiophantineConsistency.IPRAFoundationZFCReachStability DiophantineConsistency.IPRAFoundationZFCStabilityWitness
open DiophantineConsistency.IPRAFoundationZFCMappedNegation

def zfcEquiv
    (deep : ∀ ψ, ψ ∈ reachList (matrixOpen embedding) → DeepNeed ψ → StabilityWitness nativeTheory ψ) :
    nativeTheory ⊢! (Semiformula.lMap embedding sourceSentence)ᴺ 🡘 ∼mappedNativeRefutation embedding :=
  DiophantineConsistency.IPRADeepBoundJoin.zfcEquiv
    DiophantineConsistency.IPRANativeEqualityDecidable.equalityDecidable deep
end DiophantineConsistency.IPRADeepEqualityJoin
