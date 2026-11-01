import DiophantineConsistency.IPRANativeDifferenceForward
import DiophantineConsistency.IPRANativeDifferenceEquality

/-! Connect the checked forward difference proof to the equality-decision
reduction. The positive backward difference implication remains an explicit
native-theory proof premise. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRADifferenceEqualityForwardJoin
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.IPRANativeTheory

def forward
    (hz : nativeTheory ⊢! IPRANativeSubSelf.zeroDecSentence) :
    nativeTheory ⊢! IPRANativeDifferenceEquality.forwardSentence :=
  IPRANativeDifferenceForward.forwardProof hz

def equalityDecidable
    (hz : nativeTheory ⊢! IPRANativeSubSelf.zeroDecSentence)
    (hb : nativeTheory ⊢! IPRANativeDifferenceEquality.backwardSentence) :
    nativeTheory ⊢! IPRANativeAtomStability.eqDecSentence :=
  IPRANativeDifferenceEquality.equalityDecidable hz (forward hz) hb
end DiophantineConsistency.IPRADifferenceEqualityForwardJoin
