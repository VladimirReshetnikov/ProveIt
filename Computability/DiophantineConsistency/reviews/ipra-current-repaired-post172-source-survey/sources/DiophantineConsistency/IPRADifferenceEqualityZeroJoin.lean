import DiophantineConsistency.IPRADifferenceEqualityForwardJoin
import DiophantineConsistency.IPRAZeroStepNative

/-! Discharge native zero decidability in the two-difference reduction.
Positive reverse difference correctness remains an explicit proof premise. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRADifferenceEqualityZeroJoin
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.IPRANativeTheory

def equalityDecidable
    (hb : nativeTheory ⊢! IPRANativeDifferenceEquality.backwardSentence) :
    nativeTheory ⊢! IPRANativeAtomStability.eqDecSentence :=
  IPRADifferenceEqualityForwardJoin.equalityDecidable
    (Classical.choice IPRAZeroStepNative.zero_decidable) hb
end DiophantineConsistency.IPRADifferenceEqualityZeroJoin
