import DiophantineConsistency.IPRADifferenceStepClosure
import DiophantineConsistency.IPRAReconstructBridgeOpen

/-! An unconditional proof of universal equality decidability in the candidate
native intuitionistic PRA theory, from its actual induction and defining axioms. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRANativeEqualityDecidable
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.IPRANativeTheory DiophantineConsistency.IPRANativeAtomStability

def equalityDecidable : nativeTheory ⊢! eqDecSentence :=
  DiophantineConsistency.IPRADifferenceStepClosure.equalityDecidable
    (fun x y => DiophantineConsistency.IPRAReconstructBridgeOpen.open_bridge x y)
end DiophantineConsistency.IPRANativeEqualityDecidable
