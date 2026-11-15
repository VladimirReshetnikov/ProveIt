import PA194OrdinaryStandardNorm
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace PA194OrdinaryNativeConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
attribute [local instance] PA194PAeqBind.ordinaryPAeq_delta

theorem ordinary_refutation_standard : ordinaryRefutation.Evalb (M := ℕ) ![] ↔
    Provable PA194PAeq.ordinaryPAeq (⌜(⊥ : Sentence PA194PAeq.language)⌝ : ℕ) := by
  simp [ordinaryRefutation,provabilityPred]
#print axioms ordinary_refutation_standard
end PA194OrdinaryNativeConsistency
