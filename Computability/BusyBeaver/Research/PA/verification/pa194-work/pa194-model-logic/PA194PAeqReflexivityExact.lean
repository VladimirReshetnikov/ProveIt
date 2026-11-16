import PA194PAeqReflexivityAt
import PA194PAeqAtomCompatibility
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194PAeq.Reflexivity
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeqTermBlueprint
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable local instance : ordinaryPAeq.Δ₁ := PA194PAeqBind.ordinaryPAeq_delta

theorem body_quote : (⌜body⌝ : V) = equalityCode (^#0) (^#0) := by
  change ((⌜body⌝ : Semiformula V language 1).val : V) = _
  simp [body,eq,equalityCode,Matrix.vecHead, Matrix.vecTail]
  rfl

theorem reflexivity_substitution {t : V} (ht : IsSemiterm language 0 t) :
    substs1 language t (⌜body⌝ : V) = equalityCode t t := by
  rw [body_quote]
  unfold substs1
  rw [equality_subst (show IsSemitermVec language 1 0 (t∷(0:V)) from by simp [ht])
    (show IsSemiterm language 1 (^#0) from by simp)
    (show IsSemiterm language 1 (^#0) from by simp)]
  simp

theorem atTermCode_exact {t : V} (ht : IsSemiterm language 0 t) :
    letI : ordinaryPAeq.Δ₁ := (ordinaryPAeq.internalize V).Δ₁
    Proof ordinaryPAeq (atTermCode t) (equalityCode t t) := by
  letI : ordinaryPAeq.Δ₁ := (ordinaryPAeq.internalize V).Δ₁
  rw [← reflexivity_substitution ht]
  exact atTermCode_valid ht
#print axioms body_quote
#print axioms reflexivity_substitution
#print axioms atTermCode_exact
end PA194PAeq.Reflexivity
