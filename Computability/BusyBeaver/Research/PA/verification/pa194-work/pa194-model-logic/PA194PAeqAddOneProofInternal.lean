import PA194PAeqAddOneProof
import PA194PAeqOrdinaryTheoryClass
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Coding
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace PA194PAeq.AddOne
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
local instance (n : Nat) : DecidableEq (PA194PAeq.Func n) := by
  intro a b; cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)
local instance (n : Nat) : DecidableEq (PA194PAeq.Rel n) := by
  intro a b; cases a <;> cases b; exact isTrue rfl
local instance : PA194PAeq.language.DecidableEq := ⟨fun _ => inferInstance, fun _ => inferInstance⟩
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem addOneProof_internal :
    letI := PA194PAeqBind.ordinaryPAeq_delta
    Proof ordinaryPAeq (⌜(show ordinaryPAeq ⊢! resultSentence from addOneTheoryProof)⌝ : V) (⌜resultSentence⌝ : V) := by
  letI := PA194PAeqBind.ordinaryPAeq_delta
  exact proof_of_quote_proof addOneTheoryProof
#print axioms addOneProof_internal
end PA194PAeq.AddOne
