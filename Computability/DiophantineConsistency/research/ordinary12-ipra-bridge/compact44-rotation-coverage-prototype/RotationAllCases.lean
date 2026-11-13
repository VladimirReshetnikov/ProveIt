import DiophantineConsistency.RotationCoverage67
import DiophantineConsistency.RotationAdjacent
import DiophantineConsistency.WrappedAdjacent
import DiophantineConsistency.StraddlingAdjacent
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace RotationAllCases
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticWindowDigits DiophantineConsistency.ArithmeticCyclicWord
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def fragment (X q r : V) : V :=
  dig 67 X q / Exp.exp r + (dig 67 X (q+1) % Exp.exp r)*Exp.exp (67-r)

theorem digit (X n e k : V) (hk : k<n) (hX : X<Exp.exp (67*n)) :
    ∃ q r, r<67 ∧
      (dig 67 (rot 1 (67*n) X e) k = fragment X q r ∨
       ∃ a, a<67 ∧ dig 67 (rot 1 (67*n) X e) k =
         (X % Exp.exp (67-a))*Exp.exp a + fragment X q r % Exp.exp a) := by
  rcases RotationCoverage67.coverage n e k hk with ⟨q,r,u,hr,hk',hL⟩ | ⟨u,q,r,he,hi,hr⟩ | ⟨a,t,q,r,ha,he,hL,hi,hr⟩
  · refine ⟨q,r,hr,Or.inl ?_⟩
    exact RotationAdjacent.unwrapped_adjacent X (67*n) e k q r u hr hL hk' hX
  · refine ⟨q,r,hr,Or.inl ?_⟩
    exact WrappedAdjacent.wrapped_adjacent X (67*n) e k u q r he hi hr
  · refine ⟨q,r,hr,Or.inr ⟨a,ha,?_⟩⟩
    exact StraddlingAdjacent.straddling_adjacent X (67*n) e k a t q r ha he hL hX hi hr
#print axioms RotationAllCases.digit
end RotationAllCases
