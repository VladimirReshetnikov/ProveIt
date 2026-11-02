import DiophantineConsistency.RotationCoverageBounded
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace RotationBoundedCases
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticWindowDigits DiophantineConsistency.ArithmeticCyclicWord
open RotationAllCases
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem digit (X n e k : V) (hk : k<n) (he : e<67*n) (hX : X<Exp.exp (67*n)) :
    ∃ q r, q<n ∧ r<67 ∧ (q+1<n ∨ (q+1=n ∧ dig 67 X (q+1)=0)) ∧
      (dig 67 (rot 1 (67*n) X e) k = fragment X q r ∨
       ∃ a, 0<a ∧ a<67 ∧ dig 67 (rot 1 (67*n) X e) k =
         (X % Exp.exp (67-a))*Exp.exp a + fragment X q r % Exp.exp a) := by
  rcases RotationCoverageBounded.coverage n e k hk he with ⟨q,r,u,hq,hr,hk',hL⟩ | ⟨u,q,r,hq,he',hi,hr⟩ | ⟨a,t,q,r,ha0,ha,hq,he',hL,hi,hr⟩
  · refine ⟨q,r,hq,hr,RotationIndexBounds.next_in_range_or_zero X n q hq hX,Or.inl ?_⟩
    exact RotationAdjacent.unwrapped_adjacent X (67*n) e k q r u hr hL hk' hX
  · refine ⟨q,r,hq,hr,RotationIndexBounds.next_in_range_or_zero X n q hq hX,Or.inl ?_⟩
    exact WrappedAdjacent.wrapped_adjacent X (67*n) e k u q r he' hi hr
  · refine ⟨q,r,hq,hr,RotationIndexBounds.next_in_range_or_zero X n q hq hX,Or.inr ⟨a,ha0,ha,?_⟩⟩
    exact StraddlingAdjacent.straddling_adjacent X (67*n) e k a t q r ha he' hL hX hi hr

theorem reduced_digit (X n E k : V) (hk : k<n) (hX : X<Exp.exp (67*n)) :
    ∃ q r, q<n ∧ r<67 ∧ (q+1<n ∨ (q+1=n ∧ dig 67 X (q+1)=0)) ∧
      (dig 67 (rot 1 (67*n) X (E%(67*n))) k = fragment X q r ∨
       ∃ a, 0<a ∧ a<67 ∧ dig 67 (rot 1 (67*n) X (E%(67*n))) k =
         (X % Exp.exp (67-a))*Exp.exp a + fragment X q r % Exp.exp a) := by
  have hn : 0<n := lt_of_le_of_lt (by simp : (0:V)≤k) hk
  exact digit X n (E%(67*n)) k hk (RotationIndexBounds.reduced_cut_lt n E hn) hX
#print axioms RotationBoundedCases.digit
#print axioms RotationBoundedCases.reduced_digit
end RotationBoundedCases
