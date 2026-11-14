import PA194PAeqTermValidity
import PA194PAeqAtomCode
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194PAeqTermBlueprint
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem equality_valid {n s t : V} (hs : IsSemiterm PA194PAeq.language n s)
    (ht : IsSemiterm PA194PAeq.language n t) :
    IsSemiformula PA194PAeq.language n (equalityCode s t) := by
  simp [equalityCode,PA194PAeq.source_relations,hs,ht]
theorem less_valid {n s t : V} (hs : IsSemiterm PA194PAeq.language n s)
    (ht : IsSemiterm PA194PAeq.language n t) :
    IsSemiformula PA194PAeq.language n (lessCode s t) := by
  simp only [lessCode,IsSemiformula.exs]
  apply equality_valid
  · simp [PA194PAeq.source_functions,hs.termBShift]
  · exact ht.termBShift

theorem original_relations (k r : V) : (ℒₒᵣ).IsRel k r ↔ k=2 ∧ (r=0 ∨ r=1) := by
  change (V ⊧/![k,r] “k r. (k=2 ∧ r=0) ∨ (k=2 ∧ r=1)”) ↔ _
  simp; tauto

theorem atom_valid {n k r ts : V} (param : V) (hr : (ℒₒᵣ).IsRel k r)
    (ht : IsSemitermVec ℒₒᵣ k n ts) : IsSemiformula PA194PAeq.language n (atomCode param k r ts) := by
  obtain ⟨rfl,_⟩ := (original_relations _ _).mp hr
  have hs := termCode_valid (ht.nth (i:=0) (by simp))
  have ht' := termCode_valid (ht.nth (i:=1) (by simp))
  unfold atomCode
  split_ifs
  · exact equality_valid hs ht'
  · exact less_valid hs ht'


#print axioms equality_valid
#print axioms less_valid
#print axioms atom_valid
end PA194PAeqTermBlueprint
