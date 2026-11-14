import PA194PAeqAtomCompatibility
import PA194PAeqTranslationTermSubst
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194PAeqTermBlueprint
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem atomCode_shift (param : V) {k r ts : V} (hr : (ℒₒᵣ).IsRel k r)
    (ht : IsUTermVec ℒₒᵣ k ts) :
    atomCode param k r (termShiftVec ℒₒᵣ k ts)=Bootstrapping.shift PA194PAeq.language (atomCode param k r ts) := by
  obtain ⟨rfl,_⟩ := (original_relations k r).mp hr
  have hs := termCode_valid (ht.isSemitermVec.nth (i:=0) (by simp))
  have hu := termCode_valid (ht.isSemitermVec.nth (i:=1) (by simp))
  unfold atomCode
  rw [nth_termShiftVec ht (i:=0) (by simp),nth_termShiftVec ht (i:=1) (by simp),
    termCode_shift (ht.nth (i:=0) (by simp)),termCode_shift (ht.nth (i:=1) (by simp))]
  split_ifs
  · exact (equality_shift hs hu).symm
  · exact (less_shift hs hu).symm

theorem atomCode_subst (param : V) {a k n w r ts : V} (hr : (ℒₒᵣ).IsRel a r)
    (hw : IsSemitermVec ℒₒᵣ k n w) (ht : IsSemitermVec ℒₒᵣ a k ts) :
    atomCode param a r (termSubstVec ℒₒᵣ a w ts)=
      subst PA194PAeq.language (termVector k w) (atomCode param a r ts) := by
  obtain ⟨rfl,_⟩ := (original_relations a r).mp hr
  have hs := termCode_valid (ht.nth (i:=0) (by simp))
  have hu := termCode_valid (ht.nth (i:=1) (by simp))
  unfold atomCode
  rw [nth_termSubstVec ht.isUTerm (i:=0) (by simp),nth_termSubstVec ht.isUTerm (i:=1) (by simp),
    termCode_subst hw (ht.nth (i:=0) (by simp)),termCode_subst hw (ht.nth (i:=1) (by simp))]
  split_ifs
  · exact (equality_subst (termVector_valid hw) hs hu).symm
  · exact (less_subst (termVector_valid hw) hs hu).symm

#print axioms atomCode_shift
#print axioms atomCode_subst
end PA194PAeqTermBlueprint
