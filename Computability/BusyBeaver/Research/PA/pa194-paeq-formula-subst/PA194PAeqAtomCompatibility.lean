import PA194PAeqAtomValidity
import PA194PAeqTranslationQVec
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
namespace PA194PAeqTermBlueprint
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem equality_shift {n s t : V} (hs : IsSemiterm PA194PAeq.language n s)
    (ht : IsSemiterm PA194PAeq.language n t) :
    Bootstrapping.shift PA194PAeq.language (equalityCode s t)=
      equalityCode (termShift PA194PAeq.language s) (termShift PA194PAeq.language t) := by
  simp [equalityCode,PA194PAeq.source_relations,hs.isUTerm,ht.isUTerm]

theorem equality_subst {k n w s t : V} (hw : IsSemitermVec PA194PAeq.language k n w)
    (hs : IsSemiterm PA194PAeq.language k s) (ht : IsSemiterm PA194PAeq.language k t) :
    subst PA194PAeq.language w (equalityCode s t)=
      equalityCode (termSubst PA194PAeq.language w s) (termSubst PA194PAeq.language w t) := by
  simp [equalityCode,PA194PAeq.source_relations,hs.isUTerm,ht.isUTerm]

theorem less_shift {n s t : V} (hs : IsSemiterm PA194PAeq.language n s)
    (ht : IsSemiterm PA194PAeq.language n t) :
    Bootstrapping.shift PA194PAeq.language (lessCode s t)=
      lessCode (termShift PA194PAeq.language s) (termShift PA194PAeq.language t) := by
  have hadd : IsSemiterm PA194PAeq.language (n+1)
      (qqFunc 2 2 (termBShift PA194PAeq.language s∷(qqFunc 1 1 (qqBvar 0∷0)∷0))) := by
    simp [PA194PAeq.source_functions,hs.termBShift]
  have he := equality_valid hadd ht.termBShift
  simp only [lessCode]
  rw [shift_exs he.isUFormula,equality_shift hadd ht.termBShift]
  simp [PA194PAeq.source_functions,termShift_func,hs.termBShift.isUTerm,
    ←termBShift_termShift hs,←termBShift_termShift ht]

theorem less_subst {k n w s t : V} (hw : IsSemitermVec PA194PAeq.language k n w)
    (hs : IsSemiterm PA194PAeq.language k s) (ht : IsSemiterm PA194PAeq.language k t) :
    subst PA194PAeq.language w (lessCode s t)=
      lessCode (termSubst PA194PAeq.language w s) (termSubst PA194PAeq.language w t) := by
  have hadd : IsSemiterm PA194PAeq.language (k+1)
      (qqFunc 2 2 (termBShift PA194PAeq.language s∷(qqFunc 1 1 (qqBvar 0∷0)∷0))) := by
    simp [PA194PAeq.source_functions,hs.termBShift]
  have he := equality_valid hadd ht.termBShift
  simp only [lessCode]
  rw [substs_ex he.isUFormula,equality_subst hw.qVec hadd ht.termBShift]
  have hn : nth (qVec PA194PAeq.language w) (0:V)=qqBvar 0 := by simp [qVec]
  simp [PA194PAeq.source_functions,termSubst_func,hs.termBShift.isUTerm,
    substs_qVec_bShift hs hw,substs_qVec_bShift ht hw,hn]

#print axioms equality_shift
#print axioms equality_subst
#print axioms less_shift
#print axioms less_subst
end PA194PAeqTermBlueprint
