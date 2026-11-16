module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAeqCodeAtoms
public import M6PA.Calibration.FoundationPAeqCodeTermLift
@[expose] public section
namespace M6.PA.FoundationPAeqCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem equality_shift {n s t : V} (hs : IsSemiterm Presentation.language n s)
    (ht : IsSemiterm Presentation.language n t) :
    Bootstrapping.shift Presentation.language (equalityCode s t)=
      equalityCode (termShift Presentation.language s) (termShift Presentation.language t) := by
  simp [equalityCode,Presentation.source_relations,hs.isUTerm,ht.isUTerm]

theorem equality_subst {k n w s t : V} (hw : IsSemitermVec Presentation.language k n w)
    (hs : IsSemiterm Presentation.language k s) (ht : IsSemiterm Presentation.language k t) :
    subst Presentation.language w (equalityCode s t)=
      equalityCode (termSubst Presentation.language w s) (termSubst Presentation.language w t) := by
  simp [equalityCode,Presentation.source_relations,hs.isUTerm,ht.isUTerm]

theorem less_shift {n s t : V} (hs : IsSemiterm Presentation.language n s)
    (ht : IsSemiterm Presentation.language n t) :
    Bootstrapping.shift Presentation.language (lessCode s t)=
      lessCode (termShift Presentation.language s) (termShift Presentation.language t) := by
  have hadd : IsSemiterm Presentation.language (n+1)
      (qqFunc 2 2 (termBShift Presentation.language s∷(qqFunc 1 1 (qqBvar 0∷0)∷0))) := by
    simp [Presentation.source_functions,hs.termBShift]
  have he := equality_valid hadd ht.termBShift
  simp only [lessCode]
  rw [shift_exs he.isUFormula,equality_shift hadd ht.termBShift]
  simp [Presentation.source_functions,termShift_func,hs.termBShift.isUTerm,
    ←termBShift_termShift hs,←termBShift_termShift ht]

theorem less_subst {k n w s t : V} (hw : IsSemitermVec Presentation.language k n w)
    (hs : IsSemiterm Presentation.language k s) (ht : IsSemiterm Presentation.language k t) :
    subst Presentation.language w (lessCode s t)=
      lessCode (termSubst Presentation.language w s) (termSubst Presentation.language w t) := by
  have hadd : IsSemiterm Presentation.language (k+1)
      (qqFunc 2 2 (termBShift Presentation.language s∷(qqFunc 1 1 (qqBvar 0∷0)∷0))) := by
    simp [Presentation.source_functions,hs.termBShift]
  have he := equality_valid hadd ht.termBShift
  simp only [lessCode]
  rw [substs_ex he.isUFormula,equality_subst hw.qVec hadd ht.termBShift]
  have hn : nth (qVec Presentation.language w) (0:V)=qqBvar 0 := by simp [qVec]
  simp [Presentation.source_functions,termSubst_func,hs.termBShift.isUTerm,
    substs_qVec_bShift hs hw,substs_qVec_bShift ht hw,hn]

#print axioms equality_shift
#print axioms equality_subst
#print axioms less_shift
#print axioms less_subst
end M6.PA.FoundationPAeqCode
