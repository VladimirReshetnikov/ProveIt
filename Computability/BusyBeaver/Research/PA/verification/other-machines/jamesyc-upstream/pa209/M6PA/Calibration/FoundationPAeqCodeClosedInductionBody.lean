module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAeqCodeIdentityVector
@[expose] public section
/-! A successor induction body constructed directly from a closed matrix with
model-valued parameter arity. Membership in the canonical axiom class is separate. -/
namespace M6.PA.FoundationPAeqCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "PAeq" => Presentation.language

noncomputable def closedBaseVector (m : V) : V := zeroCode∷boundIdentity m
noncomputable def closedStepVector (m : V) : V :=
  qqFunc 1 1 (qqBvar 0∷0)∷termBShiftVec PAeq m (boundIdentity m)
noncomputable def closedSuccessorBody (m q : V) : V :=
  imp PAeq (subst PAeq (closedBaseVector m) q)
    (imp PAeq (qqAll (imp PAeq q (subst PAeq (closedStepVector m) q))) (qqAll q))

theorem closedBaseVector_valid (m : V) : IsSemitermVec PAeq (m+1) m (closedBaseVector m) := by
  simp [closedBaseVector,zeroCode,termShiftVec_cons,Presentation.source_functions,boundIdentity_valid]
theorem closedStepVector_valid (m : V) : IsSemitermVec PAeq (m+1) (m+1) (closedStepVector m) := by
  simp [closedStepVector,Presentation.source_functions,(boundIdentity_valid (L:=PAeq) m).termBShiftVec]

theorem boundIdentity_shift (m : V) : termShiftVec PAeq m (boundIdentity m)=boundIdentity m := by
  have hv := (boundIdentity_valid (L:=PAeq) m).isUTerm
  apply nth_ext' m (by simp [hv]) (by simp)
  intro i hi
  rw [nth_termShiftVec hv hi,boundIdentity_nth m i hi,termShift_bvar]

theorem shiftedIdentity_shift (m : V) :
    termShiftVec PAeq m (termBShiftVec PAeq m (boundIdentity m))=
      termBShiftVec PAeq m (boundIdentity m) := by
  have hv := (boundIdentity_valid (L:=PAeq) m).isUTerm
  apply nth_ext' m (len_termShiftVec (boundIdentity_valid (L:=PAeq) m).termBShiftVec.isUTerm) (len_termBShiftVec hv)
  intro i hi
  rw [nth_termShiftVec (boundIdentity_valid (L:=PAeq) m).termBShiftVec.isUTerm hi,
    nth_termBShiftVec hv hi,boundIdentity_nth m i hi]
  simp

theorem closedBaseVector_shift (m : V) :
    termShiftVec PAeq (m+1) (closedBaseVector m)=closedBaseVector m := by
  simp [closedBaseVector,zeroCode,termShiftVec_cons,Presentation.source_functions,
    (boundIdentity_valid (L:=PAeq) m).isUTerm,boundIdentity_shift]
theorem closedStepVector_shift (m : V) :
    termShiftVec PAeq (m+1) (closedStepVector m)=closedStepVector m := by
  simp [closedStepVector,termShiftVec_cons,Presentation.source_functions,
    (boundIdentity_valid (L:=PAeq) m).termBShiftVec.isUTerm,shiftedIdentity_shift]

theorem closedSuccessorBody_valid {m q : V} (hq : IsSemiformula PAeq (m+1) q) :
    IsSemiformula PAeq m (closedSuccessorBody m q) := by
  simp [closedSuccessorBody,hq,hq.subst (closedBaseVector_valid m),hq.subst (closedStepVector_valid m)]
theorem closedSuccessorBody_shift {m q : V} (hq : IsSemiformula PAeq (m+1) q)
    (hs : shift PAeq q=q) : shift PAeq (closedSuccessorBody m q)=closedSuccessorBody m q := by
  have hb := hq.subst (closedBaseVector_valid m)
  have ht := hq.subst (closedStepVector_valid m)
  simp [closedSuccessorBody,imp,Bootstrapping.shift_neg hb,Bootstrapping.shift_neg hq,Bootstrapping.shift_neg ht,hq.isUFormula,hb.isUFormula,ht.isUFormula,
    shift_substs hq (closedBaseVector_valid m),shift_substs hq (closedStepVector_valid m),
    closedBaseVector_shift,closedStepVector_shift,hs]

#print axioms closedBaseVector_valid
#print axioms closedStepVector_valid
#print axioms boundIdentity_shift
#print axioms shiftedIdentity_shift
#print axioms closedBaseVector_shift
#print axioms closedStepVector_shift
#print axioms closedSuccessorBody_valid
#print axioms closedSuccessorBody_shift
end M6.PA.FoundationPAeqCode

