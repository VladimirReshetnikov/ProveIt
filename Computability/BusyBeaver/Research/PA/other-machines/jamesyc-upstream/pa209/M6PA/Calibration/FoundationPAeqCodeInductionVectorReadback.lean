module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAeqCodeClosedInductionBody
@[expose] public section
namespace M6.PA.FoundationPAeqCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "PAeq" => Presentation.language

theorem bShift_fvarVec (m : V) : termBShiftVec PAeq m (fvarVec m)=fvarVec m := by
  have hv := (target_fvarVec_valid m 0).isUTerm
  apply nth_ext' m (by simp [hv]) (by simp)
  intro i hi
  rw [nth_termBShiftVec hv hi,nth_fvarVec m i hi,termBShift_fvar]
theorem qVec_fvarVec (m : V) : qVec PAeq (fvarVec m)=qqBvar 0∷fvarVec m := by
  simp [qVec,bShift_fvarVec]
theorem substVec_fvarVec (m w : V) : termSubstVec PAeq m w (fvarVec m)=fvarVec m := by
  have hv := (target_fvarVec_valid m 0).isUTerm
  apply nth_ext' m (by simp [hv]) (by simp)
  intro i hi
  rw [nth_termSubstVec hv hi,nth_fvarVec m i hi,termSubst_fvar]
theorem substVec_boundIdentity {m n w : V} (hw : IsSemitermVec PAeq m n w) :
    termSubstVec PAeq m w (boundIdentity m)=w := by
  have hv := (boundIdentity_valid (L:=PAeq) m).isUTerm
  apply nth_ext' m (by simp [hv]) hw.lh
  intro i hi
  rw [nth_termSubstVec hv hi,boundIdentity_nth m i hi,termSubst_bvar]
theorem substVec_liftedFree (m : V) {t : V} (ht : IsUTerm PAeq t) :
    termSubstVec PAeq (m+1) (t∷0) (qVec PAeq (fvarVec m))=t∷fvarVec m := by
  rw [qVec_fvarVec,termSubstVec_cons (by simp) (target_fvarVec_valid m 0).isUTerm]
  simp [substVec_fvarVec]
theorem closedBaseVector_readback (m : V) :
    termSubstVec PAeq (m+1) (fvarVec m) (closedBaseVector m)=zeroCode∷fvarVec m := by
  unfold closedBaseVector
  rw [termSubstVec_cons (by simp [zeroCode,Presentation.source_functions]) (boundIdentity_valid (L:=PAeq) m).isUTerm,
    substVec_boundIdentity (target_fvarVec_valid m 0)]
  simp [zeroCode,Presentation.source_functions]
theorem closedStepVector_readback (m : V) :
    termSubstVec PAeq (m+1) (qVec PAeq (fvarVec m)) (closedStepVector m)=
      qqFunc 1 1 (qqBvar 0∷0)∷fvarVec m := by
  have hv := (boundIdentity_valid (L:=PAeq) m).termBShiftVec.isUTerm
  have htail : termSubstVec PAeq m (qVec PAeq (fvarVec m))
      (termBShiftVec PAeq m (boundIdentity m))=fvarVec m := by
    apply nth_ext' m (by simp [hv]) (by simp)
    intro i hi
    rw [nth_termSubstVec hv hi,nth_termBShiftVec (boundIdentity_valid (L:=PAeq) m).isUTerm hi,
      boundIdentity_nth m i hi,termBShift_bvar,termSubst_bvar,qVec_fvarVec]
    simp [nth_fvarVec m i hi]
  unfold closedStepVector
  rw [termSubstVec_cons (by simp [Presentation.source_functions]) hv,htail,qVec_fvarVec]
  simp [Presentation.source_functions]

#print axioms bShift_fvarVec
#print axioms qVec_fvarVec
#print axioms substVec_fvarVec
#print axioms substVec_boundIdentity
#print axioms substVec_liftedFree
#print axioms closedBaseVector_readback
#print axioms closedStepVector_readback
end M6.PA.FoundationPAeqCode

