module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAeqCodeClosureProofLeaf
@[expose] public section
namespace M6.PA.FoundationPAeqCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "PAeq" => Presentation.language

theorem fvarVec_front (k : V) :
    fvarVec (k+1)=qqFvar 0∷termShiftVec PAeq k (fvarVec k) := by
  have hv := (target_fvarVec_valid k 0).isUTerm
  apply nth_ext' (k+1) (by simp) (by simp [hv])
  intro i hi
  rcases zero_or_succ i with rfl|⟨i,rfl⟩
  · rw [nth_fvarVec (k+1) 0 hi]; simp
  · have hi' : i<k := by simpa using hi
    rw [nth_fvarVec (k+1) (i+1) hi]
    simp [nth_termShiftVec hv hi',nth_fvarVec k i hi']

theorem substVec_shiftedFvar (k w : V) :
    termSubstVec PAeq k w (termShiftVec PAeq k (fvarVec k))=
      termShiftVec PAeq k (fvarVec k) := by
  have hv := (target_fvarVec_valid k 0).isUTerm
  apply nth_ext' k (by simp [hv]) (by simp [hv])
  intro i hi
  rw [nth_termSubstVec (target_fvarVec_valid k 0).termShiftVec.isUTerm hi,
    nth_termShiftVec hv hi,nth_fvarVec k i hi]
  simp

theorem openingSuccVector (k : V) :
    termSubstVec PAeq (k+1) (qqFvar 0∷0)
      (termShiftVec PAeq (k+1) (qVec PAeq (fvarVec k)))=fvarVec (k+1) := by
  have hv := (target_fvarVec_valid k 0).isUTerm
  rw [qVec_fvarVec,termShiftVec_cons (by simp) hv]
  simp only [termShift_bvar]
  rw [termSubstVec_cons (by simp) (target_fvarVec_valid k 0).termShiftVec.isUTerm]
  rw [show termSubst (V:=V) PAeq (qqFvar 0∷0) (qqBvar 0)=qqFvar 0 from by simp,substVec_shiftedFvar]
  exact (fvarVec_front k).symm

theorem free_opening_succ {k b : V} (hb : IsSemiformula PAeq (k+1) b)
    (hs : shift PAeq b=b) :
    Bootstrapping.free PAeq (subst PAeq (qVec PAeq (fvarVec k)) b)=
      subst PAeq (fvarVec (k+1)) b := by
  have hw : IsSemitermVec PAeq (k+1) 1 (qVec PAeq (fvarVec k)) := by
    simpa using (target_fvarVec_valid k 0).qVec
  unfold Bootstrapping.free substs1
  rw [shift_substs hb hw,hs,
    substs_substs hb (show IsSemitermVec PAeq 1 0 (qqFvar 0∷0) from by simp) hw.termShiftVec,
    openingSuccVector]

#print axioms fvarVec_front
#print axioms substVec_shiftedFvar
#print axioms openingSuccVector
#print axioms free_opening_succ
end M6.PA.FoundationPAeqCode

