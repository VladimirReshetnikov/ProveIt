import ZFCinPA.ModelCodedShiftCancellation
set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA.ModelCodedShiftCancellation
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]
#print axioms LeanProofs.ZFCinPA.ModelCodedShiftCancellation.unaryView_free
#print axioms LeanProofs.ZFCinPA.ModelCodedShiftCancellation.unaryView_subst_fvar
#print axioms LeanProofs.ZFCinPA.ModelCodedShiftCancellation.cancelShift
#print axioms LeanProofs.ZFCinPA.ModelCodedShiftCancellation.provable_shift_iff
#print axioms LeanProofs.ZFCinPA.ModelCodedShiftCancellation.cancelShiftN
#print axioms LeanProofs.ZFCinPA.ModelCodedShiftCancellation.provable_shiftN_iff
example (p : Formula V L) : (unaryView p).free = p.shift := unaryView_free p
example (p : Formula V L) (x : V) : (unaryView p).subst ![Semiterm.fvar x] = p :=
  unaryView_subst_fvar p x
example (T : InternalTheory V L) (p : Formula V L) (h : T ⊢! p.shift) : T ⊢! p :=
  cancelShift T p h
example (T : InternalTheory V L) (p : Formula V L) : (T ⊢ p.shift) ↔ (T ⊢ p) :=
  provable_shift_iff T p
example (T : InternalTheory V L) (p : Formula V L) (n : Nat) (h : T ⊢! shiftN n p) : T ⊢! p :=
  cancelShiftN T p n h
example (T : InternalTheory V L) (p : Formula V L) (n : Nat) :
    (T ⊢ shiftN n p) ↔ (T ⊢ p) := provable_shiftN_iff T p n
example (T : InternalTheory V L) (p : Formula V L) (h : T ⊢! p) : T ⊢! p :=
  cancelShiftN T p 0 h
example (T : InternalTheory V L) (p : Formula V L) (h : T ⊢! p.shift.shift) : T ⊢! p :=
  cancelShiftN T p 2 h
example (p : Formula V L) : (unaryView p).val = p.val := rfl
