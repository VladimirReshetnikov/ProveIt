import ZFCinPA.ModelCodedBinderAbsorption

set_option autoImplicit false

/-!
Cancel free-variable shifts in an actual internal proof by generalizing an
unused bound slot and specializing it again. Formula codes and free parameters
remain arbitrary internal elements. The iteration index here is externally
finite, for use with a fixed proof template's shift buffer.
-/
namespace LeanProofs.ZFCinPA.ModelCodedShiftCancellation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA.ModelCodedBinderAbsorption
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

noncomputable def unaryView (p : Formula V L) : Semiformula V L 1 :=
  ⟨p.val,⟨p.isSemiformula.isUFormula,le_trans p.isSemiformula.bv_le (by simp)⟩⟩

lemma unaryView_free (p : Formula V L) : (unaryView p).free = p.shift := by
  apply Semiformula.ext
  exact free_formula p.isSemiformula

lemma unaryView_subst_fvar (p : Formula V L) (x : V) :
    (unaryView p).subst ![Semiterm.fvar x] = p := by
  apply Semiformula.ext
  change substs1 L (^&x) p.val = p.val
  exact substs1_formula p.isSemiformula x

noncomputable def cancelShift (T : InternalTheory V L) (p : Formula V L)
    (h : T ⊢! p.shift) : T ⊢! p := by
  rw [←unaryView_free p] at h
  have hh := TProof.specialize (TProof.all h) (Semiterm.fvar (0 : V))
  simpa only [unaryView_subst_fvar] using hh

theorem provable_shift_iff (T : InternalTheory V L) (p : Formula V L) :
    (T ⊢ p.shift) ↔ (T ⊢ p) :=
  ⟨fun h => ⟨cancelShift T p h.get⟩,fun h => ⟨TProof.shift h.get⟩⟩

noncomputable def shiftN : Nat → Formula V L → Formula V L
  | 0,p => p
  | n+1,p => (shiftN n p).shift

noncomputable def cancelShiftN (T : InternalTheory V L) (p : Formula V L) :
    (n : Nat) → (T ⊢! shiftN n p) → (T ⊢! p)
  | 0,h => h
  | n+1,h => cancelShiftN T p n (cancelShift T (shiftN n p) h)

theorem provable_shiftN_iff (T : InternalTheory V L) (p : Formula V L) (n : Nat) :
    (T ⊢ shiftN n p) ↔ (T ⊢ p) := by
  induction n with
  | zero => rfl
  | succ n ih => exact (provable_shift_iff T (shiftN n p)).trans ih

end LeanProofs.ZFCinPA.ModelCodedShiftCancellation
