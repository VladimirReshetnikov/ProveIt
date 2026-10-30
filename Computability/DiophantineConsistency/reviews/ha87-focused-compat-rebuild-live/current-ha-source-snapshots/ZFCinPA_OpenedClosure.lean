import ZFCinPA.ModelCodedBindFree

set_option autoImplicit false

/-! Language-generic bookkeeping for opening universally closed formulas. -/

namespace LeanProofs.ZFCinPA.OpenedClosure

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

lemma shift_qqAlls {body : V} (hb : IsUFormula L body) (count : V) :
    shift L (qqAlls body count) = qqAlls (shift L body) count := by
  induction count using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ count ih =>
    rw [qqAlls_succ, shift_all (isUFormula_qqAlls.mpr hb), ih, qqAlls_succ]

/-- Freeing the first binder of an opened closure opens one more variable. -/
theorem free_subst_qVec_fvarVec {k B : V} (hB : IsSemiformula L (k + 1) B)
    (hs : shift L B = B) :
    free L (subst L (qVec L (fvarVec k)) B) = subst L (fvarVec (k + 1)) B := by
  have hf := ModelCodedBindFree.fvarVec_isTermVec (L := L) (V := V) k
  have hw : IsSemitermVec L (k + 1) 1 (qVec L (fvarVec k)) := by simpa using hf.qVec
  rw [free, substs1, shift_substs hB hw, hs,
    substs_substs hB (show IsSemitermVec L 1 0 ?[^&0] by simp) hw.termShiftVec]
  congr 1
  apply nth_ext' (k + 1)
  · simp [hw.termShiftVec.isUTerm]
  · simp
  · intro i hi
    rw [nth_termSubstVec hw.termShiftVec.isUTerm hi, nth_termShiftVec hw.isUTerm hi,
      nth_fvarVec _ _ hi]
    rcases zero_or_succ i with rfl | ⟨j, rfl⟩
    · simp [Bootstrapping.qVec]
    · have hj : j < k := by simpa using hi
      simp only [Bootstrapping.qVec, hf.lh, nth_adjoin_succ]
      rw [nth_termBShiftVec hf.isUTerm hj, nth_fvarVec _ _ hj]
      simp

end LeanProofs.ZFCinPA.OpenedClosure
