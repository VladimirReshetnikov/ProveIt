import ZFCinPA.ModelCodedFreeRenaming

/-!
Exact syntax connection to the checked named binder: reopening its new bound
slot with free label zero after a free-label SHIFT is the two-counter renaming
at level/offset zero. This is not yet the proof transport needed for GEN.
-/
namespace LeanProofs.ZFCinPA.ModelCodedRenamingBindOne
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA.ModelCodedSpecialization
open LeanProofs.ZFCinPA.ModelCodedBindOne
open LeanProofs.ZFCinPA.ModelCodedFreeRenaming
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

lemma termBindOneAt_free {depth term : V} (ht : IsSemiterm L depth term) :
    ∀ chosen : V,
    termSubst L (qVecIter L depth (^&0 ∷ 0))
      (termShift L (termBindOneAt L chosen depth term)) =
        termRename L chosen 0 0 term := by
  apply IsSemiterm.induction 𝚷 ?_ ?_ ?_ ?_ term ht
  · definability
  · intro z hz chosen
    rw [termBindOneAt_bvar,termShift_bvar,termSubst_bvar,termRename_bvar]
    exact (qVecIter_free_spec depth 0).1 z hz
  · intro x chosen
    classical
    by_cases h : x = chosen
    · rw [h,termBindOneAt_chosen,termShift_bvar,termSubst_bvar,
        (qVecIter_free_spec depth 0).2,termRename_fvar]
      simp [renameIndex]
    · rw [termBindOneAt_other chosen depth x h,termShift_fvar,
        termSubst_fvar,termRename_fvar]
      simp [renameIndex,h]
  · intro arity f terms hf hv ih chosen
    rw [termBindOneAt_func chosen depth hf hv.isUTerm,
      termShift_func hf (termBindOneVecAt_isUTerm chosen depth hv.isUTerm),
      termSubst_func hf (termBindOneVecAt_isUTerm chosen depth hv.isUTerm).termShiftVec,
      termRename_func chosen 0 0 hf hv.isUTerm]
    apply congrArg (fun args => ^func arity f args)
    apply nth_ext' arity
    · simp [termBindOneVecAt_isUTerm chosen depth hv.isUTerm]
    · simp [hv.isUTerm]
    · intro i hi
      rw [nth_termSubstVec
          (termBindOneVecAt_isUTerm chosen depth hv.isUTerm).termShiftVec hi,
        nth_termShiftVec (termBindOneVecAt_isUTerm chosen depth hv.isUTerm) hi,
        nth_termBindOneVecAt chosen depth hv.isUTerm hi,
        nth_termRenameVec chosen 0 0 hv.isUTerm hi]
      exact ih i hi chosen

lemma termBindOneVecAt_free {depth arity terms : V}
    (ht : IsSemitermVec L arity depth terms) (chosen : V) :
    termSubstVec L arity (qVecIter L depth (^&0 ∷ 0))
      (termShiftVec L arity (termBindOneVecAt L chosen depth arity terms)) =
        termRenameVec L chosen 0 0 arity terms := by
  apply nth_ext' arity
  · simp [termBindOneVecAt_isUTerm chosen depth ht.isUTerm]
  · simp [ht.isUTerm]
  · intro i hi
    rw [nth_termSubstVec (termBindOneVecAt_isUTerm chosen depth ht.isUTerm).termShiftVec hi,
      nth_termShiftVec (termBindOneVecAt_isUTerm chosen depth ht.isUTerm) hi,
      nth_termBindOneVecAt chosen depth ht.isUTerm hi,
      nth_termRenameVec chosen 0 0 ht.isUTerm hi]
    exact termBindOneAt_free (ht.nth hi) chosen

lemma bindOneAt_free {depth p : V} (hp : IsSemiformula L depth p) :
    ∀ chosen : V,
    subst L (qVecIter L depth (^&0 ∷ 0)) (shift L (bindOneAt L chosen depth p)) =
      rename L chosen 0 0 p := by
  apply IsSemiformula.pi1_structural_induction (P := fun depth p =>
    ∀ chosen : V,
    subst L (qVecIter L depth (^&0 ∷ 0)) (shift L (bindOneAt L chosen depth p)) =
      rename L chosen 0 0 p)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro depth arity R terms hR ht chosen
    rw [bindOneAt_rel chosen depth hR ht.isUTerm,
      shift_rel hR (termBindOneVecAt_isUTerm chosen depth ht.isUTerm),
      substs_rel hR (termBindOneVecAt_isUTerm chosen depth ht.isUTerm).termShiftVec,
      termBindOneVecAt_free ht chosen,rename_rel chosen 0 0 hR ht.isUTerm]
  · intro depth arity R terms hR ht chosen
    rw [bindOneAt_nrel chosen depth hR ht.isUTerm,
      shift_nrel hR (termBindOneVecAt_isUTerm chosen depth ht.isUTerm),
      substs_nrel hR (termBindOneVecAt_isUTerm chosen depth ht.isUTerm).termShiftVec,
      termBindOneVecAt_free ht chosen,rename_nrel chosen 0 0 hR ht.isUTerm]
  · intro depth chosen; simp
  · intro depth chosen; simp
  · intro depth p q hp hq ihp ihq chosen
    rw [bindOneAt_and chosen depth hp.isUFormula hq.isUFormula,
      shift_and (bindOneAt_isSemiformula hp chosen).isUFormula
        (bindOneAt_isSemiformula hq chosen).isUFormula,
      substs_and (bindOneAt_isSemiformula hp chosen).shift.isUFormula
        (bindOneAt_isSemiformula hq chosen).shift.isUFormula,
      ihp chosen,ihq chosen,rename_and chosen 0 0 hp.isUFormula hq.isUFormula]
  · intro depth p q hp hq ihp ihq chosen
    rw [bindOneAt_or chosen depth hp.isUFormula hq.isUFormula,
      shift_or (bindOneAt_isSemiformula hp chosen).isUFormula
        (bindOneAt_isSemiformula hq chosen).isUFormula,
      substs_or (bindOneAt_isSemiformula hp chosen).shift.isUFormula
        (bindOneAt_isSemiformula hq chosen).shift.isUFormula,
      ihp chosen,ihq chosen,rename_or chosen 0 0 hp.isUFormula hq.isUFormula]
  · intro depth p hp ih chosen
    rw [bindOneAt_all chosen depth hp.isUFormula,
      shift_all (bindOneAt_isSemiformula hp chosen).isUFormula,
      substs_all (bindOneAt_isSemiformula hp chosen).shift.isUFormula,
      ←qVecIter_succ,ih chosen,rename_all chosen 0 0 hp.isUFormula]
  · intro depth p hp ih chosen
    rw [bindOneAt_exs chosen depth hp.isUFormula,
      shift_exs (bindOneAt_isSemiformula hp chosen).isUFormula,
      substs_ex (bindOneAt_isSemiformula hp chosen).shift.isUFormula,
      ←qVecIter_succ,ih chosen,rename_exs chosen 0 0 hp.isUFormula]

/-- The literal ALL premise needed for `namedAll`, for all internal formulas. -/
theorem free_bindOneAt {p : V} (hp : IsFormula L p) (chosen : V) :
    free L (bindOneAt L chosen 0 p) = rename L chosen 0 0 p := by
  simpa [free,substs1] using bindOneAt_free hp chosen

end LeanProofs.ZFCinPA.ModelCodedRenamingBindOne
