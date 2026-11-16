import PA194PAeqInductionClosureReduction
import PA194PAeqClosureClosed
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeqBind
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem termShift_freeBound_zero {t : V} (ht : IsUTerm PA194PAeq.language t) :
    termShift PA194PAeq.language t = t → termFreeBound t = 0 := by
  haveI : 𝚺₁-Function₁ (termFreeBound : V → V) := termFreeBound_defined.to_definable
  have hdef : 𝚺₁-Predicate (fun t : V => termShift PA194PAeq.language t = t → termFreeBound t = 0) := by definability
  apply IsUTerm.induction 𝚺 hdef ?_ ?_ ?_ t ht
  · intro i hs; simp
  · intro i hs
    simp only [termShift_fvar, qqFvar_inj] at hs
    have := lt_add_one i
    exact (ne_of_gt this hs).elim
  · intro ar f v hf hv ih hs
    have hvec : termShiftVec PA194PAeq.language ar v = v := by
      simpa [termShift_func hf hv] using hs
    rw [termFreeBound_func hf hv]
    apply le_antisymm _ zero_le
    apply listMaxss_le
    intro i hi
    have hi' : i < ar := by simpa [termFreeBoundVec_len hv] using hi
    have he : termShift PA194PAeq.language (v.[i]) = v.[i] := by
      have h := congrArg (fun w : V => w.[i]) hvec
      simpa [nth_termShiftVec hv hi'] using h
    rw [termFreeBoundVec_nth hv hi', ih i hi' he]
theorem atomShift_freeBound_zero {ar v : V} (hv : IsUTermVec PA194PAeq.language ar v)
    (hs : termShiftVec PA194PAeq.language ar v = v) : atomFreeBound ar v = 0 := by
  unfold atomFreeBound
  apply le_antisymm _ zero_le
  apply listMaxss_le
  intro i hi
  have hi' : i < ar := by simpa [termFreeBoundVec_len hv] using hi
  have he : termShift PA194PAeq.language (v.[i]) = v.[i] := by
    have h := congrArg (fun w : V => w.[i]) hs
    simpa [nth_termShiftVec hv hi'] using h
  rw [termFreeBoundVec_nth hv hi', termShift_freeBound_zero (hv.nth hi') he]

theorem formulaShift_freeBound_zero {p : V} (hp : IsUFormula PA194PAeq.language p) :
    shift PA194PAeq.language p = p → formulaFreeBound p = 0 := by
  haveI : 𝚺₁-Function₁ (formulaFreeBound : V → V) := formulaFreeBound_defined.to_definable
  have hdef : 𝚺₁-Predicate (fun p : V => shift PA194PAeq.language p = p → formulaFreeBound p = 0) := by definability
  apply IsUFormula.ISigma1.sigma1_succ_induction hdef ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · intro ar r v hr hv hs
    have he : termShiftVec PA194PAeq.language ar v = v := by simpa [shift_rel hr hv] using hs
    simpa [formulaFreeBound_rel hr hv] using atomShift_freeBound_zero hv he
  · intro ar r v hr hv hs
    have he : termShiftVec PA194PAeq.language ar v = v := by simpa [shift_nrel hr hv] using hs
    simpa [formulaFreeBound_nrel hr hv] using atomShift_freeBound_zero hv he
  · intro hs; simp
  · intro hs; simp
  · intro a b ha hb iha ihb hs
    have he : shift PA194PAeq.language a = a ∧ shift PA194PAeq.language b = b := by
      simpa [shift_and ha hb] using hs
    simp [formulaFreeBound_and ha hb, iha he.1, ihb he.2]
  · intro a b ha hb iha ihb hs
    have he : shift PA194PAeq.language a = a ∧ shift PA194PAeq.language b = b := by
      simpa [shift_or ha hb] using hs
    simp [formulaFreeBound_or ha hb, iha he.1, ihb he.2]
  · intro a ha ih hs
    have he : shift PA194PAeq.language a = a := by simpa [shift_all ha] using hs
    simp [formulaFreeBound_all ha,ih he]
  · intro a ha ih hs
    have he : shift PA194PAeq.language a = a := by simpa [shift_exs ha] using hs
    simp [formulaFreeBound_exs ha,ih he]
#print axioms formulaShift_freeBound_zero
#print axioms termShift_freeBound_zero
end PA194PAeqBind
