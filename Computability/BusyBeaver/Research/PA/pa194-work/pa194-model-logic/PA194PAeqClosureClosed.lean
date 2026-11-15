import PA194PAeqClosureFreeBound
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeqBind
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem termFreeBound_zero_shift {t : V} (ht : IsUTerm PA194PAeq.language t) :
    termFreeBound t = 0 → termShift PA194PAeq.language t = t := by
  haveI : 𝚺₁-Function₁ (termFreeBound : V → V) := termFreeBound_defined.to_definable
  have hdef : 𝚺₁-Predicate (fun t : V => termFreeBound t = 0 → termShift PA194PAeq.language t = t) := by definability
  apply IsUTerm.induction 𝚺 hdef ?_ ?_ ?_ t ht
  · intro i h; simp
  · intro i h; simp at h
  · intro ar f v hf hv ih hz
    have hmax : listMax (termFreeBoundVec ar v) = 0 := by simpa [termFreeBound_func hf hv] using hz
    have hvec : termShiftVec PA194PAeq.language ar v = v := by
      apply nth_ext' ar (len_termShiftVec hv) hv.lh.symm
      intro i hi
      rw [nth_termShiftVec hv hi]
      apply ih i hi
      apply le_antisymm _ zero_le
      have hle : nth (termFreeBoundVec ar v) i ≤ listMax (termFreeBoundVec ar v) := nth_le_listMax (by simpa [termFreeBoundVec_len hv] using hi)
      simpa [termFreeBoundVec_nth hv hi,hmax] using hle
    simp [termShift_func hf hv,hvec]

theorem atomFreeBound_zero_shift {ar v : V} (hv : IsUTermVec PA194PAeq.language ar v)
    (hz : atomFreeBound ar v = 0) : termShiftVec PA194PAeq.language ar v = v := by
  apply nth_ext' ar (len_termShiftVec hv) hv.lh.symm
  intro i hi
  rw [nth_termShiftVec hv hi]
  apply termFreeBound_zero_shift (hv.2 i hi)
  apply le_antisymm _ zero_le
  have hle : nth (termFreeBoundVec ar v) i ≤ listMax (termFreeBoundVec ar v) := nth_le_listMax (by simpa [termFreeBoundVec_len hv] using hi)
  simpa [termFreeBoundVec_nth hv hi,atomFreeBound] using hle.trans (le_of_eq hz)

theorem formulaFreeBound_zero_shift {p : V} (hp : IsUFormula PA194PAeq.language p) :
    formulaFreeBound p = 0 → shift PA194PAeq.language p = p := by
  haveI : 𝚺₁-Function₁ (formulaFreeBound : V → V) := formulaFreeBound_defined.to_definable
  have hdef : 𝚺₁-Predicate (fun p : V => formulaFreeBound p = 0 → shift PA194PAeq.language p = p) := by definability
  apply IsUFormula.ISigma1.sigma1_succ_induction hdef ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · intro ar r v hr hv hz
    have hzero : atomFreeBound ar v = 0 := by simpa [formulaFreeBound_rel hr hv] using hz
    simp [shift_rel hr hv,atomFreeBound_zero_shift hv hzero]
  · intro ar r v hr hv hz
    have hzero : atomFreeBound ar v = 0 := by simpa [formulaFreeBound_nrel hr hv] using hz
    simp [shift_nrel hr hv,atomFreeBound_zero_shift hv hzero]
  · intro hz; simp
  · intro hz; simp
  · intro a b ha hb iha ihb hz
    have hmax : max (formulaFreeBound a) (formulaFreeBound b) = 0 := by simpa [formulaFreeBound_and ha hb] using hz
    have hza : formulaFreeBound a = 0 := le_antisymm (by simpa [hmax] using le_max_left (formulaFreeBound a) (formulaFreeBound b)) zero_le
    have hzb : formulaFreeBound b = 0 := le_antisymm (by simpa [hmax] using le_max_right (formulaFreeBound a) (formulaFreeBound b)) zero_le
    simp [shift_and ha hb,iha hza,ihb hzb]
  · intro a b ha hb iha ihb hz
    have hmax : max (formulaFreeBound a) (formulaFreeBound b) = 0 := by simpa [formulaFreeBound_or ha hb] using hz
    have hza : formulaFreeBound a = 0 := le_antisymm (by simpa [hmax] using le_max_left (formulaFreeBound a) (formulaFreeBound b)) zero_le
    have hzb : formulaFreeBound b = 0 := le_antisymm (by simpa [hmax] using le_max_right (formulaFreeBound a) (formulaFreeBound b)) zero_le
    simp [shift_or ha hb,iha hza,ihb hzb]
  · intro a ha ih hz
    simp [shift_all ha,ih (by simpa [formulaFreeBound_all ha] using hz)]
  · intro a ha ih hz
    simp [shift_exs ha,ih (by simpa [formulaFreeBound_exs ha] using hz)]

theorem close_closed (n : V) {p : V} (hp : IsSemiformula PA194PAeq.language 0 p)
    (hn : formulaFreeBound p ≤ n) :
    IsSemiformula PA194PAeq.language 0 (close n p) ∧ shift PA194PAeq.language (close n p) = close n p := by
  have hscope := close_scope n hp
  have hzero : formulaFreeBound (close n p) = 0 := by
    rw [close_freeBound n hp]
    exact tsub_eq_zero_iff_le.mpr hn
  exact ⟨hscope,formulaFreeBound_zero_shift hscope.isUFormula hzero⟩
#print axioms termFreeBound_zero_shift
#print axioms formulaFreeBound_zero_shift
#print axioms close_closed
end generic
end PA194PAeqBind
