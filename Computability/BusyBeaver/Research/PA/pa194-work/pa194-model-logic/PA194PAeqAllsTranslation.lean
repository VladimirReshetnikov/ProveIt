import PA194PAeqArithmeticInduction
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeqBind
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeqTermBlueprint
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem formulaCode_qqAlls (param p n : V) (hp : IsUFormula ℒₒᵣ p) :
    formulaCode param (qqAlls p n) = qqAlls (formulaCode param p) n := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih =>
    rw [qqAlls_succ, qqAlls_succ,
      formulaCode_all _ _ (isUFormula_qqAlls.mpr hp), ih]
theorem fvarVec_scoped (n : V) : IsSemitermVec ℒₒᵣ n 0 (fvarVec n) := by
  rw [IsSemitermVec.iff]
  refine ⟨len_fvarVec n, ?_⟩
  intro i hi
  rw [nth_fvarVec n i hi]
  simp

theorem termVector_fvarVec (n : V) : termVector n (fvarVec n) = fvarVec n := by
  have h := fvarVec_scoped n
  apply nth_ext (by simp [h.isUTerm])
  intro i hi
  have hi' : i < n := by simpa [h.isUTerm] using hi
  rw [termVector_nth h.isUTerm hi', nth_fvarVec n i hi', termCode_fvar]

theorem induction_image_shape (param p : V) (h : InductionUnivR p) :
    ∃ m b k : V,
      formulaCode param p = qqAlls b m ∧
      IsUFormula PA194PAeq.language b ∧
      shift PA194PAeq.language b = b ∧
      IsSemiformula PA194PAeq.language 1 k ∧
      subst PA194PAeq.language (fvarVec m) b = inductionBodyAddOne k := by
  obtain ⟨m, hm, b, hbnd, hp, hb, hshift, hbv, k, hkbound, hk, hbody⟩ := h
  have hbs : IsSemiformula ℒₒᵣ m b := ⟨hb, le_of_eq hbv⟩
  refine ⟨m, formulaCode param b, formulaCode param k, ?_,
    formulaCode_isUFormula param hb, ?_, formulaCode_valid param hk, ?_⟩
  · rw [hp, formulaCode_qqAlls param b m hb]
  · rw [← formulaCode_shift param hb, hshift]
  · rw [← termVector_fvarVec m, ← formulaCode_subst param hbs (fvarVec_scoped m), hbody,
      formulaCode_indBodyVal param hk]

#print axioms induction_image_shape
#print axioms fvarVec_scoped
#print axioms termVector_fvarVec
#print axioms formulaCode_qqAlls
end generic
end PA194PAeqBind
