import PA194PAeqAllsTranslation
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeqBind
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeqTermBlueprint
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem induction_image_scoped (param p : V) (h : InductionUnivR p) :
    ∃ m b k : V,
      formulaCode param p = qqAlls b m ∧
      IsSemiformula PA194PAeq.language m b ∧
      shift PA194PAeq.language b = b ∧
      IsSemiformula PA194PAeq.language 1 k ∧
      subst PA194PAeq.language (fvarVec m) b = inductionBodyAddOne k := by
  obtain ⟨m, hm, b, hbnd, hp, hb, hshift, hbv, k, hkbound, hk, hbody⟩ := h
  have hbs : IsSemiformula ℒₒᵣ m b := ⟨hb, le_of_eq hbv⟩
  refine ⟨m, formulaCode param b, formulaCode param k, ?_,
    formulaCode_valid param hbs, ?_, formulaCode_valid param hk, ?_⟩
  · rw [hp, formulaCode_qqAlls param b m hb]
  · rw [← formulaCode_shift param hb, hshift]
  · rw [← termVector_fvarVec m, ← formulaCode_subst param hbs (fvarVec_scoped m), hbody,
      formulaCode_indBodyVal param hk]

theorem induction_supplier_reduced (U : Theory PA194PAeq.language) [U.Δ₁]
    (hadd : ∀ m b k : V,
      IsSemiformula PA194PAeq.language m b →
      shift PA194PAeq.language b = b →
      IsSemiformula PA194PAeq.language 1 k →
      subst PA194PAeq.language (fvarVec m) b = inductionBodyAddOne k →
      Provable U (qqAlls b m)) :
    ∀ p : V, InductionUnivR p → Provable U (formulaCode 0 p) := by
  intro p hp
  obtain ⟨m,b,k, heq, hb, hshift, hk, hbody⟩ := induction_image_scoped 0 p hp
  rw [heq]
  exact hadd m b k hb hshift hk hbody

#print axioms induction_image_scoped
#print axioms induction_supplier_reduced
end generic
end PA194PAeqBind
