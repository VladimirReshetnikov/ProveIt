import PA194PAeqUnbindFormulaInverse
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeqBind
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
def BindComplexity (p : V) : Prop := ∀ k, formulaComplexity PA194PAeq.language (bindFormula k p) = formulaComplexity PA194PAeq.language p
theorem BindComplexity_definable : 𝚷₁-Predicate (BindComplexity : V → Prop) := by
  haveI : 𝚺₁-Function₂ (bindFormula : V → V → V) := bindFormula_defined.to_definable
  unfold BindComplexity
  definability
theorem bindFormula_complexity {p : V} (hp : IsUFormula PA194PAeq.language p) : BindComplexity p := by
  apply IsUFormula.ISigma1.pi1_succ_induction BindComplexity_definable ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · intro ar r v hr hv k
    rw [bindFormula_rel hr hv,formulaComplexity_rel hr (bindTermVec_uterm hv),formulaComplexity_rel hr hv]
  · intro ar r v hr hv k
    rw [bindFormula_nrel hr hv,formulaComplexity_nrel hr (bindTermVec_uterm hv),formulaComplexity_nrel hr hv]
  · intro k; simp
  · intro k; simp
  · intro a b ha hb iha ihb k
    rw [bindFormula_and ha hb,formulaComplexity_and (bindFormula_uformula ha) (bindFormula_uformula hb),formulaComplexity_and ha hb,iha k,ihb k]
  · intro a b ha hb iha ihb k
    rw [bindFormula_or ha hb,formulaComplexity_or (bindFormula_uformula ha) (bindFormula_uformula hb),formulaComplexity_or ha hb,iha k,ihb k]
  · intro a ha ih k
    rw [bindFormula_all ha,formulaComplexity_all (bindFormula_uformula ha),formulaComplexity_all ha,ih (k+1)]
  · intro a ha ih k
    rw [bindFormula_exs ha,formulaComplexity_ex (bindFormula_uformula ha),formulaComplexity_ex ha,ih (k+1)]

theorem closeOne_complexity {p : V} (hp : IsSemiformula PA194PAeq.language 0 p) :
    formulaComplexity PA194PAeq.language (closeOne p) = formulaComplexity PA194PAeq.language p + 1 := by
  rw [closeOne,formulaComplexity_all (bindFormula_uformula hp.isUFormula),bindFormula_complexity hp.isUFormula 0]
theorem close_complexity (n : V) {p : V} (hp : IsSemiformula PA194PAeq.language 0 p) :
    formulaComplexity PA194PAeq.language (close n p) = formulaComplexity PA194PAeq.language p + n := by
  haveI : 𝚺₁-Function₂ (close : V → V → V) := close_defined.to_definable
  induction n using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ n ih =>
    rw [close_succ,closeOne_complexity (close_scope n hp),ih]
    simp [add_assoc]

theorem formulaComplexity_le_code {p : V} (hp : IsUFormula PA194PAeq.language p) :
    formulaComplexity PA194PAeq.language p ≤ p := by
  apply IsUFormula.ISigma1.sigma1_succ_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · definability
  · intro k r v hr hv; rw [formulaComplexity_rel hr hv]; exact zero_le
  · intro k r v hr hv; rw [formulaComplexity_nrel hr hv]; exact zero_le
  · simp
  · simp
  · intro a b ha hb iha ihb
    rw [formulaComplexity_and ha hb]
    change max (formulaComplexity PA194PAeq.language a) (formulaComplexity PA194PAeq.language b) + 1 ≤ pair (4 : V) (pair a b) + 1
    apply (add_le_add_iff_right 1).mpr
    apply max_le
    · exact le_trans iha (le_trans (le_pair_left a b) (le_pair_right (4 : V) (pair a b)))
    · exact le_trans ihb (le_trans (le_pair_right a b) (le_pair_right (4 : V) (pair a b)))
  · intro a b ha hb iha ihb
    rw [formulaComplexity_or ha hb]
    change max (formulaComplexity PA194PAeq.language a) (formulaComplexity PA194PAeq.language b) + 1 ≤ pair (5 : V) (pair a b) + 1
    apply (add_le_add_iff_right 1).mpr
    apply max_le
    · exact le_trans iha (le_trans (le_pair_left a b) (le_pair_right (5 : V) (pair a b)))
    · exact le_trans ihb (le_trans (le_pair_right a b) (le_pair_right (5 : V) (pair a b)))
  · intro a ha ih
    rw [formulaComplexity_all ha]
    change formulaComplexity PA194PAeq.language a + 1 ≤ pair (6 : V) a + 1
    exact (add_le_add_iff_right 1).mpr (le_trans ih (le_pair_right (6 : V) a))
  · intro a ha ih
    rw [formulaComplexity_ex ha]
    change formulaComplexity PA194PAeq.language a + 1 ≤ pair (7 : V) a + 1
    exact (add_le_add_iff_right 1).mpr (le_trans ih (le_pair_right (7 : V) a))
theorem close_count_le_code (n : V) {p : V} (hp : IsSemiformula PA194PAeq.language 0 p) :
    n ≤ close n p := by
  have hcode := formulaComplexity_le_code (close_scope n hp).isUFormula
  rw [close_complexity n hp] at hcode
  exact le_trans (by simp) hcode
#print axioms bindFormula_complexity
#print axioms close_complexity
#print axioms formulaComplexity_le_code
#print axioms close_count_le_code
end generic
end PA194PAeqBind
