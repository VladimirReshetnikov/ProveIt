import PA194PAeqFreeBoundFormula
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeqBind
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem max_pred (a b : V) : max (a-1) (b-1) = max a b - 1 := by
  rcases le_total a b with hab | hba
  · rw [max_eq_right hab,max_eq_right (tsub_le_tsub_right hab 1)]
  · rw [max_eq_left hba,max_eq_left (tsub_le_tsub_right hba 1)]
theorem bindTermVec_uterm {k ar v : V} (hv : IsUTermVec PA194PAeq.language ar v) :
    IsUTermVec PA194PAeq.language ar (bindTermVec k ar v) := by
  have hlen : ar = len (bindTermVec k ar v) := by
    simpa [bindTermVec] using (termConstruction.resultVec_lh PA194PAeq.language ![k] hv).symm
  refine ⟨hlen,?_⟩
  intro i hi
  rw [bindTermVec_nth hv hi]
  exact bindTerm_uterm (hv.2 i hi)
theorem bindFormula_uformula {k p : V} (hp : IsUFormula PA194PAeq.language p) :
    IsUFormula PA194PAeq.language (bindFormula k p) := by
  let n := max k (bv PA194PAeq.language p)
  have hs : IsSemiformula PA194PAeq.language n p := ⟨hp,le_max_right _ _⟩
  exact (bindFormula_scope hp k n (le_max_left _ _) hs).isUFormula

theorem atomFreeBound_bind {k ar v : V} (hv : IsUTermVec PA194PAeq.language ar v) :
    atomFreeBound ar (bindTermVec k ar v) = atomFreeBound ar v - 1 := by
  have hvb := bindTermVec_uterm (k := k) hv
  unfold atomFreeBound
  apply listMax_pred
  · simp [termFreeBoundVec_len hv,termFreeBoundVec_len hvb]
  · intro i hi
    have hi' : i < ar := by simpa [termFreeBoundVec_len hv] using hi
    rw [termFreeBoundVec_nth hvb hi',bindTermVec_nth hv hi',termFreeBoundVec_nth hv hi']
    exact termFreeBound_bind (hv.2 i hi') k

def FormulaFreeBind (p : V) : Prop := ∀ k, formulaFreeBound (bindFormula k p) = formulaFreeBound p - 1
theorem FormulaFreeBind_definable : 𝚷₁-Predicate (FormulaFreeBind : V → Prop) := by
  haveI : 𝚺₁-Function₂ (bindFormula : V → V → V) := bindFormula_defined.to_definable
  haveI : 𝚺₁-Function₁ (formulaFreeBound : V → V) := formulaFreeBound_defined.to_definable
  unfold FormulaFreeBind
  definability

theorem formulaFreeBound_bind {p : V} (hp : IsUFormula PA194PAeq.language p) : FormulaFreeBind p := by
  apply IsUFormula.ISigma1.pi1_succ_induction FormulaFreeBind_definable ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · intro ar r v hr hv k
    rw [bindFormula_rel hr hv,formulaFreeBound_rel hr (bindTermVec_uterm hv),formulaFreeBound_rel hr hv,atomFreeBound_bind hv]
  · intro ar r v hr hv k
    rw [bindFormula_nrel hr hv,formulaFreeBound_nrel hr (bindTermVec_uterm hv),formulaFreeBound_nrel hr hv,atomFreeBound_bind hv]
  · intro k; simp
  · intro k; simp
  · intro a b ha hb iha ihb k
    rw [bindFormula_and ha hb,formulaFreeBound_and (bindFormula_uformula ha) (bindFormula_uformula hb),formulaFreeBound_and ha hb,iha k,ihb k,max_pred]
  · intro a b ha hb iha ihb k
    rw [bindFormula_or ha hb,formulaFreeBound_or (bindFormula_uformula ha) (bindFormula_uformula hb),formulaFreeBound_or ha hb,iha k,ihb k,max_pred]
  · intro a ha ih k
    rw [bindFormula_all ha,formulaFreeBound_all (bindFormula_uformula ha),formulaFreeBound_all ha,ih (k+1)]
  · intro a ha ih k
    rw [bindFormula_exs ha,formulaFreeBound_exs (bindFormula_uformula ha),formulaFreeBound_exs ha,ih (k+1)]
#print axioms atomFreeBound_bind
#print axioms formulaFreeBound_bind
end generic
end PA194PAeqBind
