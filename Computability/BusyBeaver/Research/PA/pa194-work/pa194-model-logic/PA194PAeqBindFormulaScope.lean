import PA194PAeqBindFormula
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeqBind
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem bindTermVec_scope {k n ar v : V} (hk : k≤n) (hv : IsSemitermVec PA194PAeq.language ar n v) :
    IsSemitermVec PA194PAeq.language ar (n+1) (bindTermVec k ar v) := by
  have hlen : ar = len (bindTermVec k ar v) := by
    simpa [bindTermVec] using (termConstruction.resultVec_lh PA194PAeq.language ![k] hv.isUTermVec).symm
  have hc : ∀ i < ar, IsSemiterm PA194PAeq.language (n+1) (nth (bindTermVec k ar v) i) := by
    intro i hi
    rw [bindTermVec_nth hv.isUTermVec hi]
    exact bindTerm_scope (hv.nth hi).isUTerm k n hk (hv.nth hi)
  constructor
  · exact ⟨hlen,fun i hi => (hc i hi).isUTerm⟩
  · intro i hi
    exact (hc i hi).bv

def FormulaBindScope (p : V) : Prop := ∀ k n, k≤n → IsSemiformula PA194PAeq.language n p →
  IsSemiformula PA194PAeq.language (n+1) (bindFormula k p)
theorem FormulaBindScope_definable : 𝚷₁-Predicate (FormulaBindScope : V → Prop) := by
  haveI : 𝚺₁-Function₂ (bindFormula : V → V → V) := bindFormula_defined.to_definable
  unfold FormulaBindScope
  definability

theorem bindFormula_scope {p : V} (hp : IsUFormula PA194PAeq.language p) : FormulaBindScope p := by
  apply IsUFormula.ISigma1.pi1_succ_induction FormulaBindScope_definable ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · intro ar r v hr hv k n hk hs
    have hv' := ((IsSemiformula.rel).mp hs).2
    rw [bindFormula_rel hr hv,IsSemiformula.rel]
    exact ⟨hr,bindTermVec_scope hk hv'⟩
  · intro ar r v hr hv k n hk hs
    have hv' := ((IsSemiformula.nrel).mp hs).2
    rw [bindFormula_nrel hr hv,IsSemiformula.nrel]
    exact ⟨hr,bindTermVec_scope hk hv'⟩
  · intro k n hk hs
    simp
  · intro k n hk hs
    simp
  · intro p q hp hq ihp ihq k n hk hs
    have h := (IsSemiformula.and).mp hs
    rw [bindFormula_and hp hq,IsSemiformula.and]
    exact ⟨ihp k n hk h.1,ihq k n hk h.2⟩
  · intro p q hp hq ihp ihq k n hk hs
    have h := (IsSemiformula.or).mp hs
    rw [bindFormula_or hp hq,IsSemiformula.or]
    exact ⟨ihp k n hk h.1,ihq k n hk h.2⟩
  · intro p hp ih k n hk hs
    have h := (IsSemiformula.all).mp hs
    rw [bindFormula_all hp,IsSemiformula.all]
    exact ih (k+1) (n+1) (by simpa [add_comm] using add_le_add_right hk (1 : V)) h
  · intro p hp ih k n hk hs
    have h := (IsSemiformula.exs).mp hs
    rw [bindFormula_exs hp,IsSemiformula.exs]
    exact ih (k+1) (n+1) (by simpa [add_comm] using add_le_add_right hk (1 : V)) h
#print axioms bindTermVec_scope
#print axioms FormulaBindScope_definable
#print axioms bindFormula_scope
end generic
end PA194PAeqBind
