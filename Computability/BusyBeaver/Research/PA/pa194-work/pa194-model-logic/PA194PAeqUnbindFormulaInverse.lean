import PA194PAeqUnbindFormula
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeqBind
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem unbindTermVec_bind {k ar v : V} (hv : IsSemitermVec PA194PAeq.language ar k v) :
    unbindTermVec k ar (bindTermVec k ar v) = v := by
  have hvb := bindTermVec_uterm (k := k) hv.isUTermVec
  apply nth_ext' ar (by simpa [unbindTermVec] using (unbindTermConstruction.resultVec_lh PA194PAeq.language ![k] hvb)) hv.lh
  intro i hi
  rw [unbindTermVec_nth hvb hi,bindTermVec_nth hv.isUTermVec hi]
  exact unbindTerm_bind (hv.nth hi).isUTerm k (hv.nth hi)

def FormulaBindInverse (p : V) : Prop := ∀ k, IsSemiformula PA194PAeq.language k p → unbindFormula k (bindFormula k p) = p
theorem FormulaBindInverse_definable : 𝚷₁-Predicate (FormulaBindInverse : V → Prop) := by
  haveI : 𝚺₁-Function₂ (bindFormula : V → V → V) := bindFormula_defined.to_definable
  haveI : 𝚺₁-Function₂ (unbindFormula : V → V → V) := unbindFormula_defined.to_definable
  unfold FormulaBindInverse
  definability
theorem unbindFormula_bind {p : V} (hp : IsUFormula PA194PAeq.language p) : FormulaBindInverse p := by
  apply IsUFormula.ISigma1.pi1_succ_induction FormulaBindInverse_definable ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · intro ar r v hr hv k hs
    have hsv := ((IsSemiformula.rel).mp hs).2
    rw [bindFormula_rel hr hv,unbindFormula_rel hr (bindTermVec_uterm hv),unbindTermVec_bind hsv]
  · intro ar r v hr hv k hs
    have hsv := ((IsSemiformula.nrel).mp hs).2
    rw [bindFormula_nrel hr hv,unbindFormula_nrel hr (bindTermVec_uterm hv),unbindTermVec_bind hsv]
  · intro k hs; simp
  · intro k hs; simp
  · intro a b ha hb iha ihb k hs
    have hs' := (IsSemiformula.and).mp hs
    rw [bindFormula_and ha hb,unbindFormula_and (bindFormula_uformula ha) (bindFormula_uformula hb),iha k hs'.1,ihb k hs'.2]
  · intro a b ha hb iha ihb k hs
    have hs' := (IsSemiformula.or).mp hs
    rw [bindFormula_or ha hb,unbindFormula_or (bindFormula_uformula ha) (bindFormula_uformula hb),iha k hs'.1,ihb k hs'.2]
  · intro a ha ih k hs
    rw [bindFormula_all ha,unbindFormula_all (bindFormula_uformula ha),ih (k+1) ((IsSemiformula.all).mp hs)]
  · intro a ha ih k hs
    rw [bindFormula_exs ha,unbindFormula_exs (bindFormula_uformula ha),ih (k+1) ((IsSemiformula.exs).mp hs)]
#print axioms unbindTermVec_bind
#print axioms unbindFormula_bind
end generic
end PA194PAeqBind
