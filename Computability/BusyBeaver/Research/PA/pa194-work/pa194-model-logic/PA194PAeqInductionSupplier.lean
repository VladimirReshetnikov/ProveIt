import PA194PAeqBindSubstFormula
import PA194PAeqClosureOneStep
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.InductionReopen
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeqBind PA194PAeqTermBlueprint
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local instance] PA194PAeqBind.ordinaryPAeq_delta

theorem fvarVec_scoped_target (n : V) : IsSemitermVec language n 0 (fvarVec n) := by
  rw [IsSemitermVec.iff]
  refine ⟨len_fvarVec n, ?_⟩
  intro i hi
  rw [nth_fvarVec n i hi]
  simp

theorem fvarVec_bind_relation (m : V) : ∀ i < m+1,
    bindTerm 0 (fvarVec (m+1)).[i] = (qVec language (fvarVec m)).[i] := by
  intro i hi
  rcases zero_or_succ i with rfl | ⟨j,rfl⟩
  · rw [nth_fvarVec (m+1) 0 (by simp)]
    simp [bindFree,qVec]
  · have hj : j<m := by simpa using hi
    rw [nth_fvarVec (m+1) (j+1) hi]
    have hf := fvarVec_scoped_target (V := V) m
    simp [bindFree,qVec,nth_termBShiftVec hf.isUTerm hj,nth_fvarVec m j hj,hf.lh]

theorem bindSubstReconstruction : BindSubstReconstruction (V := V) := by
  intro m b hb hs
  have hv := fvarVec_scoped_target (V := V) (m+1)
  have hw := (fvarVec_scoped_target (V := V) m).qVec
  exact formulaBindSubst hb.isUFormula (m+1) 0 _ _ hb hv (by simpa using hw)
    (fvarVec_bind_relation m) (formulaShift_freeBound_zero hb.isUFormula hs)

theorem induction_supplier : ∀ p : V, InductionUnivR p →
    Provable ordinaryPAeq (formulaCode 0 p) :=
  induction_supplier_of_bindSubst bindSubstReconstruction
#print axioms fvarVec_bind_relation
#print axioms bindSubstReconstruction
#print axioms induction_supplier
end PA194PAeq.InductionReopen
