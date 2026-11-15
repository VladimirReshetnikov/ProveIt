import PA194PAeqBindBShift
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeqBind
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem bindQVec {n k v w : V}
    (hv : IsSemitermVec PA194PAeq.language n k v)
    (hw : IsSemitermVec PA194PAeq.language n (k+1) w)
    (h : ∀ i < n, bindTerm k v.[i] = w.[i]) :
    ∀ i < n+1, bindTerm (k+1) (qVec PA194PAeq.language v).[i] = (qVec PA194PAeq.language w).[i] := by
  intro i hi
  rcases zero_or_succ i with rfl | ⟨j,rfl⟩
  · simp [qVec]
  · have hj : j<n := by simpa using hi
    have hjv : j<len v := by simpa [hv.lh] using hj
    have hjw : j<len w := by simpa [hw.lh] using hj
    simp only [qVec,nth_adjoin_succ,hv.lh,hw.lh,nth_termBShiftVec hv.isUTerm hj,nth_termBShiftVec hw.isUTerm hj]
    rw [termBindBShift (hv.nth hj).isUTerm k (hv.nth hj), h j hj]
#print axioms bindQVec
end PA194PAeqBind
