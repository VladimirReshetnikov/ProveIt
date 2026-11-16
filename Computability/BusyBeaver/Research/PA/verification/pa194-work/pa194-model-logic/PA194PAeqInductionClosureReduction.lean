import PA194PAeqGeneralizeClosure
import PA194PAeqInductionSupplierReduction
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.InductionReopen
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeqBind PA194PAeqTermBlueprint
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local instance] PA194PAeqBind.ordinaryPAeq_delta

/-- Precise syntax identity still needed to identify the classifier's parameter closure. -/
def ClosureReconstruction : Prop := ∀ m b : V,
  IsSemiformula language m b → shift language b = b →
  close m (subst language (fvarVec m) b) = qqAlls b m

theorem induction_supplier_of_closure_reconstruction
    (hclose : ClosureReconstruction (V := V)) :
    ∀ p : V, InductionUnivR p → Provable ordinaryPAeq (formulaCode 0 p) := by
  intro p hp
  obtain ⟨m,b,k,heq,hb,hshift,hk,hbody⟩ := induction_image_scoped 0 p hp
  have hscope : IsSemiformula language 0 (subst language (fvarVec m) b) := by
    have hv : IsSemitermVec language m 0 (fvarVec m) := by
      rw [IsSemitermVec.iff]
      refine ⟨len_fvarVec m, ?_⟩
      intro i hi
      rw [nth_fvarVec m i hi]
      simp
    exact hb.subst hv
  have hbodyPr : Provable ordinaryPAeq (subst language (fvarVec m) b) := by
    rw [hbody]
    exact addOneBody_unconditional hk
  have hclosed := close_iterated_provable m _ hscope hbodyPr
  rw [hclose m b hb hshift] at hclosed
  simpa only [heq] using hclosed
#print axioms induction_supplier_of_closure_reconstruction
end PA194PAeq.InductionReopen
