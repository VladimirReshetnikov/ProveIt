module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAeqCodeClosedInductionReadback
@[expose] public section
/-! A genuinely canonical target induction axiom for any shift-fixed coded
matrix. The closure count is its actual support, never an added vacuous count. -/
namespace M6.PA.FoundationPAeqCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "PAeq" => Presentation.language
noncomputable def matrixParameterCount (q : V) : V := bv PAeq (qqAll q)
noncomputable def canonicalSuccessorBody (q : V) : V := closedSuccessorBody (matrixParameterCount q) q
noncomputable def canonicalSuccessorAxiom (q : V) : V := qqAlls (canonicalSuccessorBody q) (matrixParameterCount q)

theorem matrixParameterCount_valid {q : V} (hq : IsUFormula PAeq q) :
    IsSemiformula PAeq (matrixParameterCount q+1) q := by
  have ha : IsUFormula PAeq (qqAll q) := by simp [hq]
  exact IsSemiformula.all.mp ha.isSemiformula

theorem canonicalSuccessorBody_bv {q : V} (hq : IsUFormula PAeq q) :
    bv PAeq (canonicalSuccessorBody q)=matrixParameterCount q := by
  have hv := matrixParameterCount_valid hq
  have hb := hv.subst (closedBaseVector_valid (matrixParameterCount q))
  have ht := hv.subst (closedStepVector_valid (matrixParameterCount q))
  apply le_antisymm (closedSuccessorBody_valid hv).bv_le
  have hc : IsUFormula PAeq (qqAll q) := by simp [hq]
  have hleft : IsUFormula PAeq (neg PAeq (qqAll (qqOr (neg PAeq q)
      (subst PAeq (closedStepVector (matrixParameterCount q)) q)))) := by
    simp [hq,ht.isUFormula]
  have hright := IsUFormula.or.mpr ⟨hleft,hc⟩
  change bv PAeq (qqAll q) ≤ bv PAeq (closedSuccessorBody (matrixParameterCount q) q)
  simp only [closedSuccessorBody,imp]
  rw [bv_or hb.isUFormula.neg hright,bv_or hleft hc]
  exact (le_max_right _ _).trans (le_max_right _ _)

theorem canonicalSuccessorAxiom_recognized {q : V} (hq : IsUFormula PAeq q)
    (hs : shift PAeq q=q) : targetInductionR (canonicalSuccessorAxiom q) := by
  let m := matrixParameterCount q
  have hv := matrixParameterCount_valid hq
  have hb := closedSuccessorBody_valid hv
  have hw : IsSemitermVec PAeq (m+1) 1 (qVec PAeq (fvarVec m)) := by
    simpa using (target_fvarVec_valid m 0).qVec
  refine ⟨m,index_le_qqAlls _ _,canonicalSuccessorBody q,le_qqAlls _ _,rfl,
    hb.isUFormula,closedSuccessorBody_shift hv hs,canonicalSuccessorBody_bv hq,
    subst PAeq (qVec PAeq (fvarVec m)) q,?_,hv.subst hw,?_⟩
  · rw [show subst PAeq (fvarVec m) (canonicalSuccessorBody q)=
        targetIndBody (subst PAeq (qVec PAeq (fvarVec m)) q) from closedSuccessorBody_readback hv]
    exact le_targetIndBody _
  · exact closedSuccessorBody_readback hv

theorem canonicalSuccessorAxiom_mem {q : V} (hq : IsUFormula PAeq q)
    (hs : shift PAeq q=q) : canonicalSuccessorAxiom q∈Presentation.ordinaryPAeq.Δ₁Class :=
  (ordinaryPAeq_mem_iff _).mpr (Or.inr (canonicalSuccessorAxiom_recognized hq hs))

#print axioms matrixParameterCount_valid
#print axioms canonicalSuccessorBody_bv
#print axioms canonicalSuccessorAxiom_recognized
#print axioms canonicalSuccessorAxiom_mem
end M6.PA.FoundationPAeqCode

