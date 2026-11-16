module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAeqCodeFormulaSupport
@[expose] public section
/-! Transfer the exact source induction witness, retaining its canonical support
count. The resulting body is additive; it is not a successor induction axiom. -/
namespace M6.PA.FoundationPAeqCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem source_fvarVec_valid (m n : V) : IsSemitermVec ℒₒᵣ m n (fvarVec m) := by
  apply IsSemitermVec.iff.mpr
  refine ⟨by simp,?_⟩
  intro i hi
  rw [nth_fvarVec m i hi]
  simp

theorem termVector_fvarVec (m : V) : termVector m (fvarVec m)=fvarVec m := by
  have hv := (source_fvarVec_valid m 0).isUTerm
  apply nth_ext' m (termVector_length hv) (by simp)
  intro i hi
  rw [termVector_nth hv hi,nth_fvarVec m i hi,termCode_fvar]

variable [V↓[ℒₒᵣ] ⊧* theory]
theorem translated_induction_witness {c : V} (hc : InductionR (fun _=>True) c) :
    ∃ m b k : V,
      formulaCode 0 c=qqAlls b m ∧ IsUFormula Presentation.language b ∧
      shift Presentation.language b=b ∧ bv Presentation.language b=m ∧
      IsSemiformula Presentation.language 1 k ∧
      subst Presentation.language (fvarVec m) b=targetAdditiveBody k := by
  rcases hc with ⟨m,_,b,_,rfl,hb,hshift,hbv,k,_,hk,_,hbody⟩
  refine ⟨m,formulaCode 0 b,formulaCode 0 k,formulaCode_alls 0 m hb,
    formulaCode_isUFormula 0 hb,?_,?_,formulaCode_valid 0 hk,?_⟩
  · rw [←formulaCode_shift 0 hb,hshift]
  · rw [formulaCode_bv 0 hb,hbv]
  · have hbm : IsSemiformula ℒₒᵣ m b := ⟨hb,by rw [hbv]⟩
    rw [←termVector_fvarVec m,←formulaCode_subst 0 hbm (source_fvarVec_valid m 0),
      hbody,formulaCode_indBody hk]

#print axioms source_fvarVec_valid
#print axioms termVector_fvarVec
#print axioms translated_induction_witness
end M6.PA.FoundationPAeqCode

