module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAeqCodeSubstitutionInverse
@[expose] public section
/-! Recover a closed matrix from the final universal conclusion of an additive
induction body. No claim that this alone fixes its exact parameter support. -/
namespace M6.PA.FoundationPAeqCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem target_fvarVec_valid (m n : V) :
    IsSemitermVec Presentation.language m n (fvarVec m) := by
  apply IsSemitermVec.iff.mpr
  refine ⟨by simp,?_⟩
  intro i hi
  rw [nth_fvarVec m i hi]
  simp

theorem additive_matrix_witness {m b k : V}
    (hb : IsSemiformula Presentation.language m b)
    (hshift : shift Presentation.language b=b)
    (hbody : subst Presentation.language (fvarVec m) b=targetAdditiveBody k) :
    ∃ a s q : V,
      b=qqOr a (qqOr s (qqAll q)) ∧
      IsSemiformula Presentation.language m a ∧
      IsSemiformula Presentation.language m s ∧
      IsSemiformula Presentation.language (m+1) q ∧
      shift Presentation.language q=q ∧
      subst Presentation.language (qVec Presentation.language (fvarVec m)) q=k := by
  have hw := target_fvarVec_valid m 0
  unfold targetAdditiveBody imp at hbody
  obtain ⟨a,d,rfl,ha,hd,_,hrest⟩ := subst_or_inverse hb hw hbody
  obtain ⟨s,e,rfl,hs,he,_,hlast⟩ := subst_or_inverse hd hw hrest
  obtain ⟨q,rfl,hq,hqbody⟩ := subst_all_inverse he hw hlast
  refine ⟨a,s,q,rfl,ha,hs,hq,?_,hqbody⟩
  simp only [shift_or ha.isUFormula hd.isUFormula,
    shift_or hs.isUFormula he.isUFormula,shift_all hq.isUFormula,
    qqOr_inj,qqAll_inj] at hshift
  exact hshift.2.2

#print axioms target_fvarVec_valid
#print axioms additive_matrix_witness
end M6.PA.FoundationPAeqCode

