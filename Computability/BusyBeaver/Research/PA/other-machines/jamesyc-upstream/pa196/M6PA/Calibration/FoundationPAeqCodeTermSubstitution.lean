module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAeqCodeTermShift
@[expose] public section
namespace M6.PA.FoundationPAeqCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem termCode_subst {k n w t : V} (hw : IsSemitermVec ℒₒᵣ k n w) (ht : IsSemiterm ℒₒᵣ k t) :
    termCode (termSubst ℒₒᵣ w t)=
      termSubst Presentation.language (termVector k w) (termCode t) := by
  apply IsSemiterm.induction 𝚺 (P:=fun t => termCode (termSubst ℒₒᵣ w t)=
    termSubst Presentation.language (termVector k w) (termCode t)) ?_ ?_ ?_ ?_ t ht
  · definability
  · intro i hi
    simp only [termSubst_bvar,termCode_bvar]
    exact (termVector_nth hw.isUTerm hi).symm
  · intro i; simp
  · intro a f ts hf hs ih
    have hv := termVector_isUTermVec hs.isUTerm
    have he : termVector a (termSubstVec ℒₒᵣ a w ts)=
        termSubstVec Presentation.language a (termVector k w) (termVector a ts) := by
      apply nth_ext' a (termVector_length (hw.termSubstVec hs).isUTerm) (by simp [hv])
      intro i hi
      rw [termVector_nth (hw.termSubstVec hs).isUTerm hi,nth_termSubstVec hs.isUTerm hi,
        nth_termSubstVec hv hi,termVector_nth hs.isUTerm hi]
      exact ih i hi
    rw [termSubst_func hf hs.isUTerm,termCode_func hf (hw.termSubstVec hs).isUTerm,
      termCode_func hf hs.isUTerm,he]
    rcases (original_functions a f).mp hf with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · simp [functionCode,zeroCode,Presentation.source_functions]
    · simp [functionCode,oneCode,zeroCode,Presentation.source_functions]
    · simp [functionCode,termSubst_func,Presentation.source_functions,hv]
    · simp [functionCode,termSubst_func,Presentation.source_functions,hv]

theorem termVector_subst {a k n w ts : V} (hw : IsSemitermVec ℒₒᵣ k n w)
    (ht : IsSemitermVec ℒₒᵣ a k ts) :
    termVector a (termSubstVec ℒₒᵣ a w ts)=
      termSubstVec Presentation.language a (termVector k w) (termVector a ts) := by
  have hv := termVector_isUTermVec ht.isUTerm
  apply nth_ext' a (termVector_length (hw.termSubstVec ht).isUTerm) (by simp [hv])
  intro i hi
  rw [termVector_nth (hw.termSubstVec ht).isUTerm hi,nth_termSubstVec ht.isUTerm hi,
    nth_termSubstVec hv hi,termVector_nth ht.isUTerm hi]
  exact termCode_subst hw (ht.nth hi)

#print axioms termCode_subst
#print axioms termVector_subst
end M6.PA.FoundationPAeqCode
