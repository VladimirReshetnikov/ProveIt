module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAeqCodeTerm
@[expose] public section

/-! Target arity preservation for arbitrary model-valued source terms.
The induction is Foundation's definable syntax induction, not Nat induction. -/
namespace M6.PA.FoundationPAeqCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem functionCode_valid {n k f w : V} (hf : (ℒₒᵣ).IsFunc k f)
    (hw : IsSemitermVec Presentation.language k n w) :
    IsSemiterm Presentation.language n (functionCode k f w) := by
  rcases (original_functions k f).mp hf with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · simp [functionCode,zeroCode,Presentation.source_functions]
  · simp [functionCode,oneCode,zeroCode,Presentation.source_functions]
  · simpa [functionCode,Presentation.source_functions] using hw
  · simpa [functionCode,Presentation.source_functions] using hw

theorem termCode_valid {n t : V} (ht : IsSemiterm ℒₒᵣ n t) :
    IsSemiterm Presentation.language n (termCode t) := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro i hi; simpa using hi
  · intro i; simp
  · intro k f ts hf hs ih
    rw [termCode_func hf hs.isUTerm]
    apply functionCode_valid hf
    apply IsSemitermVec.iff.mpr
    refine ⟨?_,?_⟩
    · simp [hs.isUTerm]
    · intro i hi
      rw [termVector_nth hs.isUTerm hi]
      exact ih i hi

theorem termVector_valid {n k ts : V} (hs : IsSemitermVec ℒₒᵣ k n ts) :
    IsSemitermVec Presentation.language k n (termVector k ts) := by
  apply IsSemitermVec.iff.mpr
  refine ⟨?_,?_⟩
  · simp [hs.isUTerm]
  · intro i hi
    rw [termVector_nth hs.isUTerm hi]
    exact termCode_valid (hs.nth hi)

#print axioms functionCode_valid
#print axioms termCode_valid
#print axioms termVector_valid
end M6.PA.FoundationPAeqCode

