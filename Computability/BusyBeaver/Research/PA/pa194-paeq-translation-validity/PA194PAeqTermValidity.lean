import PA194PAeqLanguage
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194PAeqTermBlueprint
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem functionCode_valid {n k f w : V} (hf : (ℒₒᵣ).IsFunc k f)
    (hw : IsSemitermVec PA194PAeq.language k n w) :
    IsSemiterm PA194PAeq.language n (functionCode k f w) := by
  rcases (original_functions k f).mp hf with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · simp [functionCode,zeroCode,PA194PAeq.source_functions]
  · simp [functionCode,oneCode,zeroCode,PA194PAeq.source_functions]
  · simpa [functionCode,PA194PAeq.source_functions] using hw
  · simpa [functionCode,PA194PAeq.source_functions] using hw

theorem termCode_valid {n t : V} (ht : IsSemiterm ℒₒᵣ n t) :
    IsSemiterm PA194PAeq.language n (termCode t) := by
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
    IsSemitermVec PA194PAeq.language k n (termVector k ts) := by
  apply IsSemitermVec.iff.mpr
  refine ⟨?_,?_⟩
  · simp [hs.isUTerm]
  · intro i hi
    rw [termVector_nth hs.isUTerm hi]
    exact termCode_valid (hs.nth hi)

#print axioms functionCode_valid
#print axioms termCode_valid
#print axioms termVector_valid
end PA194PAeqTermBlueprint

