module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaClosedSupport
public import M6PA.Calibration.NumericPAeqFormulaSupportedSubstitution
@[expose] public section
namespace M6.PA.NumericPAeqCanonicalMatrix
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqFormula
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem fvarVector_valid (m n:V):IsSemitermVec Presentation.language m n (fvarVec m) := by
  apply IsSemitermVec.iff.mpr
  refine ⟨by simp,?_⟩
  intro i hi;rw [nth_fvarVec m i hi];simp
theorem fvarVector_supported {m i:V} (hi:i<m):NumericPAeqTerm.FreeSupported m (nth (fvarVec m) i) := by
  rw [nth_fvarVec m i hi]
  exact ⟨by simp,by simpa only [NumericPAeqTerm.freeBound_fvar] using succ_le_iff_lt.mpr hi⟩
theorem opened_matrix_supported {m b:V} (hb:IsSemiformula Presentation.language m b)
    (hs:FreeSupported 0 b):FreeSupported m (subst Presentation.language (fvarVec m) b) := by
  apply freeSupported_subst hb (fvarVector_valid m 0)
  · exact ⟨hs.1,le_trans hs.2 (by simp)⟩
  · exact fun i hi=>fvarVector_supported hi
theorem induction_property_supported {m b p:V} (hb:IsSemiformula Presentation.language m b)
    (hs:shift Presentation.language b=b)
    (he:subst Presentation.language (fvarVec m) b=FoundationPAeqCode.targetIndBody p):FreeSupported m p := by
  have h:=opened_matrix_supported hb (freeSupported_zero_of_shift_fixed hb.isUFormula hs)
  rw [he] at h
  exact freeSupported_targetIndBody h
#print axioms fvarVector_valid
#print axioms fvarVector_supported
#print axioms opened_matrix_supported
#print axioms induction_property_supported
end M6.PA.NumericPAeqCanonicalMatrix

