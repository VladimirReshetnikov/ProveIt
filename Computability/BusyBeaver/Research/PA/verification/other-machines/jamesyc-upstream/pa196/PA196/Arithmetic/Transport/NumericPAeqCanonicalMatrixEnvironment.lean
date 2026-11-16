module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqCanonicalMatrixSupport
public import PA196.Arithmetic.Transport.NumericPAeqFormulaRealization
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.NumericPAeqCanonicalMatrix

namespace PA196.Arithmetic.Transport.NumericPAeqCanonicalMatrix
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqFormula NumericPAeqFormulaRealization
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem canonical_environment {m B b:V} (hB:IsSemitermVec RelationalSource.language m 0 B)
    (hb:IsSemiformula Presentation.language m b) (hs:FreeSupported 0 b):
    FormulaEnvironment m 0 0 B B (fvarVec m) b := by
  refine ⟨by simp,?_,hB,hb,fvarVector_valid m 0,?_,?_⟩
  · simpa [hB.lh] using hB
  · exact ⟨hs.1,le_trans hs.2 (by simp)⟩
  · intro i hi
    simpa [←hB.lh] using fvarVector_supported hi
#print axioms canonical_environment
end PA196.Arithmetic.Transport.NumericPAeqCanonicalMatrix

