module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqInductionSuccessorComparison
public import PA196.Arithmetic.Transport.NumericPAeqInductionStepOpening
public import PA196.Arithmetic.Transport.NumericPAeqInductionStepTemplateCertificate
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqInductionInterpretation
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqFormula NumericPAeqFormulaLogical NumericPAeqValueTotality
open NumericPAeqInductionStepTemplate NumericPAeqInductionStepOpening
open NumericPAeqTerm (targetShiftTerms targetShiftTerms_valid targetShiftTerms_length)
open RelationalSource.Numeric PA196.Arithmetic.Checker
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem uniform_successor_certificate {f p:V} (hf:IsSemitermVec language (len f) 0 f)
    (hp:IsSemiformula Presentation.language 1 p) (hs:FreeSupported (len f) p)
    (native lo z:V) (hc:FormulaCovered 0 native lo z (uniformCode (freeDomain f) (property f p) (successorProperty f p))):
    ∃code,verifyValue code=translate (RelationalSource.Numeric.parameters 0 native lo z)
      (uniformCode (freeDomain f) (property f p) (successorProperty f p))+1 := by
  have hF := freeDomain_valid hf
  have hP := property_valid hf hp hs
  have hR := successorProperty_valid hf hp hs
  apply double_universal_certificate _ native lo z (uniformMatrixCode_valid hF hP hR) hc
  intro native lo z hc
  rw [uniformMatrixCode_double_open hF hP hR] at hc ⊢
  have hf1 : IsSemitermVec language (len (targetShiftTerms f)) 0 (targetShiftTerms f) := by simpa [targetShiftTerms_length hf] using targetShiftTerms_valid hf
  have hs1 : FreeSupported (len (targetShiftTerms f)) p := by simpa [targetShiftTerms_length hf] using hs
  have hf2 : IsSemitermVec language (len (targetShiftTerms (targetShiftTerms f))) 0 (targetShiftTerms (targetShiftTerms f)) := by simpa [targetShiftTerms_length hf1] using targetShiftTerms_valid hf1
  have hs2 : FreeSupported (len (targetShiftTerms (targetShiftTerms f))) p := by simpa [targetShiftTerms_length hf1] using hs1
  simp only [openedCode,freeDomain_shift hf,freeDomain_shift hf1,
    property_shift hf hp hs,property_shift hf1 hp hs1,
    successorProperty_shift hf hp hs,successorProperty_shift hf1 hp hs1] at hc ⊢
  exact successor_comparison_certificate hf2 hp hs2 (by simp) (by simp) native lo z hc
noncomputable def stepCompatibilityCode (f p:V):V :=
  imp language (qqAnd (freeDomain f) (sourceStepCode (property f p) (successorProperty f p))) (targetStepCode (property f p))
theorem step_compatibility_certificate {f p:V} (hf:IsSemitermVec language (len f) 0 f)
    (hp:IsSemiformula Presentation.language 1 p) (hs:FreeSupported (len f) p)
    (native lo z:V) (hc:FormulaCovered 0 native lo z (stepCompatibilityCode f p)):
    ∃code,verifyValue code=translate (RelationalSource.Numeric.parameters 0 native lo z) (stepCompatibilityCode f p)+1 := by
  have hv := stepCode_valid (freeDomain_valid hf) (property_valid hf hp hs) (successorProperty_valid hf hp hs)
  apply source_certificate_mp (uniformCode (freeDomain f) (property f p) (successorProperty f p)) (stepCompatibilityCode f p) native lo z
    (IsSemiformula.imp.mp hv).1 (IsSemiformula.imp.mp hv).2 hc
  · exact uniform_successor_certificate hf hp hs
  · intro native lo z hc
    exact step_requested_certificate _ _ _ native lo z (freeDomain_valid hf) (property_valid hf hp hs) (successorProperty_valid hf hp hs) hc
#print axioms uniform_successor_certificate
#print axioms step_compatibility_certificate
end PA196.Arithmetic.Transport.NumericPAeqInductionInterpretation

