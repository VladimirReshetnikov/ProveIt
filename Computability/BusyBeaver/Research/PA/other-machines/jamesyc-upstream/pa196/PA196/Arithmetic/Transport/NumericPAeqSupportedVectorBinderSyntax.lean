module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqSupportedVectorRealizationSyntax
public import M6PA.Calibration.NumericPAeqTermSupportedSourceBShift
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqSupportedVectorRealization
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm NumericPAeqValueRealizationGuard
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
/-! Source binder lifting compensates qVec by adjoining the SAME actual target
term to the two bound environments. Target free parameters are not erased. -/
theorem vector_qVec_entry_zero (b f a w x:V):
    M6.PA.NumericPAeqValueRealizationGuard.entry (x∷b) f (qVec Presentation.language w) (x∷a) 0=variableValue x x := by
  simp [M6.PA.NumericPAeqValueRealizationGuard.entry,qVec,valueSyntax_bvar,parameters]
theorem vector_qVec_entry_succ {s r n b f a w x i:V}
    (hb:IsSemitermVec language r n b) (hf:IsSemitermVec language (len f) n f)
    (ha:IsSemitermVec language s n a) (hw:IsSemitermVec Presentation.language s r w)
    (hs:∀j<s,FreeSupported (len f) (nth w j)) (hx:IsSemiterm language n x) (hi:i<s):
    M6.PA.NumericPAeqValueRealizationGuard.entry (x∷b) f (qVec Presentation.language w) (x∷a) (i+1)=M6.PA.NumericPAeqValueRealizationGuard.entry b f w a i := by
  simp only [M6.PA.NumericPAeqValueRealizationGuard.entry,qVec,nth_adjoin_succ]
  rw [hw.lh,nth_termBShiftVec hw.isUTerm hi]
  exact valueSyntax_supported_sourceBShift_parameters hb hf (hw.nth hi) (hs i hi) hx (ha.nth hi)
#print axioms vector_qVec_entry_zero
#print axioms vector_qVec_entry_succ
end PA196.Arithmetic.Transport.NumericPAeqSupportedVectorRealization
