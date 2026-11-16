module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqSupportedValueCoherenceSyntax
public import M6PA.Calibration.NumericPAeqValueCoherenceZeroCertificate
public import M6PA.Calibration.NumericPAeqValueCertificateComposition
@[expose] public section
namespace M6.PA.NumericPAeqSupportedValueCoherence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm NumericPAeqValueCoherence ActualCheckerBlueprint
open NumericPAeqSupportedValueTotality
open ActualCertificateConstructors.Dominated ActualCertificateEquivalence
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem coherence_zero_certificate {s b c f g:V} (h:SupportedCoherenceEnvironment s b c f g (qqFunc 0 0 0))
    (native lo z:V) (hc:RelationalSource.Numeric.FormulaCovered 0 native lo z (coherenceCode s b c f g (qqFunc 0 0 0))) :
    ∃code,verifyValue code=RelationalSource.Numeric.translate (RelationalSource.Numeric.parameters 0 native lo z)
      (coherenceCode s b c f g (qqFunc 0 0 0))+1 := by
  let q := comparisonCode b c f g (qqFunc (0:V) 0 0)
  let goal := coherenceCode s b c f g (qqFunc (0:V) 0 0)
  let d := max q goal
  have he := RelationalSource.Numeric.padded_proofEnvironment d native lo z hc.1.1
  have hq := comparisonCode_valid h
  have cq : RelationalSource.Numeric.FormulaCovered 0 (RelationalSource.Numeric.padEnvironment native d) lo (z+lo+d) q :=
    he.coverage hq (le_max_left _ _)
  let param := RelationalSource.Numeric.parameters 0 (RelationalSource.Numeric.padEnvironment native d) lo (z+lo+d)
  obtain ⟨code,hcode⟩ := zeroComparison_requested_certificate _ lo (z+lo+d) (by simpa [comparison_zero,q] using cq)
  have hcode : verifyValue code=RelationalSource.Numeric.translate param q+1 := by
    simpa [param,q,comparison_zero] using hcode
  obtain ⟨_,back,_,hback⟩ := RelationalSource.Numeric.translate_imp_certificates param
    (coherenceInput s b c f g) q (coherenceInput_valid h).isUFormula hq.isUFormula
  let arrow := (⟨code,hcode⟩ : Certificate (RelationalSource.Numeric.translate param q)).mp
    (k (RelationalSource.Numeric.translate param q) (RelationalSource.Numeric.translate param (coherenceInput s b c f g)))
  let out := arrow.mp ⟨back,hback⟩
  exact RelationalSource.Numeric.padded_proof_certificate_readback goal native lo z d out.code hc out.accepted

#print axioms coherence_zero_certificate
end M6.PA.NumericPAeqSupportedValueCoherence
