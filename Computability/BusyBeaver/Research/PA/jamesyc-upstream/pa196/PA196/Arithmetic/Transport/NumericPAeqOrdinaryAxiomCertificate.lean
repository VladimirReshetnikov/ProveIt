module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqInductionAxiomCertificate
public import PA196.Arithmetic.Transport.PAInterpretedFixedNumericClass
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqInductionInterpretation
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqFormula RelationalSource.Numeric PA196.Arithmetic.Checker
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem ordinary_axiom_requested_certificate {q f:V}
    (hq:q∈Presentation.ordinaryPAeq.Δ₁Class)
    (hf:IsSemitermVec RelationalSource.language (len f) 0 f)
    (native lo z:V)
    (hc:FormulaCovered 0 native lo z (formulaSyntax (NumericPAeqFormula.parameters 0 f) q)):
    ∃code,verifyValue code=translate (RelationalSource.Numeric.parameters 0 native lo z)
      (formulaSyntax (NumericPAeqFormula.parameters 0 f) q)+1 := by
  rcases (FoundationPAeqCode.ordinaryPAeq_mem_iff q).mp hq with hfixed|hind
  · exact ForwardRelational.numericFixedClass_certificate q (NumericPAeqFormula.parameters 0 f) native lo z ((FoundationPAeqCode.targetFixed_mem_iff q).mpr hfixed)
      (by simp [ParametersValid,hf]) hc
  · exact induction_axiom_requested_certificate hind f native lo z hc
#print axioms ordinary_axiom_requested_certificate
end PA196.Arithmetic.Transport.NumericPAeqInductionInterpretation

