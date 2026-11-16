module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqUniversalContextCertificate
public import PA196.Arithmetic.Transport.NumericPAeqUniversalContextOpening
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqUniversalContext
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqInductionInterpretation NumericPAeqUniversalContextOpening
open RelationalSource.Numeric PA196.Arithmetic.Checker
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
/-- The actual source free-body form of the contextual universal rule. -/
theorem universal_source_context_requested_certificate {f p S:V}
    (hf:IsSemitermVec language (len f) 0 f) (hp:IsSemiformula Presentation.language 1 p)
    (hs:NumericPAeqFormula.FreeSupported (len f) p) (hS:IsFormula language S)
    (native lo z:V) (hc:FormulaCovered 0 native lo z (contextRuleCode f p S))
    (child:∀g l z,FormulaCovered 0 g l z (imp language (freeDomain (eigenEnvironment f))
      (qqOr (NumericPAeqFormula.formulaSyntax (NumericPAeqFormula.parameters 0 (eigenEnvironment f))
        (free Presentation.language p)) (shift language S)))→
      ∃code,verifyValue code=translate (parameters 0 g l z) (imp language (freeDomain (eigenEnvironment f))
        (qqOr (NumericPAeqFormula.formulaSyntax (NumericPAeqFormula.parameters 0 (eigenEnvironment f))
          (free Presentation.language p)) (shift language S)))+1):
    ∃code,verifyValue code=translate (parameters 0 native lo z) (contextRuleCode f p S)+1 :=by
  apply universal_context_requested_certificate hf hp hs hS native lo z hc
  intro g l z hc
  have child' := child g l z
  rw [source_free_property hf hp hs] at child'
  exact child' hc
#print axioms universal_source_context_requested_certificate
end PA196.Arithmetic.Transport.NumericPAeqUniversalContext

