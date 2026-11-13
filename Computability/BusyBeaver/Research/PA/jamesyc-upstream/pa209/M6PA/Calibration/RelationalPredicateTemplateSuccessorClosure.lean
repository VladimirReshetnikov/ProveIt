module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateSuccessorClosureSyntax
public import M6PA.Calibration.RelationalClosedCertificateSupply
@[expose] public section
namespace M6.PA.RelationalPredicateTemplate.Successor
open FFL FFL.FirstOrder
open FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCheckerBlueprint RelationalSource.Numeric
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem closure_value (P : V) {f : V}
    (hf : IsSemitermVec RelationalSource.language (len f) 0 f) :
    formulaValue closure P 0 f=(⌜ForwardRelational.successorClosed⌝ : V) := by
  rw [closure_lift]
  exact formulaValue_closed _ RelationalClosedCertificate.successor_closed P hf

theorem closure_certificate (P f g lo z : V)
    (hf : IsSemitermVec RelationalSource.language (len f) 0 f)
    (hc : FormulaCovered 0 g lo z (formulaValue closure P 0 f)) :
    ∃code,verifyValue code=translate (parameters 0 g lo z) (formulaValue closure P 0 f)+1 := by
  rw [closure_value P hf] at hc ⊢
  exact RelationalClosedCertificate.successor_certificate g lo z hc

#print axioms closure_value
#print axioms closure_certificate
end M6.PA.RelationalPredicateTemplate.Successor

