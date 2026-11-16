module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateOrdinalCanonicalCertificate
public import M6PA.Calibration.RelationalPredicateTemplateNDRequested
@[expose] public section
/-! All-model ordinal-induction template supply at the exact requested native
label environment and reserve. No native free labels are collapsed. -/
namespace M6.PA.RelationalPredicateTemplate.Ordinal
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCheckerBlueprint RelationalSource.Numeric
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
local notation "L" => RelationalSource.language
attribute [local irreducible] proofFreeBound inductionDerivation inductionStatement formulaValue

theorem ordinalInduction_requested_certificate (P g lo z : V)
    (hP : IsSemiformula L 1 P) (hc : FormulaCovered 0 g lo z (ordinalInductionCode P)) :
    ∃code,verifyValue code=translate (parameters 0 g lo z) (ordinalInductionCode P)+1 := by
  have he := formulaValue_closed_environment inductionStatement inductionStatement_closed
    P 0 (inductionTermEnvironment (V:=V)) 0
  have hh : FormulaCovered 0 g lo z
      (formulaValue inductionStatement P 0 (inductionTermEnvironment (V:=V))) := by
    simpa only [he,ordinalInductionCode] using hc
  have h := template_nd_requested_certificate inductionDerivation hP
    (inductionTermEnvironment_valid (V:=V)) (inductionTermEnvironment_bound (V:=V))
    g lo z hh (fun p hp g lo z hcov =>
      induction_axiom_certificate hP (inductionTermEnvironment_valid (V:=V)) p hp g lo z hcov)
  simpa only [he,ordinalInductionCode] using h
#print axioms ordinalInduction_requested_certificate
end M6.PA.RelationalPredicateTemplate.Ordinal

