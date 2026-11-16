module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateOrdinalCode
@[expose] public section
namespace M6.PA.RelationalPredicateTemplate.Ordinal
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCheckerBlueprint RelationalSource.Numeric
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language
attribute [local irreducible] proofFreeBound inductionDerivation inductionStatement formulaValue
variable [V↓[ℒₒᵣ] ⊧* theory]
theorem ordinalInduction_certificate_exists {P : V} (hP : IsSemiformula L 1 P) :
    ∃g lo z code : V,FormulaCovered 0 g lo z (ordinalInductionCode P) ∧
      verifyValue code=translate (parameters 0 g lo z) (ordinalInductionCode P)+1 := by
  have hh := ordinal_induction_certificate hP (inductionTermEnvironment_valid (V:=V))
    (inductionTermEnvironment_bound (V:=V))
  simpa only [ordinalInductionCode,formulaValue_closed_environment inductionStatement inductionStatement_closed
    P 0 inductionTermEnvironment 0] using hh
#print axioms ordinalInduction_certificate_exists
end M6.PA.RelationalPredicateTemplate.Ordinal

