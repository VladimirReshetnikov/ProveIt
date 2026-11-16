module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqOrdinalInductionShape
public import M6PA.Calibration.RelationalPredicateTemplateOrdinalRequested
@[expose] public section
namespace M6.PA.NumericPAeqOrdinalInductionShape
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCheckerBlueprint RelationalSource.Numeric
open RelationalPredicateTemplate.Ordinal
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem inductionCode_requested_certificate (P g lo z:V)
    (hP:IsSemiformula RelationalSource.language 1 P)
    (hc:FormulaCovered 0 g lo z (inductionCode P)):
    ∃code,verifyValue code=translate (parameters 0 g lo z) (inductionCode P)+1 := by
  rw [←ordinalInductionCode_shape hP] at hc ⊢
  exact ordinalInduction_requested_certificate P g lo z hP hc
#print axioms inductionCode_requested_certificate
end M6.PA.NumericPAeqOrdinalInductionShape

