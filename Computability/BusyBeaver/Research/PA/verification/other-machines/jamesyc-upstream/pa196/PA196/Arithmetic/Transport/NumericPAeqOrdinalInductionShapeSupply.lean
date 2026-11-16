module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqOrdinalInductionShape
public import PA196.Arithmetic.Transport.RelationalPredicateTemplateOrdinalRequested
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqOrdinalInductionShape
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open PA196.Arithmetic.Checker RelationalSource.Numeric
open RelationalPredicateTemplate.Ordinal
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
theorem inductionCode_requested_certificate (P g lo z:V)
    (hP:IsSemiformula RelationalSource.language 1 P)
    (hc:FormulaCovered 0 g lo z (inductionCode P)):
    ∃code,verifyValue code=translate (parameters 0 g lo z) (inductionCode P)+1 := by
  rw [←ordinalInductionCode_shape hP] at hc ⊢
  exact ordinalInduction_requested_certificate P g lo z hP hc
#print axioms inductionCode_requested_certificate
end PA196.Arithmetic.Transport.NumericPAeqOrdinalInductionShape

