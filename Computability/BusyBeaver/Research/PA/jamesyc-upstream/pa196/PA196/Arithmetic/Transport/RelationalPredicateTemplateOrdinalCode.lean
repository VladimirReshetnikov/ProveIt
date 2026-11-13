module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.RelationalPredicateTemplateOrdinalSupport
public import M6PA.Calibration.RelationalPredicateTemplateClosedEnvironment
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.RelationalPredicateTemplate
open M6.PA.RelationalPredicateTemplate.Ordinal

/-! Explicit numerical output of the unary-hole ordinal-induction template.
The empty template free environment does not erase free parameters of P. -/
namespace PA196.Arithmetic.Transport.RelationalPredicateTemplate.Ordinal
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open PA196.Arithmetic.Checker RelationalSource.Numeric
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language

noncomputable def ordinalInductionCode (P : V) : V := formulaValue inductionStatement P 0 0
theorem ordinalInduction_valid {P : V} (hP : IsSemiformula L 1 P) :
    IsFormula L (ordinalInductionCode P) := by
  apply formulaValue_isSemiformula inductionStatement hP (show M6.PA.RelationalPredicateTemplate.EnvironmentsValid (0:V) 0 0 0 from ⟨by simp,by simp⟩)
  intro i hi
  simp [Semiformula.FVar?,inductionStatement_closed] at hi

#print axioms ordinalInduction_valid
end PA196.Arithmetic.Transport.RelationalPredicateTemplate.Ordinal

