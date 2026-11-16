module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateOrdinalSupport
public import M6PA.Calibration.RelationalPredicateTemplateClosedEnvironment
@[expose] public section
/-! Explicit numerical output of the unary-hole ordinal-induction template.
The empty template free environment does not erase free parameters of P. -/
namespace M6.PA.RelationalPredicateTemplate.Ordinal
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCheckerBlueprint RelationalSource.Numeric
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language

noncomputable def ordinalInductionCode (P : V) : V := formulaValue inductionStatement P 0 0
theorem ordinalInduction_valid {P : V} (hP : IsSemiformula L 1 P) :
    IsFormula L (ordinalInductionCode P) := by
  apply formulaValue_isSemiformula inductionStatement hP (show EnvironmentsValid (0:V) 0 0 0 from ⟨by simp,by simp⟩)
  intro i hi
  simp [Semiformula.FVar?,inductionStatement_closed] at hi

#print axioms ordinalInduction_valid
end M6.PA.RelationalPredicateTemplate.Ordinal

