module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqOrdinalInductionShapeStep
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqOrdinalInductionShape
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateTemplate RelationalPredicateTemplate.Ordinal
open NumericPAeqTerm (domainCode zeroCode successorCode)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language
theorem ordinalInductionCode_shape {P:V} (hP:IsSemiformula L 1 P):
    ordinalInductionCode P=inductionCode P := by
  unfold ordinalInductionCode inductionStatement
  rw [closed_imp_value _ _ hP (show EnvironmentsValid (0:V) 0 0 0 from ⟨by simp,by simp⟩) (by decide)]
  change imp L (qqAnd (formulaValue (inductionBase hole) P 0 0) (formulaValue (inductionStep hole) P 0 0))
    (formulaValue (inductionConclusion hole) P 0 0)=_
  rw [base_value hP (by simp),step_value hP (by simp),conclusion_value hP (by simp)]
  rfl

theorem inductionCode_isFormula {P:V} (hP:IsSemiformula L 1 P):IsFormula L (inductionCode P) := by
  rw [←ordinalInductionCode_shape hP]
  exact ordinalInduction_valid hP
#print axioms base_value
#print axioms step_value
#print axioms conclusion_value
#print axioms ordinalInductionCode_shape
#print axioms inductionCode_isFormula
end PA196.Arithmetic.Transport.NumericPAeqOrdinalInductionShape

