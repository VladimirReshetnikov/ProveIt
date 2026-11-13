module
public import NthData
public import TemplateNthBridge
@[expose] public section
namespace PalomarPA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
/-- Closed exact syntax certificate. There is no semantic placeholder or
nthDef-equality assumption in this theorem. -/
theorem nthFormula_toFoundation :
 nthFormula.toFoundation = (nthDef : ArithmeticSemisentence 3) := constructed_nth_to

theorem nthFormula_exact :
 nthFormula = Formula.fromFoundation (nthDef : ArithmeticSemisentence 3) := by
 rw [←nthFormula_toFoundation,Formula.from_to]
#print axioms nthFormula_toFoundation
end PalomarPA
