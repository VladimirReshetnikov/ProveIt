import PA196InductionBodyCounterexample
import PA196InductionBvCounterexample

/-! The negative induction recognizer bound, with only the shift-graph
counterexample bound remaining explicit. -/
set_option autoImplicit false
namespace PA196InductionNegativeShiftConditional
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAWitnessCalculus
  PA196InductionNegativeConditional
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem wb_negative (hshift : WB M shiftCounterexample) : WB M (∼chUniv.pi.val) :=
  PA196InductionNegativeConditional.wb_negative hshift
    PA196InductionBvCounterexample.wb_bvCounterexample
    PA196InductionBodyCounterexample.wb_bodyCounterexample

#print axioms wb_negative
end PA196InductionNegativeShiftConditional
