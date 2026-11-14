import PA196InductionPositiveComplete
import PA196InductionNegativeShiftConditional
import PA196InductionShiftCounterexample
import PA196PAAxiomAssembly

/-! Both polarities of Foundation's exact universal-induction recognizer and
both exact PA axiom branches have candidate-PRA witness bounds. -/
set_option autoImplicit false
namespace PA196InductionRecognizerComplete
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAWitnessCalculus
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem wb_negative : WB M (∼chUniv.pi.val) :=
  PA196InductionNegativeShiftConditional.wb_negative PA196InductionShiftCounterexample.wb_shiftCounterexample

theorem good_induction : PA196PAMinusWitness.GoodCh InductionScheme.delta1_univ M := by
  change WB M chUniv.sigma.val ∧ WB M (∼chUniv.pi.val)
  exact ⟨PA196InductionPositiveComplete.wb_positive, wb_negative⟩

theorem good_pa : PA196PAMinusWitness.GoodCh PA_delta1Definable M :=
  PA196PAMinusWitness.good_pa_of_induction good_induction

theorem axiom_branches :
    WB M PA196PAAxiomBound.actualPositive ∧ WB M (∼PA196PAAxiomBound.actualNegative) :=
  PA196PAAxiomAssembly.axiom_branches_of_induction good_induction

#print axioms wb_negative
#print axioms good_induction
#print axioms good_pa
#print axioms axiom_branches
end PA196InductionRecognizerComplete
