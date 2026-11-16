import PA196PATermBVGraph
import PA196PABvGraphBound
import PA196PAFormulaSetBound

/-! Unconditional witness bounds for the exact Foundation PA formula-set
conjunct in both derivation-core polarities. -/
set_option autoImplicit false
namespace PA196PAFormulaSetComplete
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAWitnessCalculus

variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem wb_bvGraph : WB M (bvGraph ℒₒᵣ).val :=
  PA196PABvGraphBound.wb_bvGraph PA196PATermBVGraph.wb_termBVVecGraph

theorem wb_actualSigmaLeft : WB M PA196PAFormulaSetBound.actualSigmaLeft :=
  PA196PAFormulaSetBound.wb_actualSigmaLeft wb_bvGraph

theorem wb_neg_actualPiLeft : WB M (∼PA196PAFormulaSetBound.actualPiLeft) :=
  PA196PAFormulaSetBound.wb_neg_actualPiLeft wb_bvGraph

#print axioms wb_bvGraph
#print axioms wb_actualSigmaLeft
#print axioms wb_neg_actualPiLeft
end PA196PAFormulaSetComplete
