import PA194PAeqSubstWitnessConditional
import PA196PRAQVecTowerDomination
import PA196PRAQVecTowerMonotone
set_option autoImplicit false
namespace PA194PAeqSubstWitnessComplete
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

theorem wb_fixpoint : WB M ((Substs.blueprint PA194PAeq.language).blueprint PA194PAeq.language).fixpointDef.val := by
  apply PA194PAeqSubstWitnessConditional.wb_fixpoint_conditional
  · exact PA194PAeqSubstCore.wb_core_sigma
  · exact PA194PAeqSubstCore.wb_core_neg_pi_complete
  · exact PA196PRAQVecTowerDomination.PRA_proves_tower_domination
  · exact PA196PRAQVecTowerMonotone.towerTerm_mono

theorem wb_substsGraph : WB M (substsGraph PA194PAeq.language).val := by
  unfold substsGraph
  exact PA194PAeqFormulaRecWitness.wb_result_of_fixpoint wb_fixpoint

#print axioms wb_fixpoint
#print axioms wb_substsGraph
end PA194PAeqSubstWitnessComplete
