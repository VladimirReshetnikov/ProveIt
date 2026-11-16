import PA196PASubstitutionWitnessDomination
import PA196PRAQVecTowerDomination

/-! Unconditional candidate-PRA witness bounds for arithmetic substitution. -/
set_option autoImplicit false
namespace PA196PASubstitutionWitnessComplete
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

theorem wb_fixpoint : WB M ((Substs.blueprint ℒₒᵣ).blueprint ℒₒᵣ).fixpointDef.val :=
  PA196PASubstitutionWitnessDomination.wb_fixpoint PA196PRAQVecTowerDomination.PRA_proves_tower_domination

theorem wb_substsGraph : WB M (substsGraph ℒₒᵣ).val :=
  PA196PASubstitutionWitnessDomination.wb_substsGraph PA196PRAQVecTowerDomination.PRA_proves_tower_domination

#print axioms wb_fixpoint
#print axioms wb_substsGraph
end PA196PASubstitutionWitnessComplete
