import PA196PASubstitutionWitness
import PA196PRAQVecTowerMonotone

/-! Exact arithmetic substitution witness bounds conditional only on the
candidate-PRA tower graph-domination sentence. -/
set_option autoImplicit false
namespace PA196PASubstitutionWitnessDomination
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAWitnessCalculus
  PRAWitnessTransfer PA196PASubstitutionTowerGraph

variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem wb_fixpoint (hdom : PRA ⊢ dominates towerGraph.val towerTerm) :
    WB M ((Substs.blueprint ℒₒᵣ).blueprint ℒₒᵣ).fixpointDef.val :=
  PA196PASubstitutionWitness.wb_fixpoint hdom PA196PRAQVecTowerMonotone.towerTerm_mono

theorem wb_substsGraph (hdom : PRA ⊢ dominates towerGraph.val towerTerm) :
    WB M (substsGraph ℒₒᵣ).val :=
  PA196PASubstitutionWitness.wb_substsGraph hdom PA196PRAQVecTowerMonotone.towerTerm_mono

#print axioms wb_fixpoint
#print axioms wb_substsGraph
end PA196PASubstitutionWitnessDomination
