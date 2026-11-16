import PA196PASubstitutionWitnessConditional
import PA196PASubstitutionCoreComplete

/-! Exact arithmetic substitution witness bounds conditional only on the
candidate-PRA tower graph domination and tower-term monotonicity. -/
set_option autoImplicit false
namespace PA196PASubstitutionWitness
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAWitnessCalculus
  PRAWitnessTransfer PRAWitnessFormulaRec PA196PASubstitutionTowerGraph
  PA196PASubstitutionWitnessConditional

variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem wb_fixpoint
    (hdom : PRA ⊢ dominates towerGraph.val towerTerm)
    (hmono : Mono M (fun e : Fin 1 → M => towerTerm.val e Empty.elim)) :
    WB M ((Substs.blueprint ℒₒᵣ).blueprint ℒₒᵣ).fixpointDef.val := by
  exact wb_fixpoint_conditional PA196PASubstitutionCoreComplete.wb_core_sigma
    PA196PASubstitutionCoreComplete.wb_core_neg_pi hdom hmono

theorem wb_substsGraph
    (hdom : PRA ⊢ dominates towerGraph.val towerTerm)
    (hmono : Mono M (fun e : Fin 1 → M => towerTerm.val e Empty.elim)) :
    WB M (substsGraph ℒₒᵣ).val := by
  unfold substsGraph
  exact PA196PAFormulaRecBound.wb_result_of_fixpoint (wb_fixpoint hdom hmono)

#print axioms wb_fixpoint
#print axioms wb_substsGraph
end PA196PASubstitutionWitness
