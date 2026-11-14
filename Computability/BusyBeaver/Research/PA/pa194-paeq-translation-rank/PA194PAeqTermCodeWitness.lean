import PA194PAeqTranslationClauses
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194PAeqTermCodeWitness
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAWitnessCalculus
open PA194PAeqTermBlueprint PA194PAeqTranslationClauses PA194PAeqTranslationRank
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem clauses : PA196PATermRecBound.ClauseBounds termBlueprint M := by
  obtain ⟨hb,hf,hg⟩ := positive_clauses (M := M)
  exact ⟨hb,hf,hg,bvar_negative,fvar_negative,func_negative⟩

noncomputable abbrev constructions : PA196PATermRecBound.Constructions termBlueprint :=
  fun _ _ _ => termConstruction

theorem wb_termCodeGraph : WB M termCodeGraph.val := by
  exact PA196PATermRecBound.wb_result constructions clauses (fun _ _ _ => termCode_rank)

theorem wb_termVectorGraph : WB M termVectorGraph.val := by
  exact PA196PATermRecBound.wb_resultVec constructions clauses (fun _ _ _ => termCode_rank)

#print axioms wb_termCodeGraph
#print axioms wb_termVectorGraph
end PA194PAeqTermCodeWitness
